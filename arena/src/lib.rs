#![feature(negative_impls)]

use core::marker::PhantomData;
use core::mem::{align_of, needs_drop, size_of};
use core::ptr::null_mut;
use core::slice::from_raw_parts_mut;
use core::sync::atomic::{AtomicUsize, Ordering};
use libc::{
    MAP_ANONYMOUS, MAP_FAILED, MAP_PRIVATE, PROT_NONE, PROT_READ, PROT_WRITE, mmap, mprotect,
    munmap,
};

struct ArenaInternal<'a> {
    orig_ptr: *mut u8,
    ptr: *mut u8,
    offset: AtomicUsize,
    max: usize,
    virt: bool,
    _phantom: PhantomData<&'a ()>,
}

pub struct Arena<'a> {
    arena: ArenaInternal<'a>,
}

pub struct BrandedArena<'a, T> {
    arena: ArenaInternal<'a>,
    _phantom: PhantomData<T>,
}

#[derive(Clone, Copy, Debug)]
pub struct BrandedArenaId<T> {
    id: u32,
    _phantom: PhantomData<T>,
}

impl<'a> ArenaInternal<'a> {
    fn new_backed<T, const B: usize>(backing: &'a mut [T; B], align: usize) -> ArenaInternal<'a> {
        const {
            assert!(!needs_drop::<T>());
        }
        let ptr = backing.as_mut_ptr() as *mut u8;
        let max = size_of::<[T; B]>();
        let align_offset = ptr.align_offset(align);
        assert!(align_offset <= max, "alignment too large for backed arena");
        ArenaInternal {
            orig_ptr: ptr,
            ptr: unsafe { ptr.add(align_offset) },
            offset: AtomicUsize::new(0),
            max,
            virt: false,
            _phantom: PhantomData,
        }
    }

    fn new_virt(align: usize) -> ArenaInternal<'a> {
        const MMAP_SIZE: usize = 1 << 40;
        let ptr = unsafe {
            mmap(
                null_mut(),
                MMAP_SIZE,
                PROT_NONE,
                MAP_ANONYMOUS | MAP_PRIVATE,
                -1,
                0,
            )
        };
        assert_ne!(ptr, MAP_FAILED, "mmap failed in arena");
        let align_offset = ptr.align_offset(align);
        assert!(
            align_offset <= MMAP_SIZE,
            "alignment too large for virtual arena"
        );
        ArenaInternal {
            orig_ptr: ptr as *mut u8,
            ptr: unsafe { (ptr as *mut u8).add(align_offset) },
            offset: AtomicUsize::new(0),
            max: MMAP_SIZE,
            virt: true,
            _phantom: PhantomData,
        }
    }

    fn realign(self: ArenaInternal<'a>, align: usize) -> ArenaInternal<'a> {
        let offset = self.offset.load(Ordering::Relaxed);
        let align_offset = unsafe { self.ptr.add(offset) }.align_offset(align);
        assert!(
            offset + align_offset <= self.max,
            "alignment too large to realign arena"
        );
        self.offset.store(offset + align_offset, Ordering::Relaxed);
        self
    }

    fn alloc<'b>(&'b self, size: usize, align: Option<usize>) -> usize {
        #[allow(unused_assignments)]
        let mut begin_offset = 0;
        let mut old_offset = self.offset.load(Ordering::Relaxed);
        if let Some(align) = align {
            loop {
                let align_offset = unsafe { self.ptr.add(old_offset) }.align_offset(align);
                begin_offset = old_offset + align_offset;
                assert!(begin_offset <= self.max, "ran out of space in arena");
                let end_offset = begin_offset + size;
                match self.offset.compare_exchange_weak(
                    old_offset,
                    end_offset,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => break,
                    Err(new_offset) => old_offset = new_offset,
                }
            }
        } else {
            old_offset = self.offset.fetch_add(size, Ordering::Relaxed);
            begin_offset = old_offset;
        }
        assert!(begin_offset + size <= self.max, "ran out of space in arena");

        if self.virt {
            unsafe {
                commit_sections(self.ptr, old_offset, begin_offset + size);
            }
        }

        begin_offset
    }
}

impl Drop for ArenaInternal<'_> {
    fn drop(&mut self) {
        if self.virt {
            let code = unsafe { munmap(self.orig_ptr as _, self.max) };
            assert_eq!(code, 0, "munmap failed in arena")
        }
    }
}

unsafe fn commit_sections(ptr: *mut u8, old_offset: usize, new_offset: usize) {
    const MCOMMIT_GRANULARITY: usize = 1 << 20;
    let prev_first_uncommited_section =
        (old_offset + MCOMMIT_GRANULARITY - 1) / MCOMMIT_GRANULARITY;
    let new_first_uncommited_section = (new_offset + MCOMMIT_GRANULARITY - 1) / MCOMMIT_GRANULARITY;
    let num_sections = new_first_uncommited_section - prev_first_uncommited_section;
    if num_sections != 0 {
        let code = unsafe {
            mprotect(
                ptr.add(prev_first_uncommited_section * MCOMMIT_GRANULARITY) as _,
                num_sections * MCOMMIT_GRANULARITY,
                PROT_READ | PROT_WRITE,
            )
        };
        assert_eq!(code, 0, "mprotect failed in arena");
    }
}

impl<'a> Arena<'a> {
    pub fn new_backed<T, const B: usize>(backing: &'a mut [T; B]) -> Arena<'a> {
        Arena {
            arena: ArenaInternal::new_backed(backing, 1),
        }
    }

    pub fn new_virt() -> Arena<'a> {
        Arena {
            arena: ArenaInternal::new_virt(1),
        }
    }

    pub fn brand<T>(self) -> BrandedArena<'a, T> {
        const {
            assert!(!needs_drop::<T>());
        }
        BrandedArena {
            arena: self.arena.realign(align_of::<T>()),
            _phantom: PhantomData,
        }
    }

    pub fn new<'b, T>(&'b self, x: T) -> &'b mut T {
        const {
            assert!(!needs_drop::<T>());
        }
        let offset = self.arena.alloc(size_of::<T>(), Some(align_of::<T>()));
        unsafe {
            let ptr = self.arena.ptr.add(offset) as *mut T;
            *ptr = x;
            &mut *ptr
        }
    }

    pub fn new_slice<'b, T: Clone>(&'b self, count: usize, x: T) -> &'b mut [T] {
        const {
            assert!(!needs_drop::<T>());
        }
        let offset = self
            .arena
            .alloc(count * size_of::<T>(), Some(align_of::<T>()));
        unsafe {
            let ptr = self.arena.ptr.add(offset) as *mut T;
            for i in 0..count {
                *ptr.add(i) = x.clone();
            }
            from_raw_parts_mut(ptr, count)
        }
    }
}

impl<'a, T> BrandedArena<'a, T> {
    pub fn new_backed<BT, const B: usize>(backing: &'a mut [BT; B]) -> BrandedArena<'a, T> {
        const {
            assert!(!needs_drop::<T>());
        }
        BrandedArena {
            arena: ArenaInternal::new_backed(backing, align_of::<T>()),
            _phantom: PhantomData,
        }
    }

    pub fn new_virt() -> BrandedArena<'a, T> {
        const {
            assert!(!needs_drop::<T>());
        }
        BrandedArena {
            arena: ArenaInternal::new_virt(align_of::<T>()),
            _phantom: PhantomData,
        }
    }

    pub fn rebrand<NewT>(self) -> BrandedArena<'a, NewT> {
        const {
            assert!(!needs_drop::<NewT>());
        }
        BrandedArena {
            arena: self.arena.realign(align_of::<NewT>()),
            _phantom: PhantomData,
        }
    }

    pub fn unbrand(self) -> Arena<'a> {
        Arena { arena: self.arena }
    }

    pub fn new<'b>(&'b self, x: T) -> BrandedArenaId<T> {
        let offset = self.arena.alloc(size_of::<T>(), None);
        unsafe {
            let ptr = self.arena.ptr.add(offset) as *mut T;
            *ptr = x;
        }
        BrandedArenaId {
            id: (offset / size_of::<T>()) as u32,
            _phantom: PhantomData,
        }
    }

    pub fn get<'b>(&'b self, id: BrandedArenaId<T>) -> &'b T {
        let offset = id.id as usize * size_of::<T>();
        assert!(offset + size_of::<T>() <= self.arena.max);
        unsafe { &*(self.arena.ptr.add(offset) as *mut T) }
    }

    pub fn get_mut<'b>(&'b mut self, id: BrandedArenaId<T>) -> &'b mut T {
        let offset = id.id as usize * size_of::<T>();
        assert!(offset + size_of::<T>() <= self.arena.max);
        unsafe { &mut *(self.arena.ptr.add(offset) as *mut T) }
    }
}

unsafe impl Sync for Arena<'_> {}
unsafe impl Send for Arena<'_> {}
unsafe impl<T> Sync for BrandedArena<'_, T> {}
unsafe impl<T> Send for BrandedArena<'_, T> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_backed_arena() {
        let mut buf1: [u8; 64] = [0; 64];
        let _arena1 = Arena::new_backed(&mut buf1);
        let mut buf2: [u8; 40] = [0; 40];
        let _arena2 = Arena::new_backed(&mut buf2);
    }

    #[test]
    fn create_virt_arena() {
        let _arena1 = Arena::new_virt();
        let _arena2 = Arena::new_virt();
    }

    #[test]
    fn alloc_backed_arena() {
        let mut buf: [u64; 5] = [0; 5];
        let arena = Arena::new_backed(&mut buf);
        arena.new::<i8>(0);
        assert_eq!(arena.arena.offset.load(Ordering::Relaxed), 1);
        arena.new::<i8>(0);
        assert_eq!(arena.arena.offset.load(Ordering::Relaxed), 2);
        arena.new::<i16>(0);
        assert_eq!(arena.arena.offset.load(Ordering::Relaxed), 4);
        arena.new::<i8>(0);
        assert_eq!(arena.arena.offset.load(Ordering::Relaxed), 5);
        arena.new::<i16>(0);
        assert_eq!(arena.arena.offset.load(Ordering::Relaxed), 8);
        arena.new::<i64>(0);
        assert_eq!(arena.arena.offset.load(Ordering::Relaxed), 16);
        arena.new::<i64>(0);
        assert_eq!(arena.arena.offset.load(Ordering::Relaxed), 24);
        arena.new::<i64>(0);
        assert_eq!(arena.arena.offset.load(Ordering::Relaxed), 32);
        arena.new::<i16>(0);
        assert_eq!(arena.arena.offset.load(Ordering::Relaxed), 34);
        arena.new::<i16>(0);
        assert_eq!(arena.arena.offset.load(Ordering::Relaxed), 36);
        arena.new::<i32>(0);
        assert_eq!(arena.arena.offset.load(Ordering::Relaxed), 40);
        arena.new::<()>(());
        assert_eq!(arena.arena.offset.load(Ordering::Relaxed), 40);
    }

    #[test]
    fn alloc_virt_arena() {
        #[derive(Default, Clone)]
        struct LargeType {
            _a: i128,
            _b: u128,
            _c: f64,
            _d: u128,
            _e: u128,
            _f: u128,
            _g: u128,
            _h: i8,
        }
        let arena = Arena::new_virt();
        for _ in 0..(1 << 18) {
            arena.new_slice::<LargeType>(10, LargeType::default());
        }
    }

    #[test]
    fn alloc_virt_arena_multiple() {
        let arena1 = Arena::new_virt();
        let arena2 = Arena::new_virt();
        for _ in 0..(1 << 18) {
            arena1.new_slice::<f32>(20, 0.0);
        }
        for _ in 0..(1 << 18) {
            arena2.new_slice::<f32>(8, 0.0);
        }
    }

    #[test]
    fn modify_backed_arena() {
        let mut buf: [u64; 1] = [0; 1];
        let arena = Arena::new_backed(&mut buf);
        let x = arena.new::<i32>(0);
        assert_eq!(*x, 0);
        let y = arena.new::<i32>(0);
        assert_eq!(*y, 0);
        *x = 42;
        *y = 24;
        assert_eq!(*x, 42);
        assert_eq!(*y, 24);
    }

    #[test]
    fn modify_virt_arena() {
        let arena = Arena::new_virt();
        let mut refs = vec![];
        for i in 0..(1 << 20) {
            let r = arena.new::<i32>(0);
            *r = i;
            refs.push(r);
        }
        for i in 0i32..(1 << 20) {
            assert_eq!(*refs[i as usize], i);
        }
    }

    #[test]
    fn branded_backed_arena() {
        let mut buf: [u64; 1] = [0; 1];
        let mut arena = BrandedArena::<i16>::new_backed(&mut buf);
        let x = arena.new(42);
        let y = arena.new(43);
        let z = arena.new(44);
        let w = arena.new(45);
        assert_eq!(*arena.get(x), 42);
        assert_eq!(*arena.get(y), 43);
        assert_eq!(*arena.get(z), 44);
        assert_eq!(*arena.get(w), 45);
        *arena.get_mut(y) = -42;
        *arena.get_mut(z) = -43;
        assert_eq!(*arena.get(x), 42);
        assert_eq!(*arena.get(y), -42);
        assert_eq!(*arena.get(z), -43);
        assert_eq!(*arena.get(w), 45);
    }

    #[test]
    fn branded_virt_arena() {
        let mut arena = BrandedArena::<i128>::new_virt();
        let mut ids = vec![];
        for _ in 0..(1 << 20) {
            ids.push(arena.new(42));
        }
        for i in 0..(1 << 20) {
            assert_eq!(*arena.get(ids[i]), 42);
        }
        for i in 0..(1 << 20) {
            *arena.get_mut(ids[i]) = i as i128;
        }
        for i in 0..(1 << 20) {
            assert_eq!(*arena.get(ids[i]), i as i128);
        }
    }

    #[test]
    fn mixed_backed_arena() {
        let mut buf: [u64; 1] = [0; 1];
        let arena = Arena::new_backed(&mut buf);
        arena.new::<i8>(0);
        let arena = arena.brand::<i16>();
        arena.new(0);
        let arena = arena.rebrand::<i8>();
        arena.new(0);
        let arena = arena.unbrand();
        arena.new::<i8>(0);
        arena.new::<i8>(0);
        arena.new::<i8>(0);
    }
}
