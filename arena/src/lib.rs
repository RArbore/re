#![feature(clone_to_uninit, negative_impls, ptr_metadata)]

use core::clone::CloneToUninit;
use core::marker::PhantomData;
use core::mem::{align_of, align_of_val, needs_drop, size_of, size_of_val};
use core::ptr;
use core::ptr::{metadata, null_mut};
use core::slice;
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

    fn realign<'b>(&'b self, align: usize) {
        if align > 1 {
            #[allow(unused_assignments)]
            let mut aligned_offset = 0;
            let mut old_offset = self.offset.load(Ordering::Relaxed);
            loop {
                aligned_offset =
                    old_offset + unsafe { self.ptr.add(old_offset) }.align_offset(align);
                assert!(aligned_offset <= self.max, "ran out of space in arena");
                match self.offset.compare_exchange_weak(
                    old_offset,
                    aligned_offset,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => break,
                    Err(new_offset) => old_offset = new_offset,
                }
            }
        }
    }

    fn alloc<'b>(&'b self, size: usize, align: Option<usize>) -> usize {
        #[allow(unused_assignments)]
        let mut begin_offset = 0;
        let mut old_offset = self.offset.load(Ordering::Relaxed);
        if let Some(align) = align
            && align > 1
        {
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
            slice::from_raw_parts_mut(ptr, count)
        }
    }

    pub fn new_ref<'b, T: CloneToUninit + ?Sized>(&'b self, x: &T) -> &'b mut T {
        let size = size_of_val(x);
        let align = align_of_val(x);
        let offset = self.arena.alloc(size, Some(align));
        unsafe {
            let ptr = self.arena.ptr.add(offset);
            x.clone_to_uninit(ptr);
            &mut *ptr::from_raw_parts_mut(ptr, metadata(x))
        }
    }

    pub fn alloc<'b, T>(&'b self, x: T) -> BrandedArenaId<T> {
        let offset = self.arena.alloc(size_of::<T>(), Some(align_of::<T>()));
        unsafe {
            let ptr = self.arena.ptr.add(offset) as *mut T;
            *ptr = x;
        }
        BrandedArenaId {
            id: (offset / size_of::<T>()) as u32,
            _phantom: PhantomData,
        }
    }

    pub fn collect<'b, T, I>(&'b mut self, iter: I) -> &'b mut [T]
    where
        I: Iterator<Item = T>,
    {
        self.arena.realign(align_of::<T>());
        let old_offset = self.arena.offset.load(Ordering::Relaxed);
        let mut count = 0;
        let ptr = unsafe { self.arena.ptr.add(old_offset) } as *mut T;
        for x in iter {
            self.arena.alloc(size_of::<T>(), None);
            unsafe { *ptr.add(count) = x };
            count += 1;
        }
        unsafe { slice::from_raw_parts_mut(ptr, count) }
    }

    pub fn collect_fn<'b, T, F>(&'b mut self, mut f: F) -> &'b mut [T]
    where
        F: FnMut(&mut dyn FnMut(T) -> BrandedArenaId<T>),
    {
        self.arena.realign(align_of::<T>());
        let old_offset = self.arena.offset.load(Ordering::Relaxed);
        let ptr = unsafe { self.arena.ptr.add(old_offset) } as *mut T;
        let mut count = 0;
        let mut pf = |x| {
            self.arena.alloc(size_of::<T>(), None);
            unsafe { *ptr.add(count) = x };
            let id = (old_offset / size_of::<T>() + count) as u32;
            count += 1;
            BrandedArenaId {
                id,
                _phantom: PhantomData,
            }
        };
        f(&mut pf);
        unsafe { slice::from_raw_parts_mut(ptr, count) }
    }

    pub fn get<'b, T>(&'b self, id: BrandedArenaId<T>) -> &'b T {
        let offset = id.id as usize * size_of::<T>();
        assert!(offset + size_of::<T>() <= self.arena.max);
        unsafe { &*(self.arena.ptr.add(offset) as *mut T) }
    }

    pub fn get_mut<'b, T>(&'b mut self, id: BrandedArenaId<T>) -> &'b mut T {
        let offset = id.id as usize * size_of::<T>();
        assert!(offset + size_of::<T>() <= self.arena.max);
        unsafe { &mut *(self.arena.ptr.add(offset) as *mut T) }
    }
}

unsafe impl Sync for Arena<'_> {}
unsafe impl Send for Arena<'_> {}

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
        let mut arena = Arena::new_backed(&mut buf);
        let x = arena.alloc::<i16>(42);
        let y = arena.alloc::<i16>(43);
        let z = arena.alloc::<i16>(44);
        let w = arena.alloc::<i16>(45);
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
        let mut arena = Arena::new_virt();
        let mut ids = vec![];
        for _ in 0..(1 << 20) {
            ids.push(arena.alloc::<i128>(42));
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
        arena.alloc::<i16>(0);
        arena.alloc::<i8>(0);
        arena.new::<i8>(0);
        arena.new::<i8>(0);
        arena.new::<i8>(0);
    }

    #[test]
    fn collect_backed_arena() {
        let mut buf: [u64; 32] = [0; 32];
        let mut arena = Arena::new_backed(&mut buf);
        let slice = arena.collect(0..128u8);
        for i in 0..128u8 {
            assert_eq!(slice[i as usize], i);
        }
        let slice = arena.collect_fn(|alloc_fn| {
            for count in 5..133u8 {
                alloc_fn(count);
            }
        });
        for i in 0..128u8 {
            assert_eq!(slice[i as usize], i + 5);
        }
    }
}
