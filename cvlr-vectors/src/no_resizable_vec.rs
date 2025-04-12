extern crate alloc;
use alloc::alloc::{alloc, dealloc, Layout};
use core::mem;
use core::ptr::NonNull;
use cvlr_asserts::cvlr_assert;
use std::io::{Read, Result, Write};
use std::{
    ops::{Deref, DerefMut, Index, IndexMut},
    ptr,
};

/////////////////////////
/// Raw Vec
/////////////////////////
struct RawVec<T> {
    ptr: NonNull<T>,
    cap: usize,
}

impl<T> RawVec<T> {
    fn new_zero_sized() -> Self {
        Self {
            ptr: NonNull::dangling(),
            cap: 0,
        }
    }

    fn new(capacity: usize) -> Self {
        // ZSTs have no memory allocation
        if mem::size_of::<T>() == 0 || capacity == 0 {
            return RawVec::new_zero_sized();
        }

        let layout: Layout =
            Layout::array::<T>(capacity).unwrap_or_else(|_| panic!("capacity overflow"));
        let ptr: NonNull<T> = unsafe {
            let ptr: *mut u8 = alloc(layout);
            NonNull::new_unchecked(ptr as *mut T)
        };

        Self { ptr, cap: capacity }
    }
}

impl<T> Drop for RawVec<T> {
    fn drop(&mut self) {
        // ZSTs have no memory allocation
        if mem::size_of::<T>() == 0 {
            return;
        }

        let layout: Layout = Layout::array::<T>(self.cap).unwrap();
        unsafe {
            dealloc(self.ptr.as_ptr() as *mut u8, layout);
        }
    }
}

/////////////////////////
/// NoResizableVec
/////////////////////////
pub struct NoResizableVec<T> {
    buf: RawVec<T>,
    len: usize,
}

impl<T> NoResizableVec<T> {
    pub fn new(capacity: usize) -> Self {
        Self {
            buf: RawVec::new(capacity),
            len: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn capacity(&self) -> usize {
        self.buf.cap
    }

    pub fn push(&mut self, value: T) {
        cvlr_assert!(self.buf.cap > self.len);
        unsafe {
            let end: *mut T = self.buf.ptr.as_ptr().add(self.len);
            end.write(value);
        }
        self.len += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            unsafe {
                let end: *mut T = self.buf.ptr.as_ptr().add(self.len);
                Some(end.read())
            }
        }
    }

    pub fn insert(&mut self, index: usize, value: T) {
        cvlr_assert!(self.buf.cap > self.len);
        cvlr_assert!(index <= self.len);
        unsafe {
            let ptr: *mut T = self.buf.ptr.as_ptr().add(index);
            ptr.copy_to(ptr.add(1), self.len - index);
            ptr.write(value);
        }
        self.len += 1;
    }

    pub fn remove(&mut self, index: usize) -> T {
        cvlr_assert!(index < self.len);
        unsafe {
            self.len -= 1;
            let ptr: *mut T = self.buf.ptr.as_ptr().add(index);
            let value: T = ptr.read();
            ptr.add(1).copy_to(ptr, self.len - index);
            value
        }
    }

    pub fn find(&self, value: &T) -> Option<usize>
    where
        T: Ord,
    {
        for i in 0..self.len {
            unsafe {
                let ptr: *mut T = self.buf.ptr.as_ptr().add(i);
                if ptr.read() == *value {
                    return Some(i);
                }
            }
        }
        None
    }
}

impl<T> Drop for NoResizableVec<T> {
    fn drop(&mut self) {
        // do nothiing
    }
}

//////////////////
/// Other traits:
/// - Clone
/// - Deref
/// - DerefMut
/// - Index
/// - IndexMut
/// - BosrhSerialize
/// - BorshDeserialize
//////////////////
impl<T> Clone for NoResizableVec<T> {
    fn clone(&self) -> Self {
        let raw_vec = RawVec::new(self.capacity());
        let new_vec = Self {
            buf: raw_vec,
            len: self.len(),
        };

        unsafe {
            ptr::copy_nonoverlapping(self.buf.ptr.as_ptr(), new_vec.buf.ptr.as_ptr(), self.len());
        }

        new_vec
    }
}

impl<T> Deref for NoResizableVec<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.buf.ptr.as_ptr(), self.len()) }
    }
}

impl<T> DerefMut for NoResizableVec<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.buf.ptr.as_ptr(), self.len()) }
    }
}

impl<T> Index<usize> for NoResizableVec<T> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        cvlr_assert!(index < self.len());
        unsafe {
            if mem::size_of::<T>() == 0 {
                NonNull::<T>::dangling().as_ref()
            } else {
                &*self.buf.ptr.as_ptr().add(index)
            }
        }
    }
}

impl<T> IndexMut<usize> for NoResizableVec<T> {
    fn index_mut(&mut self, index: usize) -> &mut T {
        cvlr_assert!(index < self.len());
        unsafe {
            if mem::size_of::<T>() == 0 {
                NonNull::<T>::dangling().as_mut()
            } else {
                &mut *self.buf.ptr.as_ptr().add(index)
            }
        }
    }
}

pub mod borsh0_9 {
    use super::*;

    impl<T> ::borsh0_9::BorshSerialize for NoResizableVec<T> {
        // Not implemented
        fn serialize<W: Write>(&self, _writer: &mut W) -> Result<()> {
            cvlr_assert!(false);
            unreachable!();
        }
    }

    impl<T> ::borsh0_9::BorshDeserialize for NoResizableVec<T> {
        // Not implemented
        fn deserialize(_buf: &mut &[u8]) -> Result<Self> {
            cvlr_assert!(false);
            unreachable!();
        }
    }
}

pub mod borsh0_10 {
    use super::*;

    impl<T> ::borsh0_10::BorshSerialize for NoResizableVec<T> {
        // Not implemented
        fn serialize<W: Write>(&self, _writer: &mut W) -> Result<()> {
            cvlr_assert!(false);
            unreachable!();
        }
    }

    impl<T> ::borsh0_10::BorshDeserialize for NoResizableVec<T> {
        // Not implemented
        fn deserialize(_buf: &mut &[u8]) -> Result<Self> {
            cvlr_assert!(false);
            unreachable!();
        }

        // Not implemented
        fn deserialize_reader<R: Read>(_reader: &mut R) -> Result<Self> {
            cvlr_assert!(false);
            unreachable!();
        }
    }
}

/////////////////////////
/// Iterator
/////////////////////////
pub struct IntoIter<T> {
    _buf: RawVec<T>,
    start: *const T,
    end: *const T,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.start == self.end {
            None
        } else {
            unsafe {
                if mem::size_of::<T>() != 0 {
                    let old: *const T = self.start;
                    self.start = self.start.offset(1);
                    Some(ptr::read(old))
                } else {
                    self.start = (self.start as usize + mem::align_of::<T>()) as *const _;
                    Some(ptr::read(NonNull::<T>::dangling().as_ptr()))
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let elem_size = mem::size_of::<T>();
        let exact = (self.end as usize - self.start as usize)
            / if elem_size == 0 {
                mem::align_of::<T>()
            } else {
                elem_size
            };
        (exact, Some(exact))
    }
}

impl<T> Drop for IntoIter<T> {
    fn drop(&mut self) {
        for _ in &mut *self {}
    }
}

impl<T> IntoIterator for NoResizableVec<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        unsafe {
            let buf = ptr::read(&self.buf);
            let len = self.len();
            mem::forget(self);

            IntoIter {
                start: buf.ptr.as_ptr(),
                end: if mem::size_of::<T>() == 0 {
                    (buf.ptr.as_ptr() as usize + len * mem::align_of::<T>()) as *const _
                } else if len == 0 {
                    buf.ptr.as_ptr()
                } else {
                    buf.ptr.as_ptr().add(len)
                },
                _buf: buf,
            }
        }
    }
}

////////////////////
// Macros
////////////////////

#[macro_export]
macro_rules! cvt_no_resizable_vec {
    ($(values:expr),+ $(,)?) => (
        {
            let ARG_COUNT: usize = 0 $(+ { _ = $values; 1 })*;
            let mut v = $crate::no_resizable_vec::NoResizableVec::new(ARG_COUNT*2);
            $(v.push($values);)*
            v
        }
    );

    ([$($values:expr),* $(,)?]; $cap:expr) => {
        {
            let ARG_COUNT: usize = 0 $(+ { _ = $values; 1 })*;
            cvlr::asserts::cvlr_assert!(ARG_COUNT <= $cap);
            let mut v = $crate::no_resizable_vec::NoResizableVec::new($cap);
            $(v.push($values);)*
            v
        }
    };
}

pub use cvt_no_resizable_vec;

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_push_and_pop() {
        let mut vec = NoResizableVec::new(3);
        vec.push(1);
        vec.push(2);
        vec.push(3);

        assert_eq!(vec.len(), 3);
        assert_eq!(vec.pop(), Some(3));
        assert_eq!(vec.pop(), Some(2));
        assert_eq!(vec.pop(), Some(1));
        assert_eq!(vec.pop(), None);
    }

    #[test]
    fn test_insert_and_remove() {
        let mut vec = NoResizableVec::new(3);
        vec.push(1);
        vec.push(3);
        vec.insert(1, 2);

        assert_eq!(vec.len(), 3);
        assert_eq!(vec[0], 1);
        assert_eq!(vec[1], 2);
        assert_eq!(vec[2], 3);

        assert_eq!(vec.remove(1), 2);
        assert_eq!(vec.len(), 2);
        assert_eq!(vec[0], 1);
        assert_eq!(vec[1], 3);
    }

    #[test]
    fn test_find() {
        let mut vec = NoResizableVec::new(3);
        vec.push(10);
        vec.push(20);
        vec.push(30);

        assert_eq!(vec.find(&20), Some(1));
        assert_eq!(vec.find(&40), None);
    }

    #[test]
    fn test_clone() {
        let mut vec = NoResizableVec::new(3);
        vec.push(1);
        vec.push(2);
        vec.push(3);

        let cloned_vec = vec.clone();
        assert_eq!(cloned_vec.len(), 3);
        assert_eq!(cloned_vec[0], 1);
        assert_eq!(cloned_vec[1], 2);
        assert_eq!(cloned_vec[2], 3);
    }

    #[test]
    fn test_into_iter() {
        let mut vec = NoResizableVec::new(3);
        vec.push(1);
        vec.push(2);
        vec.push(3);

        let mut iter = vec.into_iter();
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_bin_search1() {
        let mut vec: NoResizableVec<u64> = NoResizableVec::new(3);

        vec.push(5);
        vec.push(15);
        vec.push(25);

        {
            let v: u64 = 5;
            let found = vec.binary_search(&v);
            assert!(found.is_ok());
        }
        {
            let v: u64 = 15;
            let found = vec.binary_search(&v);
            assert!(found.is_ok());
        }
        {
            let v: u64 = 25;
            let found = vec.binary_search(&v);
            assert!(found.is_ok());
        }
        {
            let v: u64 = 35;
            let found = vec.binary_search(&v);
            assert!(found.is_err());
        }
    }

    #[test]
    fn test_bin_search2() {
        let mut vec: NoResizableVec<u64> = NoResizableVec::new(3);
        vec.push(4);
        vec.push(7);
        vec.push(9);

        {
            let v: u64 = 5;
            let found = vec.binary_search(&v);
            assert!(found.is_err());
        }
        {
            let v: u64 = 9;
            let found = vec.binary_search(&v);
            assert!(found.is_ok());
        }
        {
            let v: u64 = 4;
            let found = vec.binary_search(&v);
            assert!(found.is_ok());
        }
        {
            let v: u64 = 35;
            let found = vec.binary_search(&v);
            assert!(found.is_err());
        }
    }

    #[test]
    pub fn test_bin_search3() {
        let mut vec: NoResizableVec<u64> = NoResizableVec::new(3);

        let v1: u64 = 5;
        let v2: u64 = 15;
        let v3: u64 = 25;
        match vec.binary_search(&v1) {
            Ok(_) => {
                assert!(false);
            }
            Err(pos) => vec.insert(pos, v1),
        }

        match vec.binary_search(&v2) {
            Ok(_) => {
                assert!(false);
            }
            Err(pos) => vec.insert(pos, v2),
        }

        match vec.binary_search(&v3) {
            Ok(_) => {
                assert!(false);
            }
            Err(pos) => vec.insert(pos, v3),
        }

        assert_eq!(vec.len(), 3);
        assert!(vec.binary_search(&v1).is_ok());
        assert!(vec.binary_search(&v2).is_ok());
        assert!(vec.binary_search(&v3).is_ok());
    }

    #[test]
    fn test_bin_search4() {
        let mut vec1: NoResizableVec<u64> = NoResizableVec::new(3);
        let mut vec2: NoResizableVec<u64> = NoResizableVec::new(3);

        let v1: u64 = 5;
        let v2: u64 = 15;
        let v3: u64 = 25;
        match vec1.binary_search(&v1) {
            Ok(_) => {
                assert!(false);
            }
            Err(pos) => vec1.insert(pos, v1),
        }

        match vec1.binary_search(&v2) {
            Ok(_) => {
                assert!(false);
            }
            Err(pos) => vec1.insert(pos, v2),
        }

        match vec1.binary_search(&v3) {
            Ok(_) => {
                assert!(false);
            }
            Err(pos) => vec1.insert(pos, v3),
        }

        /////

        match vec2.binary_search(&v1) {
            Ok(_) => {
                assert!(false);
            }
            Err(pos) => vec2.insert(pos, v1),
        }

        match vec2.binary_search(&v2) {
            Ok(_) => {
                assert!(false);
            }
            Err(pos) => vec2.insert(pos, v2),
        }

        assert!(vec1.binary_search(&v3).is_ok());
        assert!(vec2.binary_search(&v3).is_err());
    }
}
