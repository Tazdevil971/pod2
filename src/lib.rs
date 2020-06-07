pub use pod2_macro::Pod;

use std::slice;
use std::mem::{self, size_of};
use std::fmt::{self, Debug};
use std::io::{self, Write, Read};

/// Extension for reading Pod types.
pub trait ReadPod: Read {
    /// Read a single pod from a Read stream.
    fn read_pod<T: Pod>(&mut self) -> io::Result<T> {
        // TODO: replace this when 
        // maybe_uninit_ref gets stabilized
        let mut pod = T::zeroed();
        self.read_exact(<[u8]>::from_ref_mut(&mut pod).unwrap())?;
        Ok(pod)
    }

    /// Read a slice of pods from a Read stream.
    /// Uses a single read_exact call.
    fn read_pod_slice<T: Pod>(&mut self, len: usize) -> io::Result<Vec<T>> {
        let mut pod: Vec<T> = (0..len).map(|_| T::zeroed()).collect();
        self.read_exact(<[u8]>::from_slice_mut(&mut pod).unwrap())?;
        Ok(pod)
    }
}

/// Extension for writing Pod types.
pub trait WritePod: Write {
    /// Write a single pod from a Write stream.
    fn write_pod<T: Pod>(&mut self, pod: &T) -> io::Result<()> {
        self.write_all(<[u8]>::from_ref(pod).unwrap())
    }

    /// Write a slice of pods to a Write stream.
    /// Uses a single write_all call.
    fn write_pod_slice<T: Pod>(&mut self, pod: &[T]) -> io::Result<()> {
        self.write_all(<[u8]>::from_slice(pod).unwrap())
    }
}

impl<T: Read> ReadPod for T {}
impl<T: Write> WritePod for T {}

/// Trait marking Plain Old Data types.
/// # Safety
/// Implementing this trait is not safe because it internally
/// uses a lot of `unsafe` on the assumption that the underlying
/// data is plain, and reinterpretation of the data is safe.
/// Use the derive macro in order to automatically check the data,
/// and avoid unsafe code.
pub unsafe trait Pod: Sized {
    /// Creates a new, zero initialized, pod.
    #[inline]
    fn zeroed() -> Self {
        unsafe { mem::zeroed() }
    }
}

// Zero sized struct
unsafe impl<T> Pod for std::marker::PhantomData<T> {}

macro_rules! impl_pod {
    ($($t:ty)*) => { $( 
        unsafe impl Pod for $t {} 
    )* };
    ($($e:expr)*) => { $( 
        unsafe impl<T: Pod> Pod for [T; $e] {} 
    )* };
}

impl_pod!(
    () f32 f64
    u8 u16 u32 u64 usize
    i8 i16 i32 i64 isize
);

impl_pod!(
     0  1  2  3  4  5  6  7  8  9
    10 11 12 13 14 15 16 17 18 19
    20 21 22 23 24 25 26 27 28 29
    30 31 32 33 34 35 36 37 38 39
    40 41 42 43 44 45 46 47 48 49
    50 51 52 53 54 55 56 57 58 59
    60 61 62 63 64 65 66 67 68 69
    70 71 72 73 74 75 76 77 78 79
    80 81 82 83 84 85 86 87 88 89
    90 91 92 93 94 95 96 97 98 99
    100 128 256 512 1024 2048 4096
);

/// Trait marking an object that can be constructed from a pod
pub trait FromPod {
    /// Create a Self reference from a Pod reference.
    fn from_ref<U: Pod>(other: &U) -> Option<&Self>;
    /// Create a Self reference from a Pod slice.
    fn from_slice<U: Pod>(other: &[U]) -> Option<&Self>;
    /// Create a Self reference from a Pod reference.
    fn from_ref_mut<U: Pod>(other: &mut U) -> Option<&mut Self>;
    /// Create a Self reference from a Pod slice.
    fn from_slice_mut<U: Pod>(other: &mut [U]) -> Option<&mut Self>;
}

impl<T: Pod> FromPod for T {
    fn from_ref<U: Pod>(other: &U) -> Option<&T> {
        if size_of::<T>() == size_of::<U>() {
            Some(unsafe {
                (other as *const U as *const T).as_ref().unwrap()
            })
        } else {
            None
        }
    }

    fn from_slice<U: Pod>(other: &[U]) -> Option<&T> {
        if size_of::<T>() == size_of::<U>() * other.len() {
            Some(unsafe {
                (other.as_ptr() as *const T).as_ref().unwrap()
            })
        } else {
            None
        }
    }

    fn from_ref_mut<U: Pod>(other: &mut U) -> Option<&mut T> {
        if size_of::<T>() == size_of::<U>() {
            Some(unsafe {
                &mut *(other as *mut U as *mut T)
            })
        } else {
            None
        }
    }

    fn from_slice_mut<U: Pod>(other: &mut [U]) -> Option<&mut T> {
        if size_of::<T>() == size_of::<U>() * other.len() {
            Some(unsafe {
                &mut *(other.as_mut_ptr() as *mut T)
            })
        } else {
            None
        }
    }
}

impl<T: Pod> FromPod for [T] {
    fn from_ref<U: Pod>(other: &U) -> Option<&[T]> {
        if size_of::<U>() % size_of::<T>() == 0 {
            Some(unsafe {
                slice::from_raw_parts(
                    other as *const U as *mut T, 
                    size_of::<U>() / size_of::<T>()
                )
            })
        } else {
            None
        }
    }

    fn from_slice<U: Pod>(other: &[U]) -> Option<&[T]> {
        if (size_of::<U>() * other.len()) % size_of::<T>() == 0 {
            Some(unsafe {
                slice::from_raw_parts(
                    other.as_ptr() as *mut T, 
                    (size_of::<U>() * other.len()) / size_of::<T>()
                )
            })
        } else {
            None
        }
    }

    fn from_ref_mut<U: Pod>(other: &mut U) -> Option<&mut [T]> {
        if size_of::<U>() % size_of::<T>() == 0 {
            Some(unsafe {
                slice::from_raw_parts_mut(
                    other as *mut U as *mut T, 
                    size_of::<U>() / size_of::<T>()
                )
            })
        } else {
            None
        }
    }

    fn from_slice_mut<U: Pod>(other: &mut [U]) -> Option<&mut [T]> {
        if (size_of::<U>() * other.len()) % size_of::<T>() == 0 {
            Some(unsafe {
                slice::from_raw_parts_mut(
                    other.as_mut_ptr() as *mut T, 
                    (size_of::<U>() * other.len()) / size_of::<T>()
                )
            })
        } else {
            None
        }
    }
}

#[doc(hidden)]
pub trait Endian {
    fn be_to_ne(self) -> Self;
    fn ne_to_be(self) -> Self;

    fn le_to_ne(self) -> Self;
    fn ne_to_le(self) -> Self;
}

macro_rules! impl_endian {
    ($($t:ty)*) => { $(
        impl Endian for $t {
            fn be_to_ne(self) -> Self { <$t>::from_be(self) }
            fn ne_to_be(self) -> Self { <$t>::to_be(self) }

            fn le_to_ne(self) -> Self { <$t>::from_le(self) }
            fn ne_to_le(self) -> Self { <$t>::to_le(self) }
        }
    )* };
}

impl_endian! {
    u8 u16 u32 u64 usize
    i8 i16 i32 i64 isize
}

/// Wrapper type holding the data in big endian order.
#[repr(transparent)]
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct Be<T>(T);

impl<T: Endian + Copy> Be<T> {
    /// Convert into big endian.
    pub fn from(other: T) -> Self {
        Self(T::ne_to_be(other))
    }

    /// Convert back into native endian.
    pub fn into(&self) -> T {
        T::be_to_ne(self.0)
    }
}

impl<T: Endian + Copy + Debug> Debug for Be<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Be({:?})", self.into())
    }
}

/// Wrapper type holding the data in little endian order.
#[repr(transparent)]
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct Le<T>(T);

impl<T: Endian + Copy> Le<T> {
    /// Convert into little endian.
    pub fn from(other: T) -> Self {
        Self(T::ne_to_le(other))
    }

    /// Convert back into native endian.
    pub fn into(&self) -> T {
        T::le_to_ne(self.0)
    }
}

impl<T: Endian + Copy + Debug> Debug for Le<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Le({:?})", self.into())
    }
}

unsafe impl<T: Pod> Pod for Be<T> {}
unsafe impl<T: Pod> Pod for Le<T> {}