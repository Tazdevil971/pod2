//! Pod2 is a library enabling the usage of [Pod](https://en.wikipedia.org/wiki/Passive_data_structure) data types in rust.

/// Macro for automatically deriving Pod.
pub use pod2_macro::Pod;

use std::slice;
use std::mem::{self, size_of};
use std::fmt::{self, Debug};
use std::io::{self, Write, Read};

/// Extension for taking Pod types.
/// It's used to parse byte slices with
/// zero copies.
/// # Example
/// ```
/// # use pod2::*;
/// # fn main() {
/// // Example of a buffer containing data
/// let mut buf: &[u8] = &[
///     0x00, 0x01, 
///     0x00, 0x02,
///     0xcc, 0xdd, 0xee,
///     0xff, 0xff
/// ]; 
/// 
/// let a: &Be<u16> = buf.take_pod().unwrap();
/// assert_eq!(a.get(), 1);
/// 
/// let b: &Be<u16> = buf.take_pod().unwrap();
/// assert_eq!(b.get(), 2);
/// 
/// let c: &[u8] = buf.take_pod_slice(3).unwrap();
/// assert_eq!(c, &[ 0xcc, 0xdd, 0xee ]);
/// 
/// // Check what is left in the slice
/// assert_eq!(buf, &[ 0xff, 0xff ]);
/// # }
/// ```
pub trait TakePod<'a> {
    /// Take a single pod from a byte slice.
    fn take_pod<T: Pod>(&mut self) -> Option<&'a T>;
    /// Take a slice of pods from a byte slice.
    fn take_pod_slice<T: Pod>(&mut self, len: usize) -> Option<&'a [T]>;
}

impl<'a> TakePod<'a> for &'a [u8] {
    fn take_pod<T: Pod>(&mut self) -> Option<&'a T> {
        let pod = self.get(..size_of::<T>())?;
        *self = self.get(size_of::<T>()..)?;
        pod.into_ref()
    }

    fn take_pod_slice<T: Pod>(&mut self, len: usize) -> Option<&'a [T]> {
        let pod = self.get(..size_of::<T>() * len)?;
        *self = self.get(size_of::<T>() * len..)?;
        pod.into_slice()
    }
}

/// Extension for reading Pod types.
/// This differs from `TakePod` as read data
/// is then owned, and it works on any `Read`.
/// # Example
/// ```
/// # use pod2::*;
/// # fn main() {
/// // Some readable source
/// let mut reader: &[u8] = &[
///     0x00, 0x01, 
///     0x00, 0x02,
///     0xcc, 0xdd, 0xee
/// ];
/// 
/// let a: Be<u16> = reader.read_pod().unwrap();
/// assert_eq!(a.get(), 1);
/// 
/// let b: Be<u16> = reader.read_pod().unwrap();
/// assert_eq!(b.get(), 2);
/// 
/// // This is very efficent as it 
/// // uses a single read_exact call
/// let c: Vec<u8> = reader.read_pod_slice(3).unwrap();
/// assert_eq!(c, &[ 0xcc, 0xdd, 0xee ]);
/// # }
/// ```
pub trait ReadPod: Read {
    /// Read a single pod from a Read stream.
    fn read_pod<T: Pod>(&mut self) -> io::Result<T> {
        // TODO: replace this when 
        // maybe_uninit_ref gets stabilized
        let mut pod = T::zeroed();
        self.read_exact(pod.into_slice_mut().unwrap())?;
        Ok(pod)
    }

    /// Read a slice of pods from a Read stream.
    /// Uses a single read_exact call.
    fn read_pod_slice<T: Pod>(&mut self, len: usize) -> io::Result<Vec<T>> {
        let mut pod: Vec<T> = (0..len).map(|_| T::zeroed()).collect();
        self.read_exact(pod.into_slice_mut().unwrap())?;
        Ok(pod)
    }
}

/// Extension for writing Pod types.
/// # Example
/// ```
/// # use pod2::*;
/// # fn main() {
/// // Some writable sink
/// let mut writer: Vec<u8> = Vec::new();
/// 
/// writer.write_pod::<Be<u16>>(&Be::from(1)).unwrap();
/// writer.write_pod::<Be<u16>>(&Be::from(2)).unwrap();
/// writer.write_pod_slice::<u8>(&[ 0xcc, 0xdd, 0xee ]).unwrap();
/// 
/// assert_eq!(&writer, &[
///     0x00, 0x01, 
///     0x00, 0x02,
///     0xcc, 0xdd, 0xee
/// ]);
/// # }
/// ```
pub trait WritePod: Write {
    /// Write a single pod from a Write stream.
    fn write_pod<T: Pod>(&mut self, pod: &T) -> io::Result<()> {
        self.write_all(pod.into_slice().unwrap())
    }

    /// Write a slice of pods to a Write stream.
    /// Uses a single write_all call.
    fn write_pod_slice<T: Pod>(&mut self, pod: &[T]) -> io::Result<()> {
        self.write_all(pod.into_slice().unwrap())
    }
}

impl<T: Read> ReadPod for T {}
impl<T: Write> WritePod for T {}

/// Trait marking Plain Old Data types.
/// # Safety
/// Implementing this trait is not safe because it internally
/// uses a lot of `unsafe` on the assumption that the underlying
/// data is passive, and reinterpretation of the data is safe.
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

/// Trait marking an object that can be constructed from a pod.
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

/// Trait for creating pod types.
pub trait IntoPod {
    /// Create a Pod reference from self.
    fn into_ref<U: Pod>(&self) -> Option<&U>;
    /// Create a Pod slice from self.
    fn into_slice<U: Pod>(&self) -> Option<&[U]>;
    /// Create a Pod reference from self.
    fn into_ref_mut<U: Pod>(&mut self) -> Option<&mut U>;
    /// Create a Pod slice from self.
    fn into_slice_mut<U: Pod>(&mut self) -> Option<&mut [U]>;
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

impl<T: FromPod + Pod> IntoPod for T {
    fn into_ref<U: Pod>(&self) -> Option<&U> {
        U::from_ref(self)
    }

    fn into_slice<U: Pod>(&self) -> Option<&[U]> {
        <[U]>::from_ref(self)
    }

    fn into_ref_mut<U: Pod>(&mut self) -> Option<&mut U> {
        U::from_ref_mut(self)
    }

    fn into_slice_mut<U: Pod>(&mut self) -> Option<&mut [U]> {
        <[U]>::from_ref_mut(self)
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

impl<T: FromPod + Pod> IntoPod for [T] {
    fn into_ref<U: Pod>(&self) -> Option<&U> {
        U::from_slice(self)
    }

    fn into_slice<U: Pod>(&self) -> Option<&[U]> {
        <[U]>::from_slice(self)
    }

    fn into_ref_mut<U: Pod>(&mut self) -> Option<&mut U> {
        U::from_slice_mut(self)
    }

    fn into_slice_mut<U: Pod>(&mut self) -> Option<&mut [U]> {
        <[U]>::from_slice_mut(self)
    }
}

impl FromPod for str {
    fn from_ref<U: Pod>(other: &U) -> Option<&Self> {
        std::str::from_utf8(<[u8]>::from_ref(other)?).ok()
    }

    fn from_slice<U: Pod>(other: &[U]) -> Option<&Self> {
        std::str::from_utf8(<[u8]>::from_slice(other)?).ok()
    }

    fn from_ref_mut<U: Pod>(other: &mut U) -> Option<&mut Self> {
        std::str::from_utf8_mut(<[u8]>::from_ref_mut(other)?).ok()
    }

    fn from_slice_mut<U: Pod>(other: &mut [U]) -> Option<&mut Self> {
        std::str::from_utf8_mut(<[u8]>::from_slice_mut(other)?).ok()
    }
}

#[doc(hidden)]
pub trait Endian: Copy {
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
/// # Example
/// ```
/// # use pod2::*;
/// # fn main() {
/// let mut buf: [u8; 4] = [0; 4];
/// 
/// let int: &mut Be<u32> = Be::from_ref_mut(&mut buf).unwrap();
/// assert_eq!(int.get(), 0);
/// 
/// // The underlying data will be stored as
/// // big endian no matter the native endianess.
/// int.set(0xa1b2c3d4);
/// assert_eq!(&buf, &[ 0xa1, 0xb2, 0xc3, 0xd4 ]);
/// # }
/// ```
#[repr(transparent)]
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct Be<T>(T);

impl<T: Endian> Be<T> {
    /// Get the internal value.
    pub fn get(&self) -> T {
        T::be_to_ne(self.0)
    }

    /// Set the internal value.
    pub fn set(&mut self, val: T) {
        self.0 = T::ne_to_be(val);
    }
}

impl<T: Endian> From<T> for Be<T> {
    fn from(val: T) -> Self {
        Self(T::ne_to_be(val))
    }
}

impl<T: Endian + Debug> Debug for Be<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Be({:?})", self.get())
    }
}

/// Wrapper type holding the data in little endian order.
/// # Example
/// ```
/// # use pod2::*;
/// # fn main() {
/// let mut buf: [u8; 4] = [0; 4];
/// 
/// let int: &mut Le<u32> = Le::from_ref_mut(&mut buf).unwrap();
/// assert_eq!(int.get(), 0);
/// 
/// // The underlying data will be stored as
/// // little endian no matter the native endianess.
/// int.set(0xa1b2c3d4);
/// assert_eq!(&buf, &[ 0xd4, 0xc3, 0xb2, 0xa1 ]);
/// # }
/// ```
#[repr(transparent)]
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct Le<T>(T);

impl<T: Endian> Le<T> {
    /// Get the internal value.
    pub fn get(&self) -> T {
        T::le_to_ne(self.0)
    }

    /// Set the internal value.
    pub fn set(&mut self, val: T) {
        self.0 = T::ne_to_le(val);
    }
}

impl<T: Endian> From<T> for Le<T> {
    fn from(val: T) -> Self {
        Self(T::ne_to_le(val))
    }
}

impl<T: Endian + Debug> Debug for Le<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Le({:?})", self.get())
    }
}

unsafe impl<T: Pod> Pod for Be<T> {}
unsafe impl<T: Pod> Pod for Le<T> {}