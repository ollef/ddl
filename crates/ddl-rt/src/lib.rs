//! Runtime support for the binary data description language.

#![warn(rust_2018_idioms)]

mod read;
mod write;

pub use read::{ReadBinary, ReadBinaryUnchecked, ReadCtxt, ReadEofError, ReadError, ReadScope};
pub use write::{WriteBinary, WriteCtxt};

/// Markers for data in binary form.
pub trait Binary {
    /// The host representation of this binary type.
    type Host;
}

/// Marks a section of data that was produced by an invalid data description.
///
/// Attempting to read this will always result in read error.
pub enum InvalidDataDescription {}

impl Binary for InvalidDataDescription {
    type Host = InvalidDataDescription;
}

impl<'data> ReadBinary<'data> for InvalidDataDescription {
    #[inline]
    fn read(_: &mut ReadCtxt<'data>) -> Result<InvalidDataDescription, ReadError> {
        Err(ReadError::InvalidDataDescription)
    }
}

/// Marker type for unsigned 8-bit integers.
#[derive(Copy, Clone)]
pub enum U8 {}

impl<'data> ReadBinaryUnchecked<'data> for U8 {
    const SIZE: usize = std::mem::size_of::<u8>();

    #[inline]
    unsafe fn read_unchecked(ctxt: &mut ReadCtxt<'data>) -> u8 {
        ctxt.read_unchecked_u8()
    }
}

impl WriteBinary for U8 {
    fn write(ctxt: &mut WriteCtxt, value: u8) {
        ctxt.write_u8(value);
    }
}

/// Marker type for unsigned 16-bit integers (little endian).
#[derive(Copy, Clone)]
pub enum U16Le {}

impl<'data> ReadBinaryUnchecked<'data> for U16Le {
    const SIZE: usize = std::mem::size_of::<u16>();

    #[inline]
    unsafe fn read_unchecked(ctxt: &mut ReadCtxt<'data>) -> u16 {
        let b0 = u16::from(ctxt.read_unchecked::<U8>());
        let b1 = u16::from(ctxt.read_unchecked::<U8>());
        b0 | (b1 << 8)
    }
}

impl WriteBinary for U16Le {
    fn write(ctxt: &mut WriteCtxt, value: u16) {
        ctxt.write_u8(value as u8);
        ctxt.write_u8((value >> 8) as u8);
    }
}

/// Marker type for unsigned 16-bit integers (big endian).
#[derive(Copy, Clone)]
pub enum U16Be {}

impl<'data> ReadBinaryUnchecked<'data> for U16Be {
    const SIZE: usize = std::mem::size_of::<u16>();

    #[inline]
    unsafe fn read_unchecked(ctxt: &mut ReadCtxt<'data>) -> u16 {
        let b0 = u16::from(ctxt.read_unchecked::<U8>());
        let b1 = u16::from(ctxt.read_unchecked::<U8>());
        (b0 << 8) | b1
    }
}

impl WriteBinary for U16Be {
    fn write(ctxt: &mut WriteCtxt, value: u16) {
        ctxt.write_u8((value >> 8) as u8);
        ctxt.write_u8(value as u8);
    }
}

/// Marker type for unsigned 32-bit integers (little endian).
#[derive(Copy, Clone)]
pub enum U32Le {}

impl<'data> ReadBinaryUnchecked<'data> for U32Le {
    const SIZE: usize = std::mem::size_of::<u32>();

    #[inline]
    unsafe fn read_unchecked(ctxt: &mut ReadCtxt<'data>) -> u32 {
        let b0 = u32::from(ctxt.read_unchecked::<U8>());
        let b1 = u32::from(ctxt.read_unchecked::<U8>());
        let b2 = u32::from(ctxt.read_unchecked::<U8>());
        let b3 = u32::from(ctxt.read_unchecked::<U8>());
        b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)
    }
}

impl WriteBinary for U32Le {
    fn write(ctxt: &mut WriteCtxt, value: u32) {
        ctxt.write_u8(value as u8);
        ctxt.write_u8((value >> 8) as u8);
        ctxt.write_u8((value >> 16) as u8);
        ctxt.write_u8((value >> 24) as u8);
    }
}

/// Marker type for unsigned 32-bit integers (big endian).
#[derive(Copy, Clone)]
pub enum U32Be {}

impl<'data> ReadBinaryUnchecked<'data> for U32Be {
    const SIZE: usize = std::mem::size_of::<u32>();

    #[inline]
    unsafe fn read_unchecked(ctxt: &mut ReadCtxt<'data>) -> u32 {
        let b0 = u32::from(ctxt.read_unchecked::<U8>());
        let b1 = u32::from(ctxt.read_unchecked::<U8>());
        let b2 = u32::from(ctxt.read_unchecked::<U8>());
        let b3 = u32::from(ctxt.read_unchecked::<U8>());
        (b0 << 24) | (b1 << 16) | (b2 << 8) | b3
    }
}

impl WriteBinary for U32Be {
    fn write(ctxt: &mut WriteCtxt, value: u32) {
        ctxt.write_u8((value >> 24) as u8);
        ctxt.write_u8((value >> 16) as u8);
        ctxt.write_u8((value >> 8) as u8);
        ctxt.write_u8(value as u8);
    }
}

/// Marker type for unsigned 64-bit integers (little endian).
#[derive(Copy, Clone)]
pub enum U64Le {}

impl<'data> ReadBinaryUnchecked<'data> for U64Le {
    const SIZE: usize = std::mem::size_of::<u64>();

    #[inline]
    unsafe fn read_unchecked(ctxt: &mut ReadCtxt<'data>) -> u64 {
        let b0 = u64::from(ctxt.read_unchecked::<U8>());
        let b1 = u64::from(ctxt.read_unchecked::<U8>());
        let b2 = u64::from(ctxt.read_unchecked::<U8>());
        let b3 = u64::from(ctxt.read_unchecked::<U8>());
        let b4 = u64::from(ctxt.read_unchecked::<U8>());
        let b5 = u64::from(ctxt.read_unchecked::<U8>());
        let b6 = u64::from(ctxt.read_unchecked::<U8>());
        let b7 = u64::from(ctxt.read_unchecked::<U8>());
        b0 | (b1 << 8) | (b2 << 16) | (b3 << 24) | (b4 << 32) | (b5 << 40) | (b6 << 48) | (b7 << 56)
    }
}

impl WriteBinary for U64Le {
    fn write(ctxt: &mut WriteCtxt, value: u64) {
        ctxt.write_u8(value as u8);
        ctxt.write_u8((value >> 8) as u8);
        ctxt.write_u8((value >> 16) as u8);
        ctxt.write_u8((value >> 24) as u8);
        ctxt.write_u8((value >> 32) as u8);
        ctxt.write_u8((value >> 40) as u8);
        ctxt.write_u8((value >> 48) as u8);
        ctxt.write_u8((value >> 56) as u8);
    }
}

/// Marker type for unsigned 64-bit integers (big endian).
#[derive(Copy, Clone)]
pub enum U64Be {}

impl<'data> ReadBinaryUnchecked<'data> for U64Be {
    const SIZE: usize = std::mem::size_of::<u64>();

    #[inline]
    unsafe fn read_unchecked(ctxt: &mut ReadCtxt<'data>) -> u64 {
        let b0 = u64::from(ctxt.read_unchecked::<U8>());
        let b1 = u64::from(ctxt.read_unchecked::<U8>());
        let b2 = u64::from(ctxt.read_unchecked::<U8>());
        let b3 = u64::from(ctxt.read_unchecked::<U8>());
        let b4 = u64::from(ctxt.read_unchecked::<U8>());
        let b5 = u64::from(ctxt.read_unchecked::<U8>());
        let b6 = u64::from(ctxt.read_unchecked::<U8>());
        let b7 = u64::from(ctxt.read_unchecked::<U8>());
        (b0 << 56) | (b1 << 48) | (b2 << 40) | (b3 << 32) | (b4 << 24) | (b5 << 16) | (b6 << 8) | b7
    }
}

impl WriteBinary for U64Be {
    fn write(ctxt: &mut WriteCtxt, value: u64) {
        ctxt.write_u8((value >> 56) as u8);
        ctxt.write_u8((value >> 48) as u8);
        ctxt.write_u8((value >> 40) as u8);
        ctxt.write_u8((value >> 32) as u8);
        ctxt.write_u8((value >> 24) as u8);
        ctxt.write_u8((value >> 16) as u8);
        ctxt.write_u8((value >> 8) as u8);
        ctxt.write_u8(value as u8);
    }
}

macro_rules! impl_uint_marker {
    ($UInt:ident, $uint:ident) => {
        // TODO: Generate ReadBinaryUnchecked implementations

        impl Binary for $UInt {
            type Host = $uint;
        }

        impl<'data> ReadBinary<'data> for $UInt {
            #[inline]
            fn read(ctxt: &mut ReadCtxt<'data>) -> Result<$uint, ReadError> {
                ctxt.check_available($UInt::SIZE)?;
                Ok(unsafe { ctxt.read_unchecked::<$UInt>() })
            }
        }
    };
}

impl_uint_marker!(U8, u8);
impl_uint_marker!(U16Le, u16);
impl_uint_marker!(U16Be, u16);
impl_uint_marker!(U32Le, u32);
impl_uint_marker!(U32Be, u32);
impl_uint_marker!(U64Le, u64);
impl_uint_marker!(U64Be, u64);

/// Marker type for signed, two's complement 8-bit integers.
#[derive(Copy, Clone)]
pub enum I8 {}

/// Marker type for signed, two's complement 16-bit integers (little endian).
#[derive(Copy, Clone)]
pub enum I16Le {}

/// Marker type for signed, two's complement 16-bit integers (big endian).
#[derive(Copy, Clone)]
pub enum I16Be {}

/// Marker type for signed, two's complement 32-bit integers (little endian).
#[derive(Copy, Clone)]
pub enum I32Le {}

/// Marker type for signed, two's complement 32-bit integers (big endian).
#[derive(Copy, Clone)]
pub enum I32Be {}

/// Marker type for signed, two's complement 64-bit integers (little endian).
#[derive(Copy, Clone)]
pub enum I64Le {}

/// Marker type for signed, two's complement 64-bit integers (big endian).
#[derive(Copy, Clone)]
pub enum I64Be {}

macro_rules! impl_int_marker {
    ($Int:ident, $UInt:ident, $int:ident) => {
        impl Binary for $Int {
            type Host = $int;
        }

        impl<'data> ReadBinaryUnchecked<'data> for $Int {
            const SIZE: usize = std::mem::size_of::<$int>();

            #[inline]
            unsafe fn read_unchecked(ctxt: &mut ReadCtxt<'data>) -> $int {
                ctxt.read_unchecked::<$UInt>() as $int
            }
        }

        impl<'data> ReadBinary<'data> for $Int {
            #[inline]
            fn read(ctxt: &mut ReadCtxt<'data>) -> Result<$int, ReadError> {
                ctxt.read::<$UInt>().map(|value| value as $int)
            }
        }

        impl WriteBinary for $Int {
            #[inline]
            fn write(ctxt: &mut WriteCtxt, value: $int) {
                ctxt.write::<$UInt>(unsafe { std::mem::transmute::<$int, _>(value) });
            }
        }
    };
}

impl_int_marker!(I8, U8, i8);
impl_int_marker!(I16Le, U16Le, i16);
impl_int_marker!(I16Be, U16Be, i16);
impl_int_marker!(I32Le, U32Le, i32);
impl_int_marker!(I32Be, U32Be, i32);
impl_int_marker!(I64Le, U64Le, i64);
impl_int_marker!(I64Be, U64Be, i64);

/// Marker type for IEEE754 single-precision floating point numbers (little endian).
#[derive(Copy, Clone)]
pub enum F32Le {}

/// Marker type for IEEE754 single-precision floating point numbers (big endian).
#[derive(Copy, Clone)]
pub enum F32Be {}

/// Marker type for IEEE754 double-precision floating point numbers (little endian).
#[derive(Copy, Clone)]
pub enum F64Le {}

/// Marker type for IEEE754 double-precision floating point numbers (big endian).
#[derive(Copy, Clone)]
pub enum F64Be {}

macro_rules! impl_float_marker {
    ($Float:ident, $UInt:ident, $float:ident) => {
        impl Binary for $Float {
            type Host = $float;
        }

        impl<'data> ReadBinaryUnchecked<'data> for $Float {
            const SIZE: usize = std::mem::size_of::<$float>();

            #[inline]
            unsafe fn read_unchecked(ctxt: &mut ReadCtxt<'data>) -> $float {
                std::mem::transmute::<_, $float>(ctxt.read_unchecked::<$UInt>())
            }
        }

        impl<'data> ReadBinary<'data> for $Float {
            #[inline]
            fn read(ctxt: &mut ReadCtxt<'data>) -> Result<$float, ReadError> {
                ctxt.read::<$UInt>()
                    .map(|value| unsafe { std::mem::transmute::<_, $float>(value) })
            }
        }

        impl WriteBinary for $Float {
            #[inline]
            fn write(ctxt: &mut WriteCtxt, value: $float) {
                ctxt.write::<$UInt>(unsafe { std::mem::transmute::<$float, _>(value) });
            }
        }
    };
}

impl_float_marker!(F32Le, U32Le, f32);
impl_float_marker!(F32Be, U32Be, f32);
impl_float_marker!(F64Le, U64Le, f64);
impl_float_marker!(F64Be, U64Be, f64);

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::*;

    fn round_trip<'data, T: WriteBinary + ReadBinary<'data>>(
        ctxt: &'data mut WriteCtxt,
        value: T::Host,
    ) -> T::Host {
        ctxt.write::<T>(value);
        let ctxt = ReadScope::new(ctxt.buffer());
        ctxt.read::<T>().unwrap()
    }

    proptest! {
        #[test]
        fn u8_round_trip(value: u8) {
            let mut ctxt = WriteCtxt::new(vec![]);
            prop_assert_eq!(round_trip::<U8>(&mut ctxt, value), value);
        }

        #[test]
        fn u16le_round_trip(value: u16) {
            let mut ctxt = WriteCtxt::new(vec![]);
            prop_assert_eq!(round_trip::<U16Le>(&mut ctxt, value), value);
        }

        #[test]
        fn u16be_round_trip(value: u16) {
            let mut ctxt = WriteCtxt::new(vec![]);
            prop_assert_eq!(round_trip::<U16Be>(&mut ctxt, value), value);
        }

        #[test]
        fn u32le_round_trip(value: u32) {
            let mut ctxt = WriteCtxt::new(vec![]);
            prop_assert_eq!(round_trip::<U32Le>(&mut ctxt, value), value);
        }

        #[test]
        fn u32be_round_trip(value: u32) {
            let mut ctxt = WriteCtxt::new(vec![]);
            prop_assert_eq!(round_trip::<U32Be>(&mut ctxt, value), value);
        }

        #[test]
        fn u64le_round_trip(value: u64) {
            let mut ctxt = WriteCtxt::new(vec![]);
            prop_assert_eq!(round_trip::<U64Le>(&mut ctxt, value), value);
        }

        #[test]
        fn u64be_round_trip(value: u64) {
            let mut ctxt = WriteCtxt::new(vec![]);
            prop_assert_eq!(round_trip::<U64Be>(&mut ctxt, value), value);
        }
        #[test]
        fn i8_round_trip(value: i8) {
            let mut ctxt = WriteCtxt::new(vec![]);
            prop_assert_eq!(round_trip::<I8>(&mut ctxt, value), value);
        }

        #[test]
        fn i16le_round_trip(value: i16) {
            let mut ctxt = WriteCtxt::new(vec![]);
            prop_assert_eq!(round_trip::<I16Le>(&mut ctxt, value), value);
        }

        #[test]
        fn i16be_round_trip(value: i16) {
            let mut ctxt = WriteCtxt::new(vec![]);
            prop_assert_eq!(round_trip::<I16Be>(&mut ctxt, value), value);
        }

        #[test]
        fn i32le_round_trip(value: i32) {
            let mut ctxt = WriteCtxt::new(vec![]);
            prop_assert_eq!(round_trip::<I32Le>(&mut ctxt, value), value);
        }

        #[test]
        fn i32be_round_trip(value: i32) {
            let mut ctxt = WriteCtxt::new(vec![]);
            prop_assert_eq!(round_trip::<I32Be>(&mut ctxt, value), value);
        }

        #[test]
        fn i64le_round_trip(value: i64) {
            let mut ctxt = WriteCtxt::new(vec![]);
            prop_assert_eq!(round_trip::<I64Le>(&mut ctxt, value), value);
        }

        #[test]
        fn i64be_round_trip(value: i64) {
            let mut ctxt = WriteCtxt::new(vec![]);
            prop_assert_eq!(round_trip::<I64Be>(&mut ctxt, value), value);
        }

        #[test]
        fn f32le_round_trip(value in proptest::num::f32::ANY) {
            let mut ctxt = WriteCtxt::new(vec![]);
            if value.is_nan() {
                prop_assert!(round_trip::<F32Le>(&mut ctxt, value).is_nan());
            } else {
                prop_assert_eq!(round_trip::<F32Le>(&mut ctxt, value), value);
            }
        }

        #[test]
        fn f32be_round_trip(value in proptest::num::f32::ANY) {
            let mut ctxt = WriteCtxt::new(vec![]);
            if value.is_nan() {
                prop_assert!(round_trip::<F32Be>(&mut ctxt, value).is_nan());
            } else {
                prop_assert_eq!(round_trip::<F32Be>(&mut ctxt, value), value);
            }
        }

        #[test]
        fn f64le_round_trip(value in proptest::num::f64::ANY) {
            let mut ctxt = WriteCtxt::new(vec![]);
            if value.is_nan() {
                prop_assert!(round_trip::<F64Le>(&mut ctxt, value).is_nan());
            } else {
                prop_assert_eq!(round_trip::<F64Le>(&mut ctxt, value), value);
            }
        }

        #[test]
        fn f64be_round_trip(value in proptest::num::f64::ANY) {
            let mut ctxt = WriteCtxt::new(vec![]);
            if value.is_nan() {
                prop_assert!(round_trip::<F64Be>(&mut ctxt, value).is_nan());
            } else {
                prop_assert_eq!(round_trip::<F64Be>(&mut ctxt, value), value);
            }
        }
    }
}
