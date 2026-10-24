//! Writing what the compiler keeps as bytes, and reading it back: the
//! [`Encode`] and [`Decode`] of each kind of thing, over a [`Writer`] and
//! a [`Reader`] of LEB128 numbers, tags and lengths. An artifact is written
//! so, and so is the interface of a package.

use rustc_hash::FxHashMap;

use crate::file::FileId;
use crate::lex::Span;

mod ast;

/// Lists of what is encoded but bytes, which are encoded whole.
macro_rules! lists {
    ($($t:ty),* $(,)?) => {
        $(
            impl $crate::codec::Encode for Vec<$t> {
                fn encode(&self, w: &mut $crate::codec::Writer) {
                    self.len().encode(w);
                    self.iter().for_each(|item| item.encode(w));
                }
            }

            impl $crate::codec::Decode for Vec<$t> {
                fn decode(
                    r: &mut $crate::codec::Reader,
                ) -> Result<Self, $crate::codec::DecodeError> {
                    let len = <usize as $crate::codec::Decode>::decode(r)?;
                    // A length is bounded by what is left to read.
                    if len > r.left() {
                        return Err($crate::codec::DecodeError(
                            "a list is longer than the bytes".to_string(),
                        ));
                    }
                    (0..len).map(|_| <$t as $crate::codec::Decode>::decode(r)).collect()
                }
            }
        )*
    };
}

/// Ids, each its number.
macro_rules! ids {
    ($($t:ident),*) => {
        $(
            impl $crate::codec::Encode for $t {
                fn encode(&self, w: &mut $crate::codec::Writer) {
                    self.0.encode(w);
                }
            }

            impl $crate::codec::Decode for $t {
                fn decode(
                    r: &mut $crate::codec::Reader,
                ) -> Result<Self, $crate::codec::DecodeError> {
                    Ok($t($crate::codec::Decode::decode(r)?))
                }
            }
        )*
    };
}

pub(crate) use {ids, lists};

/// What bytes are written of.
pub(crate) trait Encode {
    fn encode(&self, w: &mut Writer);
}

/// What bytes are read as.
pub(crate) trait Decode: Sized {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError>;
}

/// Bytes being written. A file is written by its index among `files`,
/// which a file that isn't there yet is added to, so that what is read
/// back can give each file the id it has then: or by the index it was
/// minted from, where there are no files.
#[derive(Default)]
pub(crate) struct Writer {
    pub(crate) bytes: Vec<u8>,
    pub(crate) files: Vec<FileId>,
    file_index: FxHashMap<FileId, usize>,
    mapped: bool,
}

/// Bytes being read. A file is read as the id at its index among `files`,
/// or as the id minted from the index where there are none.
pub(crate) struct Reader<'b> {
    bytes: &'b [u8],
    at: usize,
    files: &'b [FileId],
    /// The libraries of the packages that what is read uses, by index.
    libraries: &'b [FileId],
}

/// Why bytes aren't what they were read as.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodeError(pub(crate) String);

impl DecodeError {
    /// Why bytes that name `what` aren't read: it isn't there.
    pub(crate) fn missing(what: &str) -> Self {
        Self(format!("`{what}` is not there"))
    }
}

impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::error::Error for DecodeError {}

impl Writer {
    /// A writer that writes each file by its index among `files`, and
    /// after them each other file it comes to, in the order it does.
    pub(crate) fn mapped(files: Vec<FileId>) -> Self {
        let file_index = files.iter().enumerate().map(|(i, f)| (*f, i)).collect();
        Self {
            bytes: Vec::new(),
            files,
            file_index,
            mapped: true,
        }
    }

    /// What `file` is written as.
    fn file(&mut self, file: FileId) -> usize {
        if !self.mapped {
            return file.index();
        }
        let next = self.files.len();
        let index = *self.file_index.entry(file).or_insert(next);
        if index == next {
            self.files.push(file);
        }
        index
    }

    /// `n` in LEB128, seven bits to a byte, the least first.
    fn unsigned(&mut self, mut n: u64) {
        loop {
            let byte = (n & 0x7f) as u8;
            n >>= 7;
            match n {
                0 => return self.bytes.push(byte),
                _ => self.bytes.push(byte | 0x80),
            }
        }
    }

    /// `n` in signed LEB128.
    fn signed(&mut self, mut n: i64) {
        loop {
            let byte = (n & 0x7f) as u8;
            n >>= 7;
            let done = (n == 0 && byte & 0x40 == 0) || (n == -1 && byte & 0x40 != 0);
            match done {
                true => return self.bytes.push(byte),
                false => self.bytes.push(byte | 0x80),
            }
        }
    }

    pub(crate) fn tag(&mut self, tag: u8) {
        self.bytes.push(tag);
    }
}

impl<'b> Reader<'b> {
    pub(crate) fn new(bytes: &'b [u8]) -> Self {
        Self {
            bytes,
            at: 0,
            files: &[],
            libraries: &[],
        }
    }

    /// A reader that reads each file as the id at its index among `files`.
    pub(crate) fn mapped(bytes: &'b [u8], files: &'b [FileId]) -> Self {
        Self {
            bytes,
            at: 0,
            files,
            libraries: &[],
        }
    }

    /// The reader, reading the library of each package that what it reads
    /// uses as the id at its index among `libraries`.
    pub(crate) fn with_libraries(mut self, libraries: &'b [FileId]) -> Self {
        self.libraries = libraries;
        self
    }

    /// The library of the package written as `index`.
    pub(crate) fn library(&self, index: usize) -> Result<FileId, DecodeError> {
        let library = self.libraries.get(index).copied();
        library.ok_or_else(|| DecodeError(format!("{index} is no package that is used")))
    }

    /// The file written as `index`.
    pub(crate) fn file(&self, index: usize) -> Result<FileId, DecodeError> {
        if self.files.is_empty() {
            return Ok(FileId::minted(index));
        }
        let file = self.files.get(index).copied();
        file.ok_or_else(|| DecodeError(format!("{index} is no file of the package")))
    }

    /// Whether every byte is read.
    pub(crate) fn done(&self) -> bool {
        self.at == self.bytes.len()
    }

    /// How many bytes are left to read.
    pub(crate) fn left(&self) -> usize {
        self.bytes.len() - self.at
    }

    /// Whether the bytes go on with `prefix`, which is then read.
    pub(crate) fn starts_with(&mut self, prefix: &[u8]) -> bool {
        let starts = self.bytes[self.at..].starts_with(prefix);
        if starts {
            self.at += prefix.len();
        }
        starts
    }

    fn byte(&mut self) -> Result<u8, DecodeError> {
        let byte = *self
            .bytes
            .get(self.at)
            .ok_or_else(|| DecodeError("the bytes end early".to_string()))?;
        self.at += 1;
        Ok(byte)
    }

    fn unsigned(&mut self) -> Result<u64, DecodeError> {
        let (mut n, mut shift) = (0u64, 0);
        loop {
            let byte = self.byte()?;
            if shift >= 64 {
                return Err(DecodeError("a number is too long".to_string()));
            }
            n |= u64::from(byte & 0x7f) << shift;
            shift += 7;
            if byte & 0x80 == 0 {
                return Ok(n);
            }
        }
    }

    fn signed(&mut self) -> Result<i64, DecodeError> {
        let (mut n, mut shift) = (0i64, 0);
        loop {
            let byte = self.byte()?;
            if shift >= 64 {
                return Err(DecodeError("a number is too long".to_string()));
            }
            n |= i64::from(byte & 0x7f) << shift;
            shift += 7;
            if byte & 0x80 == 0 {
                if shift < 64 && byte & 0x40 != 0 {
                    n |= -1 << shift;
                }
                return Ok(n);
            }
        }
    }

    pub(crate) fn tag(&mut self) -> Result<u8, DecodeError> {
        self.byte()
    }
}

/// Why a tag that was read stands for nothing.
pub(crate) fn bad(what: &str, tag: u8) -> DecodeError {
    DecodeError(format!("{tag} stands for no {what}"))
}

impl Encode for u64 {
    fn encode(&self, w: &mut Writer) {
        w.unsigned(*self);
    }
}

impl Decode for u64 {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        r.unsigned()
    }
}

impl Encode for u32 {
    fn encode(&self, w: &mut Writer) {
        w.unsigned((*self).into());
    }
}

impl Decode for u32 {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        let n = r.unsigned()?;
        u32::try_from(n).map_err(|_| DecodeError(format!("{n} is too large")))
    }
}

impl Encode for u8 {
    fn encode(&self, w: &mut Writer) {
        w.tag(*self);
    }
}

impl Decode for u8 {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        r.tag()
    }
}

impl Encode for usize {
    fn encode(&self, w: &mut Writer) {
        w.unsigned(*self as u64);
    }
}

impl Decode for usize {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        let n = r.unsigned()?;
        usize::try_from(n).map_err(|_| DecodeError(format!("{n} is too large")))
    }
}

impl Encode for i64 {
    fn encode(&self, w: &mut Writer) {
        w.signed(*self);
    }
}

impl Decode for i64 {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        r.signed()
    }
}

impl Encode for i32 {
    fn encode(&self, w: &mut Writer) {
        w.signed((*self).into());
    }
}

impl Decode for i32 {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        let n = r.signed()?;
        i32::try_from(n).map_err(|_| DecodeError(format!("{n} is too large")))
    }
}

impl Encode for u128 {
    fn encode(&self, w: &mut Writer) {
        ((*self >> 64) as u64).encode(w);
        (*self as u64).encode(w);
    }
}

impl Decode for u128 {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        let high = u64::decode(r)?;
        let low = u64::decode(r)?;
        Ok(u128::from(high) << 64 | u128::from(low))
    }
}

impl Encode for f64 {
    fn encode(&self, w: &mut Writer) {
        self.to_bits().encode(w);
    }
}

impl Decode for f64 {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(f64::from_bits(u64::decode(r)?))
    }
}

impl Encode for bool {
    fn encode(&self, w: &mut Writer) {
        w.tag(u8::from(*self));
    }
}

impl Decode for bool {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        match r.tag()? {
            0 => Ok(false),
            1 => Ok(true),
            tag => Err(bad("bool", tag)),
        }
    }
}

impl Encode for char {
    fn encode(&self, w: &mut Writer) {
        u32::from(*self).encode(w);
    }
}

impl Decode for char {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        let n = u32::decode(r)?;
        char::from_u32(n).ok_or_else(|| DecodeError(format!("{n} is no character")))
    }
}

impl Encode for String {
    fn encode(&self, w: &mut Writer) {
        self.len().encode(w);
        w.bytes.extend_from_slice(self.as_bytes());
    }
}

impl Decode for String {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        let bytes = Vec::<u8>::decode(r)?;
        String::from_utf8(bytes).map_err(|_| DecodeError("a name is no UTF-8".to_string()))
    }
}

impl Encode for Vec<u8> {
    fn encode(&self, w: &mut Writer) {
        self.len().encode(w);
        w.bytes.extend_from_slice(self);
    }
}

impl Decode for Vec<u8> {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        let len = usize::decode(r)?;
        let end = r.at.checked_add(len).filter(|end| *end <= r.bytes.len());
        let end = end.ok_or_else(|| DecodeError("the bytes end early".to_string()))?;
        let bytes = r.bytes[r.at..end].to_vec();
        r.at = end;
        Ok(bytes)
    }
}

lists!(String, Span);

impl<T: Encode> Encode for Option<T> {
    fn encode(&self, w: &mut Writer) {
        match self {
            None => w.tag(0),
            Some(value) => {
                w.tag(1);
                value.encode(w);
            }
        }
    }
}

impl<T: Decode> Decode for Option<T> {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        match r.tag()? {
            0 => Ok(None),
            1 => Ok(Some(T::decode(r)?)),
            tag => Err(bad("option", tag)),
        }
    }
}

impl<T: Encode> Encode for Box<T> {
    fn encode(&self, w: &mut Writer) {
        (**self).encode(w);
    }
}

impl<T: Decode> Decode for Box<T> {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Box::new(T::decode(r)?))
    }
}

impl<A: Encode, B: Encode> Encode for (A, B) {
    fn encode(&self, w: &mut Writer) {
        self.0.encode(w);
        self.1.encode(w);
    }
}

impl<A: Decode, B: Decode> Decode for (A, B) {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok((A::decode(r)?, B::decode(r)?))
    }
}

impl<A: Encode, B: Encode, C: Encode> Encode for (A, B, C) {
    fn encode(&self, w: &mut Writer) {
        self.0.encode(w);
        self.1.encode(w);
        self.2.encode(w);
    }
}

impl<A: Decode, B: Decode, C: Decode> Decode for (A, B, C) {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok((A::decode(r)?, B::decode(r)?, C::decode(r)?))
    }
}

/// A file is written as the writer writes files, and read as the reader
/// reads them.
impl Encode for FileId {
    fn encode(&self, w: &mut Writer) {
        w.file(*self).encode(w);
    }
}

impl Decode for FileId {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        let index = usize::decode(r)?;
        r.file(index)
    }
}

impl Encode for Span {
    fn encode(&self, w: &mut Writer) {
        self.file.encode(w);
        self.start.encode(w);
        self.end.encode(w);
    }
}

impl Decode for Span {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Span {
            file: Decode::decode(r)?,
            start: Decode::decode(r)?,
            end: Decode::decode(r)?,
        })
    }
}
