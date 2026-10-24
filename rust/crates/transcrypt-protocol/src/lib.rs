//! Pure, zero-dependency parser for transcrypt object formats.
//!
//! Scope (see `docs/verification/04-dual-implementation-architecture.md`
//! and `docs/verification/10-decisions-and-blockers.md`):
//!
//! * Implemented: detection and structural parsing of the **released
//!   legacy (v2) format** — the format the shipped Bash implementation
//!   reads and writes.
//! * Not implemented: the future secure (v3) format. Its byte grammar is
//!   not frozen (decision D-01 pending); this crate must not define it
//!   by example, and its detection belongs to a future `detect_format`
//!   extension once the spec is approved.
//!
//! This crate performs **structure validation only**. It never derives
//! keys, never calls into a crypto library, and never sees a password:
//! those concerns belong to the future crypto adapter.

#![forbid(unsafe_code)]
#![deny(missing_debug_implementations)]
// Style lints that suggest std methods from very recent releases
// (is_multiple_of, repeat_n); we keep the crate buildable on a wider
// range of recent stable toolchains.
#![allow(clippy::manual_is_multiple_of, clippy::manual_repeat_n)]

mod base64;
mod v2;

pub use base64::base64_decode;
pub use v2::{
    detect_format, parse_v2, Format, V2_BASE64_PREFIX, V2Error, V2Record,
};

/// Structured errors from [`base64_decode`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Base64Error {
    /// A byte outside the alphabet/padding/line-break set.
    InvalidChar { offset: usize, byte: u8 },
    /// The number of content characters is not a multiple of four.
    BadLength { offset: usize },
    /// `=` padding in the wrong position or more than two of it.
    Padding { offset: usize },
    /// Residual (should-be-zero) bits set in a padded group.
    NonZeroPadding { offset: usize, byte: u8 },
}

impl Base64Error {
    pub(crate) fn invalid_char(offset: usize, byte: u8) -> Self {
        Self::InvalidChar { offset, byte }
    }
    pub(crate) fn bad_length(offset: usize, _byte: u8) -> Self {
        Self::BadLength { offset }
    }
    pub(crate) fn padding(offset: usize, _byte: u8) -> Self {
        Self::Padding { offset }
    }
    pub(crate) fn nonzero_pad(offset: usize, byte: u8) -> Self {
        Self::NonZeroPadding { offset, byte }
    }
}
