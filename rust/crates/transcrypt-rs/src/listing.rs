//! Snapshots of the index or of a commit's tree, as the verified core reads
//! them. A `Listing` keeps the exact bytes Git printed with the record ends
//! the core checked, and is the only code that passes them to the core, so
//! a decision can never be asked of one snapshot's bytes with another's
//! ends, or of a listing with an object order that is not its own.

use transcrypt_v3_core::{
    blob_elsewhere, first_unselectable, held_entries, listing_fields, next_move_source, object_order_ok,
    parse_listing as parse_listing_ends, parse_listing_attrs, OID_START,
};
use crate::git::{git_records, MODE_LEN};

/// One stage-0 record of the index or of a commit's tree. Every later read
/// of its content goes through `oid`, so a concurrent index change cannot
/// substitute other bytes for the ones that were verified.
pub(crate) struct Staged {
    /// The mode is 100644 or 100755 (`mode`): a file Git filters.
    pub(crate) regular: bool,
    pub(crate) mode: String,
    pub(crate) oid: String,
    pub(crate) path: Vec<u8>,
}

impl Staged {
    /// The entry of the fields of a record the verified core delimited.
    pub(crate) fn new(regular: bool, mode: &[u8], oid: &[u8], path: &[u8]) -> Result<Staged, String> {
        Ok(Staged {
            regular,
            mode: String::from_utf8_lossy(mode).into_owned(),
            oid: String::from_utf8(oid.to_vec()).map_err(|_| "malformed Git object id")?,
            path: path.to_vec(),
        })
    }

    /// The path, for messages.
    pub(crate) fn name(&self) -> std::borrow::Cow<'_, str> {
        String::from_utf8_lossy(&self.path)
    }
}

/// The paths of `entries`, for `protected_flags` and `attr_values`.
pub(crate) fn paths_of(entries: &[Staged]) -> Vec<&[u8]> {
    entries.iter().map(|e| e.path.as_slice()).collect()
}

/// One snapshot of the index or of a commit's tree: the exact listing (Git's
/// `ls-files --stage -z`, or `ls-tree -r -z` rewritten to the same records),
/// where each record ends, and its entries. The verified core checks the
/// whole listing (`parse_listing`: NUL-terminated stage-0 records with object
/// ids, in Git's byte order of paths, each path once, nothing else) and
/// delimits each entry's fields (`listing_fields`); the pre-commit decisions
/// are verified functions of `bytes` and `ends`.
pub(crate) struct Listing {
    bytes: Vec<u8>,
    ends: Vec<usize>,
    entries: Vec<Staged>,
}

impl Listing {
    /// Git's listing of the index or of one tree: each path once.
    pub(crate) fn parse(bytes: Vec<u8>) -> Result<Listing, String> {
        Listing::parse_ordered(bytes, true)
    }

    /// The records of several trees merged in path order (a path may repeat).
    pub(crate) fn merge(listings: Vec<Listing>) -> Result<Listing, String> {
        let mut records: Vec<&[u8]> = Vec::new();
        for listing in &listings { records.extend(git_records(&listing.bytes)?); }
        // Stable, by the path (after the first TAB) in byte order.
        fn path(record: &[u8]) -> &[u8] {
            record.iter().position(|b| *b == b'\t').map_or(&record[..0], |tab| &record[tab + 1..])
        }
        records.sort_by(|a, b| path(a).cmp(path(b)));
        Listing::parse_ordered(records.iter().flat_map(|r| r.iter().chain(&[0])).copied().collect(), false)
    }

    fn parse_ordered(bytes: Vec<u8>, unique: bool) -> Result<Listing, String> {
        // One slot per NUL; the core refuses unless that is exactly the
        // number of records.
        let mut ends = vec![0; bytes.iter().filter(|b| **b == 0).count()];
        if !parse_listing_ends(&bytes, &mut ends, unique) {
            if unique && parse_listing_ends(&bytes, &mut ends, false) {
                return Err("a Git tree lists a path twice or out of Git's order (a crafted tree?); \
                    `git fsck` reports it".into());
            }
            return Err("malformed or unmerged Git index entry; resolve conflicts first".into());
        }
        let entries = (0..ends.len()).map(|i| {
            let f = listing_fields(&bytes, &ends, i).ok_or("malformed Git listing")?;
            Staged::new(f.regular, &bytes[f.start..f.start + MODE_LEN], &bytes[f.start + OID_START..f.oid_end], &bytes[f.path_start..f.end])
        }).collect::<Result<_, String>>()?;
        Ok(Listing { bytes, ends, entries })
    }

    /// The listing of no entries.
    pub(crate) fn empty() -> Listing {
        Listing { bytes: Vec::new(), ends: Vec::new(), entries: Vec::new() }
    }

    pub(crate) fn entries(&self) -> &[Staged] {
        &self.entries
    }

    pub(crate) fn into_entries(self) -> Vec<Staged> {
        self.entries
    }

    /// The exact bytes Git printed, and the entries parsed from them.
    pub(crate) fn into_bytes_and_entries(self) -> (Vec<u8>, Vec<Staged>) {
        (self.bytes, self.entries)
    }

    /// Git's `check-attr -z` answer for this listing's paths, one flag per
    /// entry (the verified `parse_listing_attrs`), or `None` when the answer
    /// is not exactly one record per entry naming its path.
    pub(crate) fn attribute_flags(&self, response: &[u8]) -> Option<Vec<bool>> {
        let mut flags = vec![false; self.entries.len()];
        parse_listing_attrs(&self.bytes, &self.ends, response, &mut flags).then_some(flags)
    }

    /// The position of the first entry `flags` selects that cannot be
    /// protected (the verified `first_unselectable`), or the entry count.
    pub(crate) fn first_unselectable(&self, flags: &[bool]) -> usize {
        first_unselectable(&self.bytes, &self.ends, flags)
    }

    /// For each entry that is `wanted`, whether `other` holds its blob at
    /// its path (the verified `held_entries`).
    pub(crate) fn held_in(&self, wanted: &[bool], other: &Listing) -> Result<Vec<bool>, String> {
        let mut held = vec![false; self.entries.len()];
        if !held_entries(&self.bytes, &self.ends, wanted, &other.bytes, &other.ends, &mut held) {
            return Err("internal error: snapshot sizes differ".into());
        }
        Ok(held)
    }

    /// This listing with its object order: its positions sorted by object
    /// id, then position, which the verified `object_order_ok` checks.
    pub(crate) fn ordered(&self) -> Result<OrderedListing<'_>, String> {
        let mut order: Vec<usize> = (0..self.entries.len()).collect();
        order.sort_unstable_by(|a, b| self.entries[*a].oid.cmp(&self.entries[*b].oid).then(a.cmp(b)));
        if !object_order_ok(&self.bytes, &self.ends, &order) {
            return Err("internal error: object order of a Git listing".into());
        }
        Ok(OrderedListing { listing: self, order })
    }
}

/// A `Listing` with its verified object order, for the core's lookups of
/// blobs by object id.
pub(crate) struct OrderedListing<'a> {
    listing: &'a Listing,
    order: Vec<usize>,
}

impl<'a> OrderedListing<'a> {
    /// Whether the blob of entry `i` of this listing (the index) is at
    /// another path here, in `head` or in `parent` (the verified
    /// `blob_elsewhere`): a record moved or copied there.
    pub(crate) fn blob_elsewhere(&self, i: usize, head: &OrderedListing, parent: &OrderedListing) -> bool {
        let (index, head_listing, parent_listing) = (self.listing, head.listing, parent.listing);
        blob_elsewhere(&index.bytes, &index.ends, &self.order, i, &head_listing.bytes, &head_listing.ends,
            &head.order, &parent_listing.bytes, &parent_listing.ends, &parent.order)
    }

    /// The entries of this listing (`HEAD`) that entry `i` of `index` may
    /// have been moved from, in object order (the verified
    /// `next_move_source`: the same blob at another path, whose own entry
    /// has left the index).
    pub(crate) fn move_sources<'s>(&'s self, index: &'s Listing, i: usize) -> impl Iterator<Item = &'a Staged> + 's {
        let head = self.listing;
        let mut from = 0;
        std::iter::from_fn(move || {
            let j = next_move_source(&index.bytes, &index.ends, i, &head.bytes, &head.ends, &self.order, from);
            let source = head.entries.get(j)?;
            from = j + 1;
            Some(source)
        })
    }
}
