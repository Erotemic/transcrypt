import V3Wire.Verification.SnapshotListing
import V3Wire.Verification.SnapshotOrder
import V3Wire.Verification.SnapshotAttrs
import V3Wire.Verification.SnapshotLookup
import V3Wire.Verification.SnapshotMoves

/-!
Functional refinement of the production Git snapshot functions: the inputs
of the pre-commit decisions. `parse_listing` accepts exactly the listings
`Transcrypt.V3Policy.listingBytes es` of well-formed entries in Git's byte
order of paths (`Sorted`: each path once; or, for merged trees,
`PathOrdered`) and records where each record ends (`ListingOf`); every
query over such a listing computes the spec's predicate on its entries:
`listing_fields` (the fields of one entry), `held_entries` (`Holds`, by
binary search), `is_local_change` (`LocalChange`), `next_move_source`
(`MoveSource`, first at or after an offset, through an object order
checked by `object_order_ok`), `blob_elsewhere` (`BlobElsewhere`, likewise),
`parse_listing_attrs` (Git's attribute answer for exactly the listing's
paths, `attrResponse`) and `first_unselectable` (`Selectable`).

The proofs are split by topic: `SnapshotListing` (records and fields),
`SnapshotOrder` (byte order, `parse_listing`), `SnapshotAttrs` (per-entry
decisions), `SnapshotLookup` (path lookups) and `SnapshotMoves` (object
orders and moves).
-/
