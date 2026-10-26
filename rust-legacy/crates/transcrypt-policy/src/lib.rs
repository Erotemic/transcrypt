//! Pure decision gates for the future authenticated format.
//!
//! These gates are deliberately separated from Git, crypto, and I/O.
//! Every `true` security witness below MUST be obtained from the correct
//! staged Git snapshot and an independent verified crypto operation.
//! Neither a ciphertext prefix nor a worktree inspection suffices.
//!
//! These functions are *not yet called* by the legacy Bash filter. They
//! specify a narrow prospective Rust adapter boundary, not the finished
//! Transcrypt v3 implementation. Their boolean algebra is model-checked
//! independently in `proofs/smt/policy_bitvector.c`.

#![no_std]
#![forbid(unsafe_code)]

/// Approve a *protected* staged regular file for a modern-format commit.
///
/// This only handles per-path evidence. A caller must enumerate every
/// applicable staged path and verify the shared staged metadata snapshot.
/// `authenticated` means a full authentication check, not a magic prefix.
/// `metadata_matches` includes all relevant context, KDF, cipher and salt
/// bindings; `staged_regular` must come from the index, not the worktree.
#[inline]
pub fn secure_stage_allowed(
    staged_protected: bool,
    local_protected: bool,
    staged_regular: bool,
    config_complete: bool,
    metadata_matches: bool,
    authenticated: bool,
) -> bool {
    (staged_protected || local_protected)
        && staged_regular
        && config_complete
        && metadata_matches
        && authenticated
}

/// Only after independent authentication and preflight may unlocking
/// publish persistent credential/filter changes. A false result means
/// *zero persistent writes*, enforced by the consuming adapter.
#[inline]
pub fn unlock_writes_allowed(
    authenticated: bool,
    public_config_valid: bool,
    destination_safe: bool,
    source_snapshot_stable: bool,
) -> bool {
    authenticated && public_config_valid && destination_safe && source_snapshot_stable
}

/// The final publication gate for a candidate migration prepared in a
/// separate index. A true result is only permission to attempt atomic
/// publication; this cannot itself prove OS/Git transaction atomicity.
#[inline]
pub fn migration_publish_allowed(
    source_fully_authenticated: bool,
    all_contexts_accounted_for: bool,
    target_tree_authenticated: bool,
    target_metadata_complete: bool,
    source_snapshot_stable: bool,
    rollback_available: bool,
) -> bool {
    source_fully_authenticated
        && all_contexts_accounted_for
        && target_tree_authenticated
        && target_metadata_complete
        && source_snapshot_stable
        && rollback_available
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exhaustive_secure_stage_inputs() {
        for mask in 0u8..64u8 {
            let p = mask & 1 != 0;
            let l = mask & 2 != 0;
            let r = mask & 4 != 0;
            let c = mask & 8 != 0;
            let m = mask & 16 != 0;
            let a = mask & 32 != 0;
            let accepted = secure_stage_allowed(p, l, r, c, m, a);
            if accepted {
                assert!(p || l);
                assert!(r && c && m && a);
            }
            assert_eq!(accepted, (p || l) && r && c && m && a);
        }
    }

    #[test]
    fn exhaustive_unlock_inputs() {
        for mask in 0u8..16u8 {
            let a = mask & 1 != 0;
            let c = mask & 2 != 0;
            let d = mask & 4 != 0;
            let s = mask & 8 != 0;
            let accepted = unlock_writes_allowed(a, c, d, s);
            if !a { assert!(!accepted); }
            assert_eq!(accepted, a && c && d && s);
        }
    }

    #[test]
    fn exhaustive_migration_inputs() {
        for mask in 0u8..64u8 {
            let a = mask & 1 != 0;
            let b = mask & 2 != 0;
            let c = mask & 4 != 0;
            let d = mask & 8 != 0;
            let e = mask & 16 != 0;
            let f = mask & 32 != 0;
            let accepted = migration_publish_allowed(a, b, c, d, e, f);
            assert_eq!(accepted, a && b && c && d && e && f);
        }
    }
}
