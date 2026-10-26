import V3Wire.Verification.Snapshot
import Transcrypt.V3Policy
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
namespace Transcrypt.V3Verification
open transcrypt_v3_core

/-!
Functional refinement of two adapter-facing decisions about stored and
fetched bytes: `stored_key_state` (what the stored key file means for the
current configuration: `storedKeySpec`) and Git's `cat-file --batch` reply
framing, `parse_batch_header` (exactly `BatchHeader`: the requested object
id, type `blob`, a canonical decimal size) and `blob_read` (`blobReadSpec`:
only blobs within the record bound are loaded).
-/

open Transcrypt.V3Policy

/-! ## The stored key -/

/-- Rust encoding of the specification's stored-key states. -/
def storedKeyResult : Transcrypt.V3Policy.StoredKey → transcrypt_v3_core.StoredKey
  | .absent => .Absent
  | .damaged => .Damaged
  | .stale => .Stale
  | .unlocked => .Unlocked

/-- **Stored key.** `stored_key_state` decides exactly `storedKeySpec`: a
    key is `Unlocked` only for a 119-byte file whose first 55 bytes are the
    current configuration, and only if the key authenticates it
    (`storedKeySpec_unlocked`). -/
theorem stored_key_state_spec (present : Bool) (file current : Slice U8) (authentic : Bool) :
    stored_key_state present file current authentic ⦃ r =>
      r = storedKeyResult (storedKeySpec present (sliceBytes file) (sliceBytes current) authentic) ⦄ := by
  have hfl := sliceBytes_length file
  unfold stored_key_state storedKeySpec
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
  have hk : KEY_LEN.val = 64 := by unfold KEY_LEN; rfl
  have hkf : KEY_FILE_LEN.val = 119 := by unfold KEY_FILE_LEN; rfl
  have hc : CONFIG_LEN.val = 55 := by unfold CONFIG_LEN; rfl
  split
  · rename_i hp
    split
    · rename_i h64
      have : file.length = 64 := by rw [← hk]; have := congrArg UScalar.val h64; simpa using this
      simp [storedKeyResult, hfl, this]
    · rename_i h64
      have h64' : file.length ≠ 64 := by
        intro h; apply h64; apply UScalar.eq_of_val_eq; simp [hk, h]
      split
      · rename_i h119
        have h119' : file.length ≠ 119 := by
          intro h; simp only [bne_iff_ne, ne_eq] at h119; apply h119; apply UScalar.eq_of_val_eq; simp [hkf, h]
        simp [storedKeyResult, hfl, h64', h119', hp]
      · rename_i h119
        have h119' : file.length = 119 := by
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h119
          have := congrArg UScalar.val h119; simpa [hkf] using this
        step with index_range_spec file 0#usize CONFIG_LEN (by simp) (by rw [hc]; omega) as ⟨ s, hs ⟩
        step with bytes_eq_spec as ⟨ b, hb ⟩
        have hst : sliceBytes s = (sliceBytes file).take 55 := by
          rw [hs, hc, List.extract_eq_take_drop]; simp
        rw [← sliceBytes_inj, hst] at hb
        simp only [hp, hfl, h119', Bool.true_eq_false, false_or, if_false, ne_eq, not_true_eq_false]
        split
        · rename_i hbt
          split
          · rename_i ha
            simp [storedKeyResult, hb.mp hbt, ha]
          · rename_i ha
            simp [storedKeyResult, ha]
        · rename_i hbt
          have hn : ¬(List.take 55 (sliceBytes file) = sliceBytes current ∧ authentic = true) :=
            fun h => hbt (hb.mpr h.1)
          simp [hn, storedKeyResult]
  · rename_i hp
    simp [storedKeyResult, hp]

/-! ## Object replies -/

/-- Rust encoding of the specification's blob-read decisions. -/
def blobReadResult : Transcrypt.V3Policy.BlobRead → transcrypt_v3_core.BlobRead
  | .read => .Read
  | .skip => .Skip
  | .tooLarge => .TooLarge

/-- `blob_read` loads only blobs within the record bound (`blobReadSpec`). -/
theorem blob_read_spec (size : U64) (skip : Bool) :
    blob_read size skip ⦃ r => r = blobReadResult (blobReadSpec size.val skip) ⦄ := by
  unfold blob_read blobReadSpec
  step with MAX_RECORD_spec as ⟨ m, hm ⟩
  step*
  all_goals
    have hi1 : i1.val = maxRecord := by
      rw [i1_post, UScalar.cast_val_eq, hm]; simp [maxRecord, maxFile, UScalarTy.numBits]
  · have : size.val ≤ maxRecord := by scalar_tac
    simp [this, blobReadResult]
  · have : ¬ size.val ≤ maxRecord := by scalar_tac
    simp [this, blobReadResult]
  · have : ¬ size.val ≤ maxRecord := by scalar_tac
    simp [this, blobReadResult]

/-! ## `cat-file --batch` headers -/

theorem BLOB_FIELD_bytes : sliceBytes (Array.to_slice BLOB_FIELD) = blobField := by
  unfold BLOB_FIELD blobField ascii sliceBytes
  decide

theorem decimalValue_append (l : List Nat) (c : Nat) :
    decimalValue (l ++ [c]) = decimalValue l * 10 + (c - 48) := by
  simp [decimalValue, List.foldl_append]

theorem decimal_foldl_lt (l : List Nat) (hl : ∀ c ∈ l, DecimalDigit c) (acc k : Nat) (h : acc < 10 ^ k) :
    l.foldl (fun v c => v * 10 + (c - 48)) acc < 10 ^ (k + l.length) := by
  induction l generalizing acc k with
  | nil => simpa using h
  | cons c l ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hc := hl c (by simp)
    have : acc * 10 + (c - 48) < 10 ^ (k + 1) := by
      rw [pow_succ]; unfold DecimalDigit at hc; omega
    have := ih (fun x hx => hl x (by simp [hx])) _ _ this
    rwa [show k + 1 + l.length = k + (l.length + 1) by omega] at this

theorem decimalValue_lt (l : List Nat) (hl : ∀ c ∈ l, DecimalDigit c) :
    decimalValue l < 10 ^ l.length := by
  have := decimal_foldl_lt l hl 0 0 (by simp)
  simpa [decimalValue] using this

theorem extract_snoc (L : List Nat) {a i : Nat} (hai : a ≤ i) (hi : i < L.length) :
    L.extract a (i + 1) = L.extract a i ++ [L[i]!] := by
  rw [List.extract_eq_take_drop, List.extract_eq_take_drop, show i + 1 - a = (i - a) + 1 by omega,
    List.take_add_one, List.getElem?_drop, show a + (i - a) = i by omega, List.getElem?_eq_getElem hi,
    getElem!_pos L i hi]
  rfl

/-- Loop invariant of `decimal`. -/
def DecInv (bytes : Slice U8) (from_ to_ : Nat) (value : Nat) (ok : Bool) (i : Nat) : Prop :=
  from_ ≤ i ∧ i ≤ to_ ∧
  (ok = true → value = decimalValue ((sliceBytes bytes).extract from_ i) ∧
    ∀ c ∈ (sliceBytes bytes).extract from_ i, DecimalDigit c) ∧
  (ok = false → ∃ c ∈ (sliceBytes bytes).extract from_ to_, ¬ DecimalDigit c)

theorem decimal_spec (bytes : Slice U8) (from_ to_ : Usize) (hft : from_.val ≤ to_.val)
    (hto : to_.val ≤ bytes.length) (h19 : to_.val - from_.val ≤ 19) :
    decimal bytes from_ to_ ⦃ r => match r with
      | core.option.Option.Some v => (∀ c ∈ (sliceBytes bytes).extract from_.val to_.val, DecimalDigit c) ∧
          v.val = decimalValue ((sliceBytes bytes).extract from_.val to_.val)
      | core.option.Option.None => ∃ c ∈ (sliceBytes bytes).extract from_.val to_.val, ¬ DecimalDigit c ⦄ := by
  have hbl := sliceBytes_length bytes
  have hto' : to_.val ≤ bytes.val.length := hto
  have hbl' : (sliceBytes bytes).length = bytes.val.length := hbl
  unfold decimal decimal_loop
  step with loop.spec_decr_nat
    (fun s : U64 × Bool × Usize => 2 * (to_.val - s.2.2.val) + (if s.2.1 then 1 else 0))
    (fun s : U64 × Bool × Usize => DecInv bytes from_.val to_.val s.1.val s.2.1 s.2.2.val)
    (fun s : U64 × Bool => DecInv bytes from_.val to_.val s.1.val s.2 to_.val) as ⟨ v, okr, hinv ⟩
  · rintro ⟨value, ok, i⟩ hinv
    dsimp only at hinv ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hinv
    unfold decimal_loop.body
    split
    · rename_i hok
      obtain ⟨hv, hd⟩ := h3 hok
      split
      · rename_i hit
        have hi : i.val < to_.val := by scalar_tac
        have hvlt : value.val < 10 ^ 18 := by
          have := decimalValue_lt _ hd
          rw [← hv] at this
          have hl : ((sliceBytes bytes).extract from_.val i.val).length = i.val - from_.val := by
            rw [List.extract_eq_take_drop, List.length_take, List.length_drop, hbl']; omega
          rw [hl] at this
          exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
        step as ⟨ hil, c, hc ⟩
        have hcv : (sliceBytes bytes)[i.val]! = c.val := by
          rw [sliceBytes_getElem! bytes i.val hil, hc]
        have hext := extract_snoc (sliceBytes bytes) (a := from_.val) h1 (by rw [hbl']; omega)
        split
        · rename_i hc48
          split
          · rename_i hc57
            have hdig : DecimalDigit c.val := ⟨by scalar_tac, by scalar_tac⟩
            have h10 : value.val * 10 ≤ U64.max := by
              have : (10 : Nat) ^ 18 * 10 ≤ U64.max := by simp [U64.max, U64.numBits]
              nlinarith
            step*
            refine ⟨?_, by simp; omega⟩
            refine ⟨by omega, by omega, fun _ => ⟨?_, ?_⟩, fun h => absurd h (by simp)⟩
            · rw [show value1.val = i1.val + i3.val by scalar_tac, show i4.val = i.val + 1 by scalar_tac, hext,
                decimalValue_append, ← hv, hcv]
              have : i3.val = c.val - 48 := by
                have : c.val ≤ 255 := by scalar_tac
                rw [i3_post, UScalar.cast_val_eq, i2_post1]; simp [UScalarTy.numBits]; omega
              rw [this, i1_post]
            · rw [show i4.val = i.val + 1 by scalar_tac, hext]
              intro x hx
              rcases List.mem_append.1 hx with hx | hx
              · exact hd x hx
              · rw [List.mem_singleton.1 hx, hcv]; exact hdig
          · rename_i hc57
            refine ⟨⟨h1, h2, fun h => absurd h (by simp), fun _ => ⟨c.val, ?_, ?_⟩⟩, by simp⟩
            · rw [← hcv]
              have : (sliceBytes bytes).extract from_.val to_.val = (sliceBytes bytes).extract from_.val i.val ++
                  [(sliceBytes bytes)[i.val]!] ++ (sliceBytes bytes).extract (i.val + 1) to_.val := by
                rw [← hext]
                simp only [List.extract_eq_take_drop]
                rw [show to_.val - from_.val = (i.val + 1 - from_.val) + (to_.val - (i.val + 1)) by omega,
                  List.take_add, List.drop_drop, show from_.val + (i.val + 1 - from_.val) = i.val + 1 by omega]
              rw [this]; simp
            · intro hd'; exact hc57 (by have := hd'.2; scalar_tac)
        · rename_i hc48
          refine ⟨⟨h1, h2, fun h => absurd h (by simp), fun _ => ⟨c.val, ?_, ?_⟩⟩, by simp⟩
          · rw [← hcv]
            have : (sliceBytes bytes).extract from_.val to_.val = (sliceBytes bytes).extract from_.val i.val ++
                [(sliceBytes bytes)[i.val]!] ++ (sliceBytes bytes).extract (i.val + 1) to_.val := by
              rw [← hext]
              simp only [List.extract_eq_take_drop]
              rw [show to_.val - from_.val = (i.val + 1 - from_.val) + (to_.val - (i.val + 1)) by omega,
                List.take_add, List.drop_drop, show from_.val + (i.val + 1 - from_.val) = i.val + 1 by omega]
            rw [this]; simp
          · intro hd'; exact hc48 (by have := hd'.1; scalar_tac)
      · rename_i hit
        simp only [WP.spec_ok]
        have : i.val = to_.val := by scalar_tac
        rw [← this]
        exact ⟨h1, le_refl _, fun _ => ⟨hv, hd⟩, fun h => absurd h (by simp)⟩
    · rename_i hok
      simp only [WP.spec_ok]
      have hokf : ok = false := by simpa using hok
      exact ⟨le_trans h1 h2, le_refl _, fun h => absurd h (by simp), fun _ => h4 hokf⟩
  · refine ⟨le_refl _, hft, fun _ => ⟨by simp [decimalValue], by simp⟩, fun h => absurd h (by simp)⟩
  · obtain ⟨_, _, h3, h4⟩ := hinv
    split
    · rename_i hok
      obtain ⟨hv, hd⟩ := h3 hok
      exact ⟨hd, hv⟩
    · rename_i hok
      exact h4 (by simpa using hok)

theorem blobField_length : blobField.length = 6 := by decide

/-- `BatchHeader` as the sequence of checks `parse_batch_header` makes: the
    object id, ` blob `, one to 19 digits after it (so 2 to 20 bytes with the
    LF), a final LF, no leading zero, digits only, and the value. -/
theorem batchHeader_iff (H O : List Nat) (n : Nat) :
    BatchHeader H O n ↔ O <+: H ∧ blobField <+: H.drop O.length ∧ O.length + 6 + 2 ≤ H.length ∧
      H.length - (O.length + 6) ≤ 20 ∧ H[H.length - 1]! = 10 ∧
      (H[O.length + 6]! = 48 → H.length - (O.length + 6) = 2) ∧
      (∀ c ∈ H.extract (O.length + 6) (H.length - 1), DecimalDigit c) ∧
      n = decimalValue (H.extract (O.length + 6) (H.length - 1)) := by
  constructor
  · rintro ⟨ds, rfl, ⟨hne, hdig, hz⟩, h19, rfl⟩
    have hdl : 0 < ds.length := List.length_pos_iff.mpr hne
    have hlen : (O ++ blobField ++ ds ++ [10]).length = O.length + 6 + ds.length + 1 := by
      simp [blobField_length]; omega
    have hext : (O ++ blobField ++ ds ++ [10]).extract (O.length + 6)
        ((O ++ blobField ++ ds ++ [10]).length - 1) = ds := by
      rw [hlen, List.extract_eq_take_drop, show O ++ blobField ++ ds ++ [10] =
        (O ++ blobField) ++ (ds ++ [10]) by simp, List.drop_left' (by simp [blobField_length]),
        show O.length + 6 + ds.length + 1 - 1 - (O.length + 6) = ds.length by omega]
      simp
    rw [hext]
    refine ⟨by simp [List.append_assoc], ?_, by rw [hlen]; omega, by rw [hlen]; omega, ?_, ?_, hdig, rfl⟩
    · rw [show O ++ blobField ++ ds ++ [10] = O ++ (blobField ++ (ds ++ [10])) by simp, List.drop_left]
      exact List.prefix_append _ _
    · rw [hlen, show O.length + 6 + ds.length + 1 - 1 = (O ++ blobField ++ ds).length + 0 by
        simp [blobField_length]; omega]
      rw [getElem!_pos _ _ (by simp [blobField_length])]
      simp [List.getElem_append_right]
    · intro h48
      rw [hlen]
      have hd0 : ds[0]! = 48 := by
        rw [show O ++ blobField ++ ds ++ [10] = (O ++ blobField) ++ (ds ++ [10]) by simp,
          show O.length + 6 = (O ++ blobField).length + 0 by simp [blobField_length]] at h48
        rw [getElem!_pos _ _ (by simp), List.getElem_append_right (by simp),
          List.getElem_append_left (by simp; omega)] at h48
        rw [getElem!_pos ds 0 hdl]
        simpa using h48
      have : ds.head? = some 48 := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hdl, ← getElem!_pos ds 0 hdl, hd0]
      have := hz this
      subst this
      simp
  · rintro ⟨hO, hB, hl, h20, hlf, hz, hdig, rfl⟩
    refine ⟨H.extract (O.length + 6) (H.length - 1), ?_, ⟨?_, hdig, ?_⟩, ?_, rfl⟩
    · obtain ⟨t, rfl⟩ := hO
      simp only [List.drop_left] at hB
      obtain ⟨u, hu⟩ := hB
      subst hu
      have hlen : (O ++ (blobField ++ u)).length = O.length + 6 + u.length := by
        simp [blobField_length]; omega
      rw [hlen] at hlf h20 hl ⊢
      have hu1 : 1 ≤ u.length := by omega
      have hlast : u[u.length - 1]! = 10 := by
        rw [show O.length + 6 + u.length - 1 = (O ++ blobField).length + (u.length - 1) by
          simp [blobField_length]; omega] at hlf
        rw [show O ++ (blobField ++ u) = (O ++ blobField) ++ u by simp, idx_getElem!_append_right] at hlf
        exact hlf
      have hext : (O ++ (blobField ++ u)).extract (O.length + 6) (O.length + 6 + u.length - 1) =
          u.take (u.length - 1) := by
        rw [List.extract_eq_take_drop, show O ++ (blobField ++ u) = (O ++ blobField) ++ u by simp,
          List.drop_left' (by simp [blobField_length]), show O.length + 6 + u.length - 1 - (O.length + 6) =
          u.length - 1 by omega]
      rw [hext]
      have : u = u.take (u.length - 1) ++ [10] := by
        conv_lhs => rw [← List.take_append_drop (u.length - 1) u]
        congr 1
        rw [List.drop_eq_getElem_cons (by omega), ← getElem!_pos u _ (by omega), hlast,
          List.drop_eq_nil_of_le (by omega)]
      conv_lhs => rw [this]
      simp
    · intro h
      have := congrArg List.length h
      simp only [List.extract_eq_take_drop, List.length_take, List.length_drop, List.length_nil] at this
      omega
    · intro hh
      have hpos : O.length + 6 < H.length - 1 := by omega
      have h0 : H[O.length + 6]! = 48 := by
        rw [List.head?_eq_getElem?, List.extract_eq_take_drop, List.getElem?_take,
          if_pos (by omega), List.getElem?_drop, Nat.add_zero] at hh
        exact ((getElem?_eq_some_iff' _ _ 48).mp hh).2
      have h2 := hz h0
      apply List.ext_getElem
      · simp only [List.extract_eq_take_drop, List.length_take, List.length_drop, List.length_singleton]; omega
      · intro k h1 h2'
        have hk : k = 0 := by simp at h2'; omega
        subst hk
        simp only [List.extract_eq_take_drop, List.getElem_take, List.getElem_drop, Nat.add_zero,
          List.getElem_cons_zero]
        rw [← getElem!_pos H _ (by omega), h0]
    · simp only [List.extract_eq_take_drop, List.length_take, List.length_drop]; omega

/-- **Object reply headers.** `parse_batch_header` returns a size exactly
    when the header is Git's reply `<oid> SP blob SP <size> LF` for the
    requested object id with a canonical decimal size of at most 19 digits
    (`BatchHeader`), and that size (unique: `batchHeader_unique`). -/
theorem parse_batch_header_spec (header oid : Slice U8) :
    parse_batch_header header oid ⦃ r => match r with
      | core.option.Option.Some v => BatchHeader (sliceBytes header) (sliceBytes oid) v.val
      | core.option.Option.None => ∀ n, ¬ BatchHeader (sliceBytes header) (sliceBytes oid) n ⦄ := by
  have hHl := sliceBytes_length header
  have hOl := sliceBytes_length oid
  unfold parse_batch_header
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
  step with matches_at_spec as ⟨ b, hb ⟩
  split
  · rename_i hbt
    obtain ⟨-, hO⟩ := hb.mp hbt
    step as ⟨ s, hs ⟩
    step with matches_at_spec as ⟨ b1, hb1 ⟩
    rw [hs, BLOB_FIELD_bytes] at hb1
    have hlenv : oid.len.val = oid.length := by simp
    split
    · rename_i hb1t
      obtain ⟨hle, hB⟩ := hb1.mp hb1t
      rw [hlenv, ← hOl] at hB hle
      have hBl := hB.length_le
      simp only [List.length_drop, blobField_length] at hBl
      have hO' : sliceBytes oid <+: sliceBytes header := by simpa using hO
      step*
      all_goals
        have hd : digits.val = (sliceBytes oid).length + 6 := by rw [digits_post, hlenv, hOl]
        have hn : header.len.val = (sliceBytes header).length := by simp [hHl]
      -- One to 19 digits.
      · intro n hB
        have := ((batchHeader_iff _ _ _).mp hB).2.2.1
        scalar_tac
      · intro n hB
        have := ((batchHeader_iff _ _ _).mp hB).2.2.2.1
        scalar_tac
      -- The final LF.
      · rename_i hx10
        intro n hB
        have h10 := ((batchHeader_iff _ _ _).mp hB).2.2.2.2.1
        simp only [bne_iff_ne, ne_eq] at hx10
        apply hx10
        rw [i3_post2]
        apply UScalar.eq_of_val_eq
        rw [← sliceBytes_getElem! header i2.val (by scalar_tac), show i2.val = (sliceBytes header).length - 1 by
          scalar_tac, h10]; rfl
      -- A leading zero.
      · rename_i hx48 hne2
        intro n hB
        have hz := ((batchHeader_iff _ _ _).mp hB).2.2.2.2.2.1
        have h48 : (sliceBytes header)[(sliceBytes oid).length + 6]! = 48 := by
          rw [← hd, sliceBytes_getElem! header digits.val (by scalar_tac), ← i4_post2, hx48]; rfl
        have := hz h48
        simp only [bne_iff_ne, ne_eq] at hne2
        apply hne2
        apply UScalar.eq_of_val_eq
        simp only [i1_post1, hn, hd]
        simp; omega
      -- The digits: `decimal` decides the rest.
      all_goals
        have hd2 : digits.val ≤ i2.val := by scalar_tac
        have hi2 : i2.val ≤ header.length := by scalar_tac
        have h19 : i2.val - digits.val ≤ 19 := by scalar_tac
        have hi2v : i2.val = (sliceBytes header).length - 1 := by scalar_tac
        have hlf : (sliceBytes header)[(sliceBytes header).length - 1]! = 10 := by
          have := ‹¬(_ != 10#u8) = true›
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
          rw [← hi2v, sliceBytes_getElem! header i2.val (by scalar_tac), ← i3_post2, this]; rfl
        apply WP.spec_mono (decimal_spec header digits i2 hd2 hi2 h19)
        rintro (_ | v) hr
        · intro n hB
          obtain ⟨c, hc, hnd⟩ := hr
          rw [hd, hi2v] at hc
          exact hnd (((batchHeader_iff _ _ _).mp hB).2.2.2.2.2.2.1 c hc)
        · obtain ⟨hdig, hv⟩ := hr
          rw [hd, hi2v] at hdig hv
          dsimp only
          rw [batchHeader_iff]
          refine ⟨hO', hB, by scalar_tac, by scalar_tac, hlf, fun h48 => ?_, hdig, hv⟩
          first
          | (have := ‹¬(i1 != 2#usize) = true›
             simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
             have := congrArg UScalar.val this
             simp only [i1_post1, hn, hd] at this
             simpa using this)
          | (exfalso
             apply ‹¬_ = 48#u8›
             rw [i4_post2]
             apply UScalar.eq_of_val_eq
             rw [← sliceBytes_getElem! header digits.val (by scalar_tac), hd, h48]; rfl)
    · rename_i hb1t
      simp only [WP.spec_ok]
      intro n hB
      rw [batchHeader_iff] at hB
      apply hb1t
      rw [hb1]
      refine ⟨?_, by rw [hlenv, ← hOl]; exact hB.2.1⟩
      have := hB.2.2.1
      rw [hlenv]; omega
  · rename_i hbt
    simp only [WP.spec_ok]
    intro n hB
    rw [batchHeader_iff] at hB
    exact hbt (hb.mpr ⟨by simp, by simpa using hB.1⟩)

end Transcrypt.V3Verification
