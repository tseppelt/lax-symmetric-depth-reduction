import Lax461425Proofs.RigidWeight

/-!
A generic fact about embedding a *reduced* circuit `D` as an isolated component inside a
bigger circuit `E`: if `ι : D.Gate → E.Gate` is injective, reproduces `D`'s labels and wires
exactly on its image, and every wire out of an image gate lands back in the image (no wire
"leaks" out of the embedded block), then distinct gates of `D` can never become identified by
`E`'s equivalence relation (`RigidEquiv.Equiv`), no matter what else `E` contains or how it is
wired up elsewhere. This is what lets us compute `minSupport` of an embedded block's gates,
after rigidifying `E`, directly from `D`'s own (already known) support structure, with no need
to worry about `E`'s rigidification merging an embedded block's gates with anything else.
-/

namespace Lax461425Proofs

open Lax461425.Circuits RigidHeight RigidEquiv RigidWeight

open scoped Classical

variable {K : Type*} {n : ℕ} {D E : Circuit (Fin n × Fin n) K}

/-- No actual wire leaves the embedded image of `ι`: for `h' ∉ range ι`, `ι y` never wires into
`h'`. -/
theorem embed_wire_eq_zero_of_not_mem_range (ι : D.Gate → E.Gate)
    (hconf : ∀ y h', 0 < E.wire (ι y) h' → ∃ h, h' = ι h) {y : D.Gate} {h' : E.Gate}
    (hh' : ¬ ∃ h, h' = ι h) : E.wire (ι y) h' = 0 := by
  by_contra hne
  exact hh' (hconf y h' (Nat.pos_of_ne_zero hne))

/-- Reindexing a sum over `E.Gate` that vanishes off the image of `ι` to a sum over `D.Gate`. -/
theorem embed_reindex_sum (ι : D.Gate → E.Gate) (hι : Function.Injective ι) (f : E.Gate → ℕ)
    (hf : ∀ h', ¬ (∃ h, h' = ι h) → f h' = 0) :
    ∑ h' : E.Gate, f h' = ∑ h : D.Gate, f (ι h) := by
  have hstep : ∑ h' : E.Gate, f h' = ∑ h' ∈ (Finset.univ : Finset D.Gate).image ι, f h' := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    refine hf x (fun ⟨h, he⟩ => hx ?_)
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨h, he.symm⟩
  rw [hstep, Finset.sum_image (fun x _ y _ hxy => hι hxy)]

/-- `ι` preserves height exactly: `height E (ι y) = height D y`, in the `≤` direction. -/
theorem embed_height_le (ι : D.Gate → E.Gate) (hwire : ∀ y h, E.wire (ι y) (ι h) = D.wire y h)
    (y : D.Gate) : height D y ≤ height E (ι y) := by
  induction y using (wellFounded_child D).induction with
  | _ y ih =>
    rw [height_eq D y]
    apply Finset.sup_le
    intro h _
    by_cases hc : Child D y h
    · rw [dif_pos hc]
      have hcE : Child E (ι y) (ι h) := by
        show 0 < E.wire (ι y) (ι h)
        rw [hwire]; exact hc
      have h1 := height_child_lt E hcE
      have h2 := ih h hc
      omega
    · rw [dif_neg hc]; exact Nat.zero_le _

/-- `ι` preserves height exactly: `height E (ι y) = height D y`, in the `≥` direction. -/
theorem embed_height_ge (ι : D.Gate → E.Gate)
    (hconf : ∀ y h', 0 < E.wire (ι y) h' → ∃ h, h' = ι h)
    (hwire : ∀ y h, E.wire (ι y) (ι h) = D.wire y h) (y : D.Gate) :
    height E (ι y) ≤ height D y := by
  induction y using (wellFounded_child D).induction with
  | _ y ih =>
    rw [height_eq E (ι y)]
    apply Finset.sup_le
    intro h' _
    by_cases hc : Child E (ι y) h'
    · rw [dif_pos hc]
      obtain ⟨h, rfl⟩ := hconf y h' hc
      have hcD : Child D y h := by
        show 0 < D.wire y h
        rw [← hwire]; exact hc
      have h1 := ih h hcD
      have h2 := height_child_lt D hcD
      omega
    · rw [dif_neg hc]; exact Nat.zero_le _

/-- **`ι` preserves height exactly.** -/
theorem embed_height_eq (ι : D.Gate → E.Gate)
    (hconf : ∀ y h', 0 < E.wire (ι y) h' → ∃ h, h' = ι h)
    (hwire : ∀ y h, E.wire (ι y) (ι h) = D.wire y h) (y : D.Gate) :
    height E (ι y) = height D y :=
  le_antisymm (embed_height_ge ι hconf hwire y) (embed_height_le ι hwire y)

/-- `D`'s own `wire` function reconstructs `E`'s aggregated sum over the (level-`k`) class of
`ι h0`, when sourced at an embedded gate `ι y`, provided `height D h0 ≤ k`. -/
theorem embed_key_sum (ι : D.Gate → E.Gate) (hι : Function.Injective ι)
    (hconf : ∀ y h', 0 < E.wire (ι y) h' → ∃ h, h' = ι h)
    (hwire : ∀ y h, E.wire (ι y) (ι h) = D.wire y h) {k : ℕ}
    (ihk : ∀ y1 y2 : D.Gate, EquivRel E k (ι y1) (ι y2) → y1 = y2)
    (y h0 : D.Gate) (hh0 : height D h0 ≤ k) :
    (∑ h' : E.Gate, if EquivRel E k h' (ι h0) then E.wire (ι y) h' else 0) = D.wire y h0 := by
  have hf : ∀ h', ¬ (∃ h, h' = ι h) →
      (if EquivRel E k h' (ι h0) then E.wire (ι y) h' else 0) = 0 := by
    intro h' hh'
    rw [embed_wire_eq_zero_of_not_mem_range ι hconf hh']
    split_ifs <;> rfl
  rw [embed_reindex_sum ι hι _ hf]
  have hstep : ∀ h : D.Gate,
      (if EquivRel E k (ι h) (ι h0) then E.wire (ι y) (ι h) else 0) =
        (if EquivRel E k (ι h) (ι h0) then D.wire y h else 0) := by
    intro h
    split_ifs with hcase
    · rw [hwire]
    · rfl
  rw [Finset.sum_congr rfl (fun h _ => hstep h)]
  have hheightk : height E (ι h0) ≤ k := by rw [embed_height_eq ι hconf hwire]; exact hh0
  have hrefl : EquivRel E k (ι h0) (ι h0) :=
    equivRel_mono E hheightk (equivRel_refl_of_height E (height E (ι h0)) (ι h0) rfl)
  have hsingle : (∑ h : D.Gate, if EquivRel E k (ι h) (ι h0) then D.wire y h else 0) =
      (if EquivRel E k (ι h0) (ι h0) then D.wire y h0 else 0) :=
    Finset.sum_eq_single h0 (fun h _ hne => if_neg (fun hc => hne (ihk h h0 hc)))
      (fun hmem => absurd (Finset.mem_univ h0) hmem)
  rw [hsingle, if_pos hrefl]

/-- If `D` is reduced, a gate of height `0` has no outgoing wires at all, so it trivially
agrees (via `D.IsReduced`) with any other height-`0` gate of the same label. -/
theorem reduced_eq_of_label_wire (hred : D.IsReduced) {y1 y2 : D.Gate}
    (hl : D.label y1 = D.label y2) (hw : D.wire y1 = D.wire y2) : y1 = y2 := by
  by_cases hin : (D.label y1).IsInput
  · exact hred.1 y1 y2 hin hl
  · exact hred.2 y1 y2 hin hl hw

theorem wire_eq_zero_of_height_zero {y : D.Gate} (hy : height D y = 0) : D.wire y = 0 := by
  funext h
  by_contra hne
  have hc : Child D y h := Nat.pos_of_ne_zero hne
  have := height_child_lt D hc
  omega

/-- **The key lemma.** If `D` is reduced and embedded as an isolated block of `E` via `ι`
(injective, label- and wire-preserving on its image, with no wire leaving the image), then
`E`'s equivalence relation, restricted to the image of `ι`, is as fine as possible: it never
identifies two distinct gates of `D`. -/
theorem embed_equivRel_eq (ι : D.Gate → E.Gate) (hι : Function.Injective ι)
    (hlabel : ∀ y, E.label (ι y) = D.label y)
    (hconf : ∀ y h', 0 < E.wire (ι y) h' → ∃ h, h' = ι h)
    (hwire : ∀ y h, E.wire (ι y) (ι h) = D.wire y h) (hred : D.IsReduced) :
    ∀ k : ℕ, ∀ y1 y2 : D.Gate, EquivRel E k (ι y1) (ι y2) → y1 = y2 := by
  intro k
  induction k with
  | zero =>
      intro y1 y2 h
      obtain ⟨hl, hh1, hh2⟩ := h
      have hl' : D.label y1 = D.label y2 := by
        have := hl
        rwa [hlabel, hlabel] at this
      have hh1' : height D y1 = 0 := by rw [← embed_height_eq ι hconf hwire]; exact hh1
      have hh2' : height D y2 = 0 := by rw [← embed_height_eq ι hconf hwire]; exact hh2
      exact reduced_eq_of_label_wire hred hl'
        (by rw [wire_eq_zero_of_height_zero hh1', wire_eq_zero_of_height_zero hh2'])
  | succ k ih =>
      intro y1 y2 h
      rcases h with h | h
      · exact ih y1 y2 h
      · obtain ⟨hl, hh1, hh2, hcond⟩ := h
        have hl' : D.label y1 = D.label y2 := by
          have := hl
          rwa [hlabel, hlabel] at this
        have hh1' : height D y1 = k + 1 := by rw [← embed_height_eq ι hconf hwire]; exact hh1
        have hh2' : height D y2 = k + 1 := by rw [← embed_height_eq ι hconf hwire]; exact hh2
        have hw : D.wire y1 = D.wire y2 := by
          funext h0
          by_cases hh0 : height D h0 ≤ k
          · have hA := embed_key_sum ι hι hconf hwire ih y1 h0 hh0
            have hB := embed_key_sum ι hι hconf hwire ih y2 h0 hh0
            rw [← hA, ← hB]
            exact hcond (ι h0) (by rw [embed_height_eq ι hconf hwire]; exact hh0)
          · push Not at hh0
            have hz1 : D.wire y1 h0 = 0 := by
              by_contra hne
              have : Child D y1 h0 := Nat.pos_of_ne_zero hne
              have := height_child_lt D this
              omega
            have hz2 : D.wire y2 h0 = 0 := by
              by_contra hne
              have : Child D y2 h0 := Nat.pos_of_ne_zero hne
              have := height_child_lt D this
              omega
            rw [hz1, hz2]
        exact reduced_eq_of_label_wire hred hl' hw

/-- **The key lemma, specialised to `Equiv`.** -/
theorem embed_equiv_eq (ι : D.Gate → E.Gate) (hι : Function.Injective ι)
    (hlabel : ∀ y, E.label (ι y) = D.label y)
    (hconf : ∀ y h', 0 < E.wire (ι y) h' → ∃ h, h' = ι h)
    (hwire : ∀ y h, E.wire (ι y) (ι h) = D.wire y h) (hred : D.IsReduced)
    {y1 y2 : D.Gate} (h : Equiv E (ι y1) (ι y2)) : y1 = y2 :=
  embed_equivRel_eq ι hι hlabel hconf hwire hred (height E (ι y1)) y1 y2 h

end Lax461425Proofs
