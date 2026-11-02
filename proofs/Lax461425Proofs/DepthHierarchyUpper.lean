import Lax461425.DepthHierarchy
import Lax461425.CircuitsForPatterns
import Lax461425.Forestwidth

/-!
Second assertion of the depth hierarchy theorem: the full `n`-ary tree `T_{Δ,n}` has
`Δ+1`-forestwidth `1`, so `CircuitsForPatterns.exists_circuit` with support size `2` applies.

The tree decomposition has a root with empty bag and one node `w` for every word `w`, with bag
`{w, parent w}`; the parent of the node `w` is the node `dropLast w` (or the root if `w = []`).
-/

namespace Lax461425Proofs.DepthHierarchy

open Lax461425 Lax461425.DepthHierarchy Lax461425.HomomorphismPolynomials Lax461425.Forestwidth
  Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports

section Decomposition

variable (Δ n : ℕ)

/-- Words of length at most `Δ`. -/
abbrev W : Type := {w : List (Fin n) // w.length ≤ Δ}

instance : Finite (W Δ n) := (List.finite_length_le (Fin n) Δ).to_subtype

variable {Δ n}

/-- The word `w` as a vertex of `T_{Δ,n}`. -/
def toV (w : W Δ n) : (fullTree Δ n).A ⊕ (fullTree Δ n).B :=
  if h : Even w.1.length then Sum.inl ⟨w.1, w.2, h⟩
  else Sum.inr ⟨w.1, w.2, Nat.not_even_iff_odd.1 h⟩

/-- The parent word. -/
def par (w : W Δ n) : W Δ n := ⟨w.1.dropLast, (List.length_dropLast (xs := w.1)).trans_le
  ((Nat.sub_le _ _).trans w.2)⟩

lemma toV_even (w : W Δ n) (a : (fullTree Δ n).A) (h : w.1 = a.1) : toV w = Sum.inl a := by
  have he : Even w.1.length := h ▸ a.2.2
  simp only [toV, dif_pos he]
  congr 1
  exact Subtype.ext h

lemma toV_odd (w : W Δ n) (b : (fullTree Δ n).B) (h : w.1 = b.1) : toV w = Sum.inr b := by
  have he : ¬ Even w.1.length := Nat.not_even_iff_odd.2 (h ▸ b.2.2)
  simp only [toV, dif_neg he]
  congr 1
  exact Subtype.ext h

@[simp] lemma toV_A (a : (fullTree Δ n).A) : toV (⟨a.1, a.2.1⟩ : W Δ n) = Sum.inl a :=
  toV_even _ a rfl

@[simp] lemma toV_B (b : (fullTree Δ n).B) : toV (⟨b.1, b.2.1⟩ : W Δ n) = Sum.inr b :=
  toV_odd _ b rfl

lemma toV_injective : Function.Injective (toV (Δ := Δ) (n := n)) := by
  intro w w' h
  by_cases he : Even w.1.length <;> by_cases he' : Even w'.1.length
  · rw [toV_even w ⟨w.1, w.2, he⟩ rfl, toV_even w' ⟨w'.1, w'.2, he'⟩ rfl] at h
    have h2 := Sum.inl.inj h
    exact Subtype.ext (by injection h2)
  · rw [toV_even w ⟨w.1, w.2, he⟩ rfl,
      toV_odd w' ⟨w'.1, w'.2, Nat.not_even_iff_odd.1 he'⟩ rfl] at h
    exact absurd h Sum.inl_ne_inr
  · rw [toV_odd w ⟨w.1, w.2, Nat.not_even_iff_odd.1 he⟩ rfl,
      toV_even w' ⟨w'.1, w'.2, he'⟩ rfl] at h
    exact absurd h Sum.inr_ne_inl
  · rw [toV_odd w ⟨w.1, w.2, Nat.not_even_iff_odd.1 he⟩ rfl,
      toV_odd w' ⟨w'.1, w'.2, Nat.not_even_iff_odd.1 he'⟩ rfl] at h
    have h2 := Sum.inr.inj h
    exact Subtype.ext (by injection h2)

/-- The parent of a node. -/
def parentN : Option (W Δ n) → Option (W Δ n)
  | none => none
  | some w => if w.1 = [] then none else some (par w)

lemma parentN_iterate_none (j : ℕ) : (parentN (Δ := Δ) (n := n))^[j] none = none :=
  Function.iterate_fixed rfl j

lemma parentN_iterate (j : ℕ) : ∀ w : W Δ n, w.1.length < j →
    (parentN (Δ := Δ) (n := n))^[j] (some w) = none := by
  induction j with
  | zero => intro w h; omega
  | succ j ih =>
    intro w h
    rw [Function.iterate_succ_apply]
    by_cases hw : w.1 = []
    · simp [parentN, hw, parentN_iterate_none]
    · simp only [parentN, hw, if_false]
      apply ih
      simp only [par, List.length_dropLast]
      have : 0 < w.1.length := List.length_pos_iff.2 hw
      omega

/-- The bag of a node. -/
noncomputable def bagN : Option (W Δ n) → Finset ((fullTree Δ n).A ⊕ (fullTree Δ n).B)
  | none => ∅
  | some w => {toV w, toV (par w)}

open Classical in
/-- The tree decomposition of `T_{Δ,n}` of depth `Δ + 1` and width `1`. -/
noncomputable def decomp (Δ n : ℕ) : DepthDecomposition (fullTree Δ n) (Δ + 1) 2 where
  Node := Option (W Δ n)
  fintypeNode := Fintype.ofFinite _
  root := none
  parent := parentN
  parent_root := rfl
  depth_le t := by
    cases t with
    | none => exact parentN_iterate_none _
    | some w => exact parentN_iterate _ w (by have := w.2; omega)
  bag := bagN
  bag_root := rfl
  card_bag_le t := by
    cases t with
    | none => simp [bagN]
    | some w => exact (Finset.card_insert_le _ _).trans (by simp [bagN])
  exists_mem_bag v := by
    rcases v with a | b
    · exact ⟨some ⟨a.1, a.2.1⟩, by simp [bagN, toV_A]⟩
    · exact ⟨some ⟨b.1, b.2.1⟩, by simp [bagN, toV_B]⟩
  exists_edge_mem_bag a b h := by
    have h' : (∃ i, b.1 = a.1 ++ [i]) ∨ ∃ i, a.1 = b.1 ++ [i] := by
      by_contra hc
      exact h (by simp only [fullTree]; rw [if_neg hc])
    rcases h' with ⟨i, hi⟩ | ⟨i, hi⟩
    · refine ⟨some ⟨b.1, b.2.1⟩, ?_, ?_⟩
      · have : par (⟨b.1, b.2.1⟩ : W Δ n) = ⟨a.1, a.2.1⟩ := by
          apply Subtype.ext; simp [par, hi]
        simp [bagN, this, toV_A]
      · simp [bagN, toV_B]
    · refine ⟨some ⟨a.1, a.2.1⟩, ?_, ?_⟩
      · simp [bagN, toV_A]
      · have : par (⟨a.1, a.2.1⟩ : W Δ n) = ⟨b.1, b.2.1⟩ := by
          apply Subtype.ext; simp [par, hi]
        simp [bagN, this, toV_B]
  connected v t t' := by
    have key : ∀ t : Option (W Δ n), v ∈ bagN t → v ∉ bagN (parentN t) →
        ∃ w, t = some w ∧ toV w = v := by
      intro t h1 h2
      cases t with
      | none => simp [bagN] at h1
      | some w =>
        simp only [bagN, Finset.mem_insert, Finset.mem_singleton] at h1
        rcases h1 with h1 | h1
        · exact ⟨w, rfl, h1.symm⟩
        · by_cases hw : w.1 = []
          · have : par w = w := Subtype.ext (by simp [par, hw])
            exact ⟨w, rfl, by rw [h1, this]⟩
          · exfalso
            apply h2
            simp [parentN, hw, bagN, h1]
    intro h1 h2 h3 h4
    obtain ⟨w, rfl, hw⟩ := key t h1 h2
    obtain ⟨w', rfl, hw'⟩ := key t' h3 h4
    rw [toV_injective (hw.trans hw'.symm)]

end Decomposition

/--
---
conclusion: Lax461425.DepthHierarchy.exists_circuit
---
The tree `T_{Δ,n}` has a tree decomposition of depth `Δ + 1` with empty root bag and bags of
size `≤ 2` (`decomp`), so `CircuitsForPatterns.exists_circuit` with support size `2` applies.
-/
theorem exists_circuit {K : Type*} [Field K] [CharZero K] {Δ n : ℕ} (hΔ : 1 ≤ Δ)
    (hn : 5 ≤ n) :
    ∃ C : Circuit (Fin n × Fin n) K,
      C.Computes (hom K (fullTree Δ n) n) ∧ C.IsReduced ∧ IsMatrixSymmetric C ∧
        supportDepth C ≤ Δ + 1 ∧ orbitSize C ≤ n ^ 2 := by
  obtain ⟨C, h1, h2, h3, -, h5, h6, -, -⟩ :=
    Lax461425.CircuitsForPatterns.exists_circuit (K := K) (Δ := Δ + 1) (k := 2) (n := n)
      (by omega) le_rfl (by omega) (fullTree Δ n) ⟨decomp Δ n⟩
  exact ⟨C, h1, h2, h3, h5, by simpa using h6⟩

end Lax461425Proofs.DepthHierarchy
