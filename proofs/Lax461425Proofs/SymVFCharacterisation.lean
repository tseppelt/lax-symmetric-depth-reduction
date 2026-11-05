import Lax461425.SymmetricVFCharacterisation
import Lax461425Proofs.SymVFCharacterisationTreedepth
import Lax461425Proofs.SymVFCharacterisationGlue
import Lax461425Proofs.SymVFCharacterisationSplit
import Lax461425Proofs.PathRefinementBounds
import Lax461425Proofs.CircuitFacts
import Lax461425Proofs.CircuitFamilyFacts
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
The characterisation of `symVF` by homomorphism polynomials of patterns of bounded treedepth.
Large orders use the support depth of symmetric formulas and the bounded-depth
characterisation; small orders use invariance and the spanning theorem. Conversely, the
formulas for single patterns are combined by a scaled-sum glue whose scaling constants are
distinct and fresh, so that every block is fixed by all automorphisms.
-/

namespace Lax461425Proofs.SymVFCharacterisation

open Lax461425.Circuits Lax461425.CircuitProperties Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425.SymmetricFamilies Lax461425.SymmetricClasses Lax461425.HomomorphismPolynomials
open Lax461425.PatternWidths
open SymVFCharacterisationTreedepth SymVFCharacterisationGlue SymVFCharacterisationSplit
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

/-- Orbits are bounded by the number of gates. -/
theorem orbitSize_le_card {n : ℕ} (C : Circuit (Fin n × Fin n) K) :
    orbitSize C ≤ Fintype.card C.Gate := by
  apply Finset.sup_le
  intro g _
  simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card (orbit C g)

/-- The constants occurring in a family of circuits. -/
noncomputable def constantsOf {V : Type*} {m : ℕ} (D : Fin m → Circuit V K) : Finset K :=
  (Finset.univ : Finset (Σ j, (D j).Gate)).biUnion fun x =>
    match (D x.1).label x.2 with
    | .const c => {c}
    | _ => ∅

theorem mem_constantsOf {V : Type*} {m : ℕ} (D : Fin m → Circuit V K) (j : Fin m)
    (y : (D j).Gate) {c : K} (h : (D j).label y = .const c) : c ∈ constantsOf D := by
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨j, y⟩, Finset.mem_univ _, ?_⟩
  simp only [h, Finset.mem_singleton]

/-- A linear combination of homomorphism polynomials of patterns of treedepth at most `t` has a
matrix-symmetric formula of orbit size at most `n ^ (t + 2)`. -/
theorem exists_formula_of_mem_span {n t : ℕ} (hn : 1 ≤ n) {p : MatrixPolynomial n K}
    (hp : p ∈ Submodule.span K {q | ∃ F : Pattern, TreedepthLE t F ∧ hom K F n = q}) :
    ∃ C : Circuit (Fin n × Fin n) K,
      C.Computes p ∧ IsFormula C ∧ IsMatrixSymmetric C ∧ orbitSize C ≤ n ^ (t + 2) := by
  obtain ⟨m, c, g, hsum⟩ := Submodule.mem_span_set'.mp hp
  have hD : ∀ i, ∃ C : Circuit (Fin n × Fin n) K, C.Computes (g i : MatrixPolynomial n K) ∧
      IsFormula C ∧ IsMatrixSymmetric C ∧ orbitSize C ≤ n ^ (t + 2) := by
    intro i
    obtain ⟨F, hF, hq⟩ := (g i).2
    obtain ⟨C, h1, h2, h3, h4⟩ := Lax461425.FormulasForPatterns.exists_formula (K := K) hn F hF
    exact ⟨C, hq ▸ h1, h2, h3, h4⟩
  choose D hDc hDf hDs hDo using hD
  obtain ⟨a, hgood1, hgood2⟩ := exists_good (constantsOf D) m c
  let idx : Fin (m + m) → Fin m := fun k => (finSumFinEquiv.symm k).elim id id
  let val : Fin m ⊕ Fin m → K := Sum.elim a (fun i => c i - a i)
  let D' : Fin (m + m) → Circuit (Fin n × Fin n) K := fun k => D (idx k)
  let f' : Fin (m + m) → K := fun k => val (finSumFinEquiv.symm k)
  have hvalinj : Function.Injective val := by
    rintro (i | i) (j | j) h <;> simp only [val, Sum.elim_inl, Sum.elim_inr] at h
    · by_contra hij
      exact (hgood2 i j (fun e => hij (by rw [e]))).1 h
    · by_contra
      by_cases hij : i = j
      · subst hij; exact (hgood1 i).2.2 h
      · exact (hgood2 i j hij).2.2 h
    · by_contra
      by_cases hij : j = i
      · subst hij; exact (hgood1 j).2.2 h.symm
      · exact (hgood2 j i hij).2.2 h.symm
    · by_contra hij
      exact (hgood2 i j (fun e => hij (by rw [e]))).2.1 h
  have hvalS : ∀ x, val x ∉ constantsOf D := by
    rintro (i | i)
    · exact (hgood1 i).1
    · exact (hgood1 i).2.1
  have hinj : Function.Injective f' := hvalinj.comp finSumFinEquiv.symm.injective
  have hfresh : ∀ i j (y : (D' j).Gate), (D' j).label y ≠ .const (f' i) := by
    intro i j y h
    exact hvalS _ (mem_constantsOf D (idx j) y h)
  refine ⟨Lax461425Proofs.glueCircuit D' f', ?_, glue_isFormula D' f' (fun k => hDf _),
    glue_isMatrixSymmetric D' f' (fun k => hDs _),
    glue_orbitSize_le D' f' hinj hfresh _ (Nat.one_le_pow _ _ hn) (fun k => hDo _)⟩
  have hc := Lax461425Proofs.glueCircuit_computes D' f'
    (p := fun k => (g (idx k) : MatrixPolynomial n K)) (fun k => hDc _)
  convert hc using 1
  rw [← hsum, Fin.sum_univ_add]
  simp only [f', idx, val, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Sum.elim_inl, Sum.elim_inr, id]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← add_smul, add_sub_cancel]

/-- Families spanned by bounded-treedepth homomorphism polynomials are in `symVF`. -/
theorem inSymVF_of_span (f : MatrixFamily K) (t : ℕ)
    (hf : ∀ n, f n ∈ Submodule.span K {q | ∃ F : Pattern, TreedepthLE t F ∧ hom K F n = q}) :
    InSymVF f := by
  refine ⟨fun n => (n + 1) ^ (t + 2), ⟨1, t + 2, fun n => by simp⟩, ?_⟩
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨CircuitConstants.constant _ ((f 0).coeff 0), ?_, ?_, ?_, ?_⟩
    · rw [MvPolynomial.eq_C_of_isEmpty (f 0)]
      simpa using CircuitFacts.constant_computes (V := Fin 0 × Fin 0) ((f 0).coeff 0)
    · exact fun γ => ⟨Equiv.refl _, CircuitFacts.constant_extends _ _⟩
    · refine (orbitSize_le_card _).trans ?_
      change Fintype.card Unit ≤ _
      simp
    · exact CircuitFamilyFacts.constant_isFormula _
  · obtain ⟨C, h1, h2, h3, h4⟩ := exists_formula_of_mem_span (K := K) hn (hf n)
    exact ⟨C, h1, h3, h4.trans (Nat.pow_le_pow_left (by omega) _), h2⟩

omit [CharZero K] in
/-- Every pattern has treedepth at most `2n` if each side has at most `n` vertices. -/
theorem span_small_le {n t : ℕ} (htn : 2 * n ≤ t) (p : MatrixPolynomial n K)
    (hp : p ∈ Submodule.span K {q | ∃ F : Pattern,
      Fintype.card F.A ≤ n ∧ Fintype.card F.B ≤ n ∧ hom K F n = q}) :
    p ∈ Submodule.span K {q | ∃ F : Pattern, TreedepthLE t F ∧ hom K F n = q} := by
  refine Submodule.span_mono ?_ hp
  rintro q ⟨F, hA, hB, rfl⟩
  exact ⟨F, treedepthLE_mono (treedepthLE_card F) (by omega), rfl⟩

/-- The empty pattern. -/
def emptyPattern : Pattern := ⟨PEmpty, PEmpty, fun _ _ => 0⟩

theorem hom_emptyPattern (n : ℕ) : hom K emptyPattern n = 1 := by
  haveI : IsEmpty emptyPattern.A := (inferInstance : IsEmpty PEmpty)
  haveI : IsEmpty emptyPattern.B := (inferInstance : IsEmpty PEmpty)
  have h1 : (Finset.univ : Finset (emptyPattern.A → Fin n)).card = 1 := by
    rw [Finset.card_univ, Fintype.card_eq_one_iff]
    exact ⟨fun x => isEmptyElim x, fun g => funext fun x => isEmptyElim x⟩
  have h2 : (Finset.univ : Finset (emptyPattern.B → Fin n)).card = 1 := by
    rw [Finset.card_univ, Fintype.card_eq_one_iff]
    exact ⟨fun x => isEmptyElim x, fun g => funext fun x => isEmptyElim x⟩
  simp [hom, h1, h2]

theorem mem_span_zero (t : ℕ) (p : MatrixPolynomial 0 K) :
    p ∈ Submodule.span K {q | ∃ F : Pattern, TreedepthLE t F ∧ hom K F 0 = q} := by
  rw [MvPolynomial.eq_C_of_isEmpty p, ← mul_one (MvPolynomial.C _), ← MvPolynomial.smul_eq_C_mul,
    ← hom_emptyPattern (K := K) 0]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨emptyPattern, treedepthLE_mono (treedepthLE_card _) ?_, rfl⟩
  have hA : Fintype.card emptyPattern.A = 0 :=
    Fintype.card_eq_zero_iff.mpr (inferInstance : IsEmpty PEmpty)
  have hB : Fintype.card emptyPattern.B = 0 :=
    Fintype.card_eq_zero_iff.mpr (inferInstance : IsEmpty PEmpty)
  omega

/-- Families in `symVF` are spanned by homomorphism polynomials of bounded treedepth. -/
theorem span_of_inSymVF (f : MatrixFamily K) (hf : InSymVF f) :
    ∃ t : ℕ, ∀ n,
      f n ∈ Submodule.span K {q | ∃ F : Pattern, TreedepthLE t F ∧ hom K F n = q} := by
  obtain ⟨b, ⟨c, d, hb⟩, hf⟩ := hf
  let κ := d + 3
  let N := max (max 20 (3 * κ + 2 * (κ - 1) + 1))
    (max (d + 3) (c * 2 ^ d * (d + 3) ^ (d + 3) + 1))
  let t0 := (κ - 1 - 1 + 1) * (2 * κ)
  refine ⟨t0 + 2 * N, fun n => ?_⟩
  obtain ⟨C, hp, hsym, horb, hform⟩ := hf n
  by_cases hN : N ≤ n
  · have hn20 : 20 ≤ n := (Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans hN)
    have hlarge : 3 * κ + 2 * (κ - 1) + 1 ≤ n :=
      (Nat.le_max_right _ _).trans ((Nat.le_max_left _ _).trans hN)
    have hchoose :=
      PathRefinementBounds.polynomial_lt_choose c d n ((Nat.le_max_right _ _).trans hN)
    have horb' : orbitSize C < n.choose κ := horb.trans_lt ((hb n).trans_lt hchoose)
    obtain ⟨C', hp', hred, hsym', hsize, hdepth⟩ :=
      Lax461425.FormulaSupportDepth.exists_reduced hn20 (by omega) C hform hsym horb' hp
    have hspan := (Lax461425.BoundedDepthCharacterisation.characterisation (K := K)
      (Δ := 2 * κ) (k := κ - 1) (n := n) (by omega) (by omega) (by omega) (f n)).mp
      ⟨C', hp', hred, hsym', hsize, hdepth⟩
    refine Submodule.span_mono ?_ hspan
    rintro q ⟨F, hF, rfl⟩
    exact ⟨F, treedepthLE_mono
      (Lax461425.TreedepthForestwidth.treedepthLE_of_forestwidthLE hF) (by omega), rfl⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact mem_span_zero _ _
    · have hinv : MatrixInvariant (f n) := by
        intro γ
        obtain ⟨σ, hσ⟩ := hsym γ
        exact CircuitFacts.rename_eq_of_computes_of_extends hp hσ
      exact span_small_le (by omega) _
        (Lax461425.HomomorphismSpanning.invariant_mem_span_hom hn (f n) hinv)

/--
---
conclusion: Lax461425.SymmetricVFCharacterisation.characterisation
---
`symVF` consists of the families spanned by homomorphism polynomials of patterns of bounded
treedepth.
-/
theorem characterisation {K : Type*} [Field K] [CharZero K] (f : MatrixFamily K) :
    InSymVF f ↔ ∃ t : ℕ, ∀ n,
      f n ∈ Submodule.span K {q | ∃ F : Pattern, TreedepthLE t F ∧ hom K F n = q} :=
  ⟨span_of_inSymVF f, fun ⟨t, ht⟩ => inSymVF_of_span f t ht⟩

end Lax461425Proofs.SymVFCharacterisation
