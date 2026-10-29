import Lax461425Proofs.ReducedRigid
import Lax461425Proofs.PatternsInductionSetup
import Lax461425Proofs.PatternsRestrictedDelete

/-!
The base case of `lem:induction`: input gates.

For a gate `g` labelled by a variable `x_{i,j}`, we show (using only `hred`, `hsym`, and the
ambient bound `2 * supportSize C < n`, with no reference to any specific circuit construction)
that `sup(g) = {i, j}` exactly: `{Sum.inl i, Sum.inr j}` is itself a support of `g` (`Extends`
preserves the label up to the renaming, and a reduced circuit's input labels are pairwise
distinct, so if an automorphism fixes `i, j` it must fix `g`), and conversely every bounded
support of `g` must contain `i` on the left and `j` on the right (otherwise a transposition
moving `i` elsewhere, but fixing every other point of the support, would move `g`'s label,
hence `g` itself, contradicting that the support is a support).

We then exhibit the base-case labelled graph: the single edge between the two label vertices,
which is in `𝒯^{0,k}(1,1)` trivially (depth `0`, bag the whole label support, size `2 ≤ k`) and
whose homomorphism polynomial is exactly `X (i, j)`.

Constant gates are handled similarly and more simply: *every* automorphism fixes a constant
gate (its label is preserved by every renaming), so `∅` is a support of it, and its associated
labelled graph is a scalar multiple of `J 0 0` (so `ℓ = r = 0`).
-/

namespace Lax461425Proofs.PatternsInductionBase

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425.HomomorphismPolynomials
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open Lax461425Proofs.PatternsSupportDepth Lax461425Proofs.PatternsInductionSetup
open Lax461425Proofs.PatternsLabelledBasic Lax461425Proofs.PatternsLabelledOps
open Lax461425Proofs.PatternsRestrictedDelete
open scoped Classical

variable {K : Type*} [Field K] {n : ℕ} {C : Circuit (Fin n × Fin n) K}

/-! ### Input gates: `sup(g) = {i, j}` exactly -/

section InputGate

variable (hred : C.IsReduced) {i j : Fin n} {g : C.Gate} (hg : C.label g = GateLabel.var (i, j))

include hred hg in
/-- `{Sum.inl i, Sum.inr j}` is a support of an input gate `x_{i,j}`: an automorphism extending
a renaming that fixes `i, j` must preserve the label `var (i, j)`, and a reduced circuit's input
gates are pairwise distinct by label, so the automorphism must fix `g`. -/
theorem isSupport_input :
    IsSupport C g ({Sum.inl i, Sum.inr j} : Set (Fin n ⊕ Fin n)) := by
  intro γ σ hfix hext
  have hi : γ.1 i = i := by
    have h := hfix (Sum.inl i) (by simp)
    exact Sum.inl_injective h
  have hj : γ.2 j = j := by
    have h := hfix (Sum.inr j) (by simp)
    exact Sum.inr_injective h
  have hlabel : C.label (σ g) = C.label g := by
    rw [hext.1 g, hg]
    show GateLabel.var (actVar γ (i, j)) = GateLabel.var (i, j)
    have : actVar γ (i, j) = (i, j) := by
      show (γ.1 i, γ.2 j) = (i, j); rw [hi, hj]
    rw [this]
  have hinput : (C.label g).IsInput := by rw [hg]; trivial
  exact (hred.1 g (σ g) hinput hlabel.symm).symm

include hg in
/-- Every bounded support of an input gate `x_{i,j}` contains the left point `i`: if `i` were
missing, a transposition swapping `i` with some other point outside the support (which exists
since the support has room to spare) would fix the support pointwise but move the label, hence
the gate. -/
theorem inl_mem_of_isSupport_input (hrig : IsRigid C) {S : Set (Fin n ⊕ Fin n)}
    (hS : IsSupport C g S) (hroom : (leftPart S).ncard + 1 < n) : Sum.inl i ∈ S := by
  by_contra hmem
  have hnotin : i ∉ leftPart S := hmem
  have hcard : (leftPart S ∪ {i} : Set (Fin n)).ncard < n := by
    calc (leftPart S ∪ {i} : Set (Fin n)).ncard
        ≤ (leftPart S).ncard + ({i} : Set (Fin n)).ncard := Set.ncard_union_le _ _
      _ = (leftPart S).ncard + 1 := by rw [Set.ncard_singleton]
      _ < n := hroom
  have hne : (leftPart S ∪ {i} : Set (Fin n)) ≠ Set.univ := by
    intro hcon; rw [hcon] at hcard; simp [Set.ncard_univ] at hcard
  obtain ⟨i', hi'⟩ : ∃ x, x ∉ (leftPart S ∪ {i} : Set (Fin n)) := by
    by_contra hcon
    push_neg at hcon
    exact hne (Set.eq_univ_of_forall hcon)
  simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hi'
  obtain ⟨hi'1, hi'2⟩ := hi'
  set γ : Γ n := (Equiv.swap i i', 1) with hγ
  have hfix : ∀ x ∈ S, actPoint γ x = x := by
    intro x hx
    cases x with
    | inl a =>
        have ha : a ∈ leftPart S := hx
        have ha1 : a ≠ i := fun h => hnotin (h ▸ ha)
        have ha2 : a ≠ i' := fun h => hi'1 (h ▸ ha)
        show Sum.inl (Equiv.swap i i' a) = Sum.inl a
        rw [Equiv.swap_apply_of_ne_of_ne ha1 ha2]
    | inr b => rfl
  have hσ := hS γ (σOf hrig γ) hfix (σOf_extends hrig γ)
  have hveq : actVar γ (i, j) = (i', j) := by
    show (γ.1 i, γ.2 j) = (i', j)
    have hswap : γ.1 i = i' := Equiv.swap_apply_left i i'
    have hsnd : γ.2 j = j := rfl
    rw [hswap, hsnd]
  have h0 : C.label (σOf hrig γ g) = GateLabel.var (i', j) := by
    rw [(σOf_extends hrig γ).1 g, hg]
    show GateLabel.var (actVar γ (i, j)) = GateLabel.var (i', j)
    rw [hveq]
  have hlabel : C.label g = GateLabel.var (i', j) := by rw [← hσ]; exact h0
  have hfinal : (GateLabel.var (i, j) : GateLabel (Fin n × Fin n) K) = GateLabel.var (i', j) := by
    rw [← hg]; exact hlabel
  injection hfinal with heq
  exact hi'2 (congrArg Prod.fst heq).symm

include hg in
/-- Every bounded support of an input gate `x_{i,j}` contains the right point `j`: the mirror of
`inl_mem_of_isSupport_input` on the `B`-side. -/
theorem inr_mem_of_isSupport_input (hrig : IsRigid C) {S : Set (Fin n ⊕ Fin n)}
    (hS : IsSupport C g S) (hroom : (rightPart S).ncard + 1 < n) : Sum.inr j ∈ S := by
  by_contra hmem
  have hnotin : j ∉ rightPart S := hmem
  have hcard : (rightPart S ∪ {j} : Set (Fin n)).ncard < n := by
    calc (rightPart S ∪ {j} : Set (Fin n)).ncard
        ≤ (rightPart S).ncard + ({j} : Set (Fin n)).ncard := Set.ncard_union_le _ _
      _ = (rightPart S).ncard + 1 := by rw [Set.ncard_singleton]
      _ < n := hroom
  have hne : (rightPart S ∪ {j} : Set (Fin n)) ≠ Set.univ := by
    intro hcon; rw [hcon] at hcard; simp [Set.ncard_univ] at hcard
  obtain ⟨j', hj'⟩ : ∃ x, x ∉ (rightPart S ∪ {j} : Set (Fin n)) := by
    by_contra hcon
    push_neg at hcon
    exact hne (Set.eq_univ_of_forall hcon)
  simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hj'
  obtain ⟨hj'1, hj'2⟩ := hj'
  set γ : Γ n := (1, Equiv.swap j j') with hγ
  have hfix : ∀ x ∈ S, actPoint γ x = x := by
    intro x hx
    cases x with
    | inl a => rfl
    | inr b =>
        have hb : b ∈ rightPart S := hx
        have hb1 : b ≠ j := fun h => hnotin (h ▸ hb)
        have hb2 : b ≠ j' := fun h => hj'1 (h ▸ hb)
        show Sum.inr (Equiv.swap j j' b) = Sum.inr b
        rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2]
  have hσ := hS γ (σOf hrig γ) hfix (σOf_extends hrig γ)
  have hveq : actVar γ (i, j) = (i, j') := by
    show (γ.1 i, γ.2 j) = (i, j')
    have hfst : γ.1 i = i := rfl
    have hswap : γ.2 j = j' := Equiv.swap_apply_left j j'
    rw [hfst, hswap]
  have h0 : C.label (σOf hrig γ g) = GateLabel.var (i, j') := by
    rw [(σOf_extends hrig γ).1 g, hg]
    show GateLabel.var (actVar γ (i, j)) = GateLabel.var (i, j')
    rw [hveq]
  have hlabel : C.label g = GateLabel.var (i, j') := by rw [← hσ]; exact h0
  have hfinal : (GateLabel.var (i, j) : GateLabel (Fin n × Fin n) K) = GateLabel.var (i, j') := by
    rw [← hg]; exact hlabel
  injection hfinal with heq
  exact hj'2 (congrArg Prod.snd heq).symm

include hred hg in
/-- **The base case's support fact.** For `k ≥ 1`, `n ≥ 2 * supportSize C + 2` and an input
gate `g` labelled `x_{i,j}`, `supOf hrig hn2 g = {Sum.inl i, Sum.inr j}` exactly. -/
theorem supOf_input (hrig : IsRigid C) (hn2 : 2 * supportSize C < n)
    (hroom : supportSize C + 1 < n) :
    supOf hrig hn2 g = ({Sum.inl i, Sum.inr j} : Set (Fin n ⊕ Fin n)) := by
  -- First: every small support of `g` contains `{i, j}` (room is governed by `supportSize C`).
  have hcontains : ∀ {S : Set (Fin n ⊕ Fin n)}, IsSupport C g S → S.ncard ≤ supportSize C →
      ({Sum.inl i, Sum.inr j} : Set (Fin n ⊕ Fin n)) ⊆ S := by
    intro S hS hSc
    have hL := ncard_leftPart_le S
    have hR := ncard_rightPart_le S
    have hroomL : (leftPart S).ncard + 1 < n := by omega
    have hroomR : (rightPart S).ncard + 1 < n := by omega
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact inl_mem_of_isSupport_input hg hrig hS hroomL
    · rw [hx]
      exact inr_mem_of_isSupport_input hg hrig hS hroomR
  -- `supOf hrig hn2 g` is itself a small support, so it contains `{i, j}`.
  have h1 : ({Sum.inl i, Sum.inr j} : Set (Fin n ⊕ Fin n)) ⊆ supOf hrig hn2 g :=
    hcontains (isSupport_supOf hrig hn2 g) (ncard_supOf_le hrig hn2 g)
  -- `supportSize_spec`'s witness is a small support too, so `{i, j} ⊆` it, giving
  -- `2 ≤ supportSize C`.
  obtain ⟨S0, hS0, hS0c⟩ := supportSize_spec hrig g
  have h2 : ({Sum.inl i, Sum.inr j} : Set (Fin n ⊕ Fin n)) ⊆ S0 := hcontains hS0 hS0c
  have hcard2 : (2 : ℕ) ≤ supportSize C := by
    have hne : (Sum.inl i : Fin n ⊕ Fin n) ≠ Sum.inr j := fun h => by cases h
    have : ({Sum.inl i, Sum.inr j} : Set (Fin n ⊕ Fin n)).ncard = 2 := by
      rw [Set.ncard_insert_of_notMem (by simp [hne]), Set.ncard_singleton]
    calc (2 : ℕ) = ({Sum.inl i, Sum.inr j} : Set (Fin n ⊕ Fin n)).ncard := this.symm
      _ ≤ S0.ncard := Set.ncard_le_ncard h2 (Set.toFinite _)
      _ ≤ supportSize C := hS0c
  -- So `{i, j}` is itself a small support, hence `supOf hrig hn2 g ⊆ {i, j}`.
  have hijcard : ({Sum.inl i, Sum.inr j} : Set (Fin n ⊕ Fin n)).ncard ≤ supportSize C := by
    have hne : (Sum.inl i : Fin n ⊕ Fin n) ≠ Sum.inr j := fun h => by cases h
    rw [Set.ncard_insert_of_notMem (by simp [hne]), Set.ncard_singleton]
    exact hcard2
  have h3 : supOf hrig hn2 g ⊆ ({Sum.inl i, Sum.inr j} : Set (Fin n ⊕ Fin n)) :=
    supOf_subset hrig hn2 g (isSupport_input hred hg) hijcard
  exact Set.Subset.antisymm h3 h1

end InputGate

/-! ### Constant gates: `sup(g) = ∅` -/

section ConstGate

variable {c : K} {g : C.Gate} (hg : C.label g = GateLabel.const c)

include hg in
/-- Every automorphism fixes a constant gate's label (`GateLabel.map` leaves constants
unchanged), so `∅` is (trivially) a support of it. -/
theorem isSupport_const (hred : C.IsReduced) :
    IsSupport C g (∅ : Set (Fin n ⊕ Fin n)) := by
  intro γ σ _hfix hext
  have hlabel : C.label (σ g) = C.label g := by rw [hext.1 g, hg]; rfl
  have hinput : (C.label g).IsInput := by rw [hg]; trivial
  exact (hred.1 g (σ g) hinput hlabel.symm).symm

include hg in
theorem supOf_const (hred : C.IsReduced) (hrig : IsRigid C) (hn2 : 2 * supportSize C < n) :
    supOf hrig hn2 g = (∅ : Set (Fin n ⊕ Fin n)) :=
  Set.subset_empty_iff.mp (supOf_subset hrig hn2 g (isSupport_const hg hred) (by simp))

end ConstGate

/-! ### The base-case labelled graph: a single edge -/

/-- A single-node `RootExactDecomposition` of depth `0`, provided every non-isolated vertex of
`G` is already labelled (so the root bag can simply be `G.labelSupport`) and the label support
has size `≤ k`. -/
theorem inClass_zero_of_subset_labelSupport {ℓ r : ℕ} (G : LabelledPattern ℓ r) (k : ℕ)
    (hcov : ∀ v, ¬ isIsolated G.F v → v ∈ G.labelSupport) (hk : G.labelSupport.card ≤ k) :
    InClass 0 k G := by
  refine ⟨{ Node := Unit
            root := ()
            parent := id
            parent_root := rfl
            depth_le := fun _ => rfl
            bag := fun _ => G.labelSupport
            bag_root := rfl
            card_bag_le := fun _ => hk
            exists_mem_bag := fun v hv => ⟨(), hcov v hv⟩
            exists_edge_mem_bag := fun x y hxy => by
              have hx : ¬ isIsolated G.F (Sum.inl x) := fun h => absurd (h y) hxy
              have hy : ¬ isIsolated G.F (Sum.inr y) := fun h => absurd (h x) hxy
              exact ⟨(), hcov _ hx, hcov _ hy⟩
            connected := fun v t t' _ _ _ _ => by cases t; cases t'; rfl }⟩

/-- The single-edge `(1,1)`-labelled graph: one edge between the two (distinct) label
vertices. -/
noncomputable def edgeGraph : LabelledPattern 1 1 where
  F := { A := Unit, B := Unit, mult := fun _ _ => 1 }
  a := fun _ => ()
  b := fun _ => ()

theorem edgeGraph_cov : ∀ v, ¬ isIsolated edgeGraph.F v → v ∈ edgeGraph.labelSupport := by
  rintro (a | b) hv
  · exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_image.mpr ⟨Sum.inl (0 : Fin 1), Finset.mem_univ _, rfl⟩,
        mem_isolatedSet.not.mpr hv⟩
  · exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_image.mpr ⟨Sum.inr (0 : Fin 1), Finset.mem_univ _, rfl⟩,
        mem_isolatedSet.not.mpr hv⟩

theorem edgeGraph_not_isolated (v : edgeGraph.F.A ⊕ edgeGraph.F.B) : ¬ isIsolated edgeGraph.F v := by
  cases v with
  | inl a => exact fun h => absurd (h ()) one_ne_zero
  | inr b => exact fun h => absurd (h ()) one_ne_zero

theorem edgeGraph_labelSupport_card : edgeGraph.labelSupport.card = 2 := by
  have hinj : Function.Injective edgeGraph.labelVertex := by
    rintro (i | j) (i' | j') h
    · congr 1; exact Subsingleton.elim i i'
    · exact absurd h (by simp [LabelledPattern.labelVertex])
    · exact absurd h (by simp [LabelledPattern.labelVertex])
    · congr 1; exact Subsingleton.elim j j'
  have hcard : (Finset.univ.image edgeGraph.labelVertex).card = 2 := by
    rw [Finset.card_image_of_injective _ hinj]
    decide
  have hle1 : edgeGraph.labelSupport.card ≤ (Finset.univ.image edgeGraph.labelVertex).card :=
    Finset.card_le_card edgeGraph.labelSupport_subset_image
  have hle2 : (Finset.univ.image edgeGraph.labelVertex).card ≤ edgeGraph.labelSupport.card := by
    apply Finset.card_le_card
    intro v hv
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hv
    exact edgeGraph_cov _ (edgeGraph_not_isolated _)
  omega

theorem inClass_edgeGraph (k : ℕ) (hk : 2 ≤ k) : InClass 0 k edgeGraph :=
  inClass_zero_of_subset_labelSupport edgeGraph k edgeGraph_cov
    (by rw [edgeGraph_labelSupport_card]; exact hk)

theorem inClassP_edgeGraph (k : ℕ) (hk : 2 ≤ k) :
    InClassP 0 k (Finset.univ : Finset (Fin 1 ⊕ Fin 1)) edgeGraph :=
  inClassP_univ_of_inClass (inClass_edgeGraph k hk)

/-- The homomorphism polynomial of the single-edge graph is exactly `X (v 0, w 0)`. -/
theorem labelledHom_edgeGraph (n : ℕ) (v w : Fin 1 → Fin n) :
    labelledHom K edgeGraph n v w = MvPolynomial.X (v 0, w 0) := by
  show (∑ hA : Unit → Fin n, ∑ hB : Unit → Fin n,
      if (∀ i : Fin 1, hA () = v i) ∧ (∀ j : Fin 1, hB () = w j) then
        (∏ _x : Unit, ∏ _y : Unit, MvPolynomial.X (hA (), hB ()) ^ (1 : ℕ) :
          MvPolynomial (Fin n × Fin n) K)
      else 0) = MvPolynomial.X (v 0, w 0)
  have hcond : ∀ hA hB : Unit → Fin n,
      ((∀ i : Fin 1, hA () = v i) ∧ (∀ j : Fin 1, hB () = w j)) ↔
        (hA = fun _ => v 0) ∧ (hB = fun _ => w 0) := by
    intro hA hB
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨funext fun _ => h1 0, funext fun _ => h2 0⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun j => ?_⟩
      · rw [h1, Fin.eq_zero i]
      · rw [h2, Fin.eq_zero j]
  simp only [hcond]
  rw [Finset.sum_eq_single (fun _ : Unit => v 0)]
  · rw [Finset.sum_eq_single (fun _ : Unit => w 0)]
    · simp
    · intro hB _ hne; exact if_neg (fun h => hne h.2)
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro hA _ hne
    apply Finset.sum_eq_zero
    intro hB _
    exact if_neg (fun h => hne h.1)
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### Range computations for the pair `{i, j}` -/

theorem leftPart_pair_eq (i j : Fin n) :
    leftPart ({Sum.inl i, Sum.inr j} : Set (Fin n ⊕ Fin n)) = ({i} : Set (Fin n)) := by
  ext x; simp [leftPart]

theorem rightPart_pair_eq (i j : Fin n) :
    rightPart ({Sum.inl i, Sum.inr j} : Set (Fin n ⊕ Fin n)) = ({j} : Set (Fin n)) := by
  ext x; simp [rightPart]

theorem range_const_fin1 {α : Type*} (a : α) : Set.range (fun _ : Fin 1 => a) = ({a} : Set α) := by
  ext x; simp [eq_comm]

/-! ### Assembling the base case -/

/-- **The base case of `lem:induction`, for input gates.** For `k ≥ 2`, `2 * k + 1 ≤ n`, a
reduced matrix-symmetric circuit `C` with `supportSize C ≤ k`, and an input gate `g` labelled
`x_{i,j}`, there is `φ ∈ 𝔗^{0,k}_n(1,1)` (unrestricted, i.e. `P = Finset.univ`) with
`φ (fun _ => i) (fun _ => j) = X (i, j)`, and the pair of constant enumerations `(fun _ => i),
(fun _ => j)` has range exactly `(leftPart (supOf hrig hn2 g), rightPart (supOf hrig hn2 g))`,
matching `lem:induction`'s required shape at `g` (with `sc C g = 0`, since `g` has no
children). -/
theorem exists_phi_input {K : Type*} [Field K] {n k : ℕ} (hk : 2 ≤ k) (hn : 2 * k + 1 ≤ n)
    {C : Circuit (Fin n × Fin n) K} (hred : C.IsReduced) (hsym : IsMatrixSymmetric C)
    (hsize : supportSize C ≤ k) {i j : Fin n} {g : C.Gate}
    (hg : C.label g = GateLabel.var (i, j)) :
    ∃ φ : (Fin 1 → Fin n) → (Fin 1 → Fin n) → MvPolynomial (Fin n × Fin n) K,
      φ ∈ span𝔗P K 0 k n (Finset.univ : Finset (Fin 1 ⊕ Fin 1)) ∧
      φ (fun _ => i) (fun _ => j) = MvPolynomial.X (i, j) ∧
      sc C g = 0 ∧
      (letI hrig := ReducedRigid.isRigid hsym hred
       letI hn2 : 2 * supportSize C < n := by omega
       Set.range (fun _ : Fin 1 => i) = leftPart (supOf hrig hn2 g) ∧
         Set.range (fun _ : Fin 1 => j) = rightPart (supOf hrig hn2 g)) := by
  have hrig : IsRigid C := ReducedRigid.isRigid hsym hred
  have hn2 : 2 * supportSize C < n := by omega
  have hroom : supportSize C + 1 < n := by omega
  have hsup : supOf hrig hn2 g = ({Sum.inl i, Sum.inr j} : Set (Fin n ⊕ Fin n)) :=
    supOf_input hred hg hrig hn2 hroom
  refine ⟨labelledHom K edgeGraph n, ?_, labelledHom_edgeGraph n _ _, ?_, ?_, ?_⟩
  · exact Submodule.subset_span ⟨edgeGraph, inClassP_edgeGraph k hk, rfl⟩
  · have hinput : (C.label g).IsInput := by rw [hg]; trivial
    exact sc_eq_zero_of_isInput hinput
  · rw [hsup, leftPart_pair_eq]; exact range_const_fin1 i
  · rw [hsup, rightPart_pair_eq]; exact range_const_fin1 j

end Lax461425Proofs.PatternsInductionBase
