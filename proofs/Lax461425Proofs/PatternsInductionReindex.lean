import Lax461425Proofs.PatternsInductionSetup
import Lax461425Proofs.PatternsLabelledOps
import Lax461425Proofs.PatternsRestrictedMono
import Lax461425Proofs.PatternsRestrictedDelete
import Mathlib.Data.Fintype.BigOperators

/-!
A general **reindexing lemma** for `lem:induction`'s internal-gate case: given a labelled graph
`G` (or, at the span level, any `φ ∈ 𝔗^{Δ,k}_{n}(ℓ₀,r₀)`) and injective embeddings `ι : Fin ℓ₀ ↪
Fin ℓ₁`, `κ : Fin r₀ ↪ Fin r₁`, we produce a labelled graph `padGraph G ι κ` (resp.
`φ ∈ 𝔗^{Δ,k}_n(ℓ₁,r₁)`) at the larger arity, with the *same* depth bound `Δ` (no increase!),
whose homomorphism polynomial at `(v, w)` is exactly the original one evaluated at
`(v ∘ ι, w ∘ κ)`.

Construction: `padGraph G ι κ` adds one fresh, genuinely isolated vertex for every label
position of `Fin ℓ₁` (resp. `Fin r₁`) *not* hit by `ι` (resp. `κ`), and otherwise routes the
label at position `p = ι i` to the very same (old) vertex that carried label `i` in `G`. Since
the fresh vertices are isolated, they never affect `labelSupport`/`InClass` (the same
root-exact decomposition witnesses `InClass Δ k (padGraph G ι κ)` as witnessed `InClass Δ k G`,
via `embPad`-pushed bags), and the defining sum of `labelledHom` over the fresh vertices'
images collapses to the single term forced by `v`/`w` (so no sum ever actually appears: the
polynomial identity is a plain equality, not an identity-after-summing as in
`PatternsRestrictedDelete`'s `labelledHom_restrict_eq_sum`).
-/

namespace Lax461425Proofs.PatternsInductionReindex

open Lax461425.HomomorphismPolynomials Lax461425Proofs.PatternsLabelledBasic
open Lax461425Proofs.PatternsLabelledOps Lax461425Proofs.PatternsRestrictedMono
open Lax461425Proofs.PatternsRestrictedDelete
open scoped Classical

set_option maxHeartbeats 4000000

/-! ### A generic sum-splitting helper -/

/-- Summing over all functions out of a sum type is the same as the double sum over the two
sides' independent function choices, recombined via `Sum.elim`. The reindexing lemma's proof
uses this to split the "vertex colouring" sums defining `labelledHom (padGraph ⋯)` into the
part belonging to the original graph `G` and the part belonging to the freshly added isolated
vertices. -/
theorem sum_sumArrow {α β γ M : Type*} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]
    [Fintype γ] [AddCommMonoid M] (f : (α ⊕ β → γ) → M) :
    ∑ h : α ⊕ β → γ, f h = ∑ h0 : α → γ, ∑ h1 : β → γ, f (Sum.elim h0 h1) := by
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow α β γ) f
    (fun p => f (Sum.elim p.1 p.2)) (fun x => ?_)
  congr 1
  funext z
  cases z with
  | inl a => exact (Equiv.sumArrowEquivProdArrow_apply_fst x a).symm
  | inr b => exact (Equiv.sumArrowEquivProdArrow_apply_snd x b).symm

/-! ### `padGraph`: padding a labelled graph's label positions along injections -/

variable {ℓ₀ r₀ ℓ₁ r₁ : ℕ}

/-- The `A`-side labelling of `padGraph`: position `ι i` is routed to the old vertex `G.a i`;
every position outside the range of `ι` gets its own fresh (isolated) vertex. -/
noncomputable def padA (G : LabelledPattern ℓ₀ r₀) (ι : Fin ℓ₀ ↪ Fin ℓ₁) :
    Fin ℓ₁ → G.F.A ⊕ ↥(Set.range (⇑ι))ᶜ := fun p =>
  if h : p ∈ Set.range (⇑ι) then
    Sum.inl (G.a ((Equiv.ofInjective (⇑ι) ι.injective).symm ⟨p, h⟩))
  else Sum.inr ⟨p, h⟩

/-- The `B`-side analogue of `padA`. -/
noncomputable def padB (G : LabelledPattern ℓ₀ r₀) (κ : Fin r₀ ↪ Fin r₁) :
    Fin r₁ → G.F.B ⊕ ↥(Set.range (⇑κ))ᶜ := fun p =>
  if h : p ∈ Set.range (⇑κ) then
    Sum.inl (G.b ((Equiv.ofInjective (⇑κ) κ.injective).symm ⟨p, h⟩))
  else Sum.inr ⟨p, h⟩

theorem padA_apply_ι (G : LabelledPattern ℓ₀ r₀) (ι : Fin ℓ₀ ↪ Fin ℓ₁) (i : Fin ℓ₀) :
    padA G ι (ι i) = Sum.inl (G.a i) := by
  unfold padA
  rw [dif_pos (Set.mem_range_self i)]
  have hi : (Equiv.ofInjective (⇑ι) ι.injective).symm ⟨ι i, Set.mem_range_self i⟩ = i := by
    apply (Equiv.ofInjective (⇑ι) ι.injective).injective
    rw [Equiv.apply_symm_apply]
    rfl
  rw [hi]

theorem padA_apply_of_notMem (G : LabelledPattern ℓ₀ r₀) (ι : Fin ℓ₀ ↪ Fin ℓ₁) {p : Fin ℓ₁}
    (h : p ∉ Set.range (⇑ι)) : padA G ι p = Sum.inr ⟨p, h⟩ := by
  unfold padA
  rw [dif_neg h]

theorem padB_apply_κ (G : LabelledPattern ℓ₀ r₀) (κ : Fin r₀ ↪ Fin r₁) (j : Fin r₀) :
    padB G κ (κ j) = Sum.inl (G.b j) := by
  unfold padB
  rw [dif_pos (Set.mem_range_self j)]
  have hj : (Equiv.ofInjective (⇑κ) κ.injective).symm ⟨κ j, Set.mem_range_self j⟩ = j := by
    apply (Equiv.ofInjective (⇑κ) κ.injective).injective
    rw [Equiv.apply_symm_apply]
    rfl
  rw [hj]

theorem padB_apply_of_notMem (G : LabelledPattern ℓ₀ r₀) (κ : Fin r₀ ↪ Fin r₁) {p : Fin r₁}
    (h : p ∉ Set.range (⇑κ)) : padB G κ p = Sum.inr ⟨p, h⟩ := by
  unfold padB
  rw [dif_neg h]

/-- **`padGraph`**: `G`, with its `ℓ₀, r₀` label positions "spread out" along `ι, κ` into
`ℓ₁, r₁` positions, every uncovered position getting a fresh isolated vertex. The underlying
pattern is unchanged on `G`'s own vertices (no new edges), so `padGraph` neither increases
`labelSupport` beyond `G`'s own (up to the embedding `embPad`) nor requires any change to a
witnessing root-exact decomposition. -/
noncomputable def padGraph (G : LabelledPattern ℓ₀ r₀) (ι : Fin ℓ₀ ↪ Fin ℓ₁)
    (κ : Fin r₀ ↪ Fin r₁) : LabelledPattern ℓ₁ r₁ where
  F := { A := G.F.A ⊕ ↥(Set.range (⇑ι))ᶜ
         B := G.F.B ⊕ ↥(Set.range (⇑κ))ᶜ
         mult := fun x y => Sum.elim (fun x0 => Sum.elim (G.F.mult x0) (fun _ => 0))
           (fun _ => fun _ => 0) x y }
  a := padA G ι
  b := padB G κ

/-- The natural embedding of `G`'s vertices into `padGraph G ι κ`'s vertices. -/
def embPad (G : LabelledPattern ℓ₀ r₀) (ι : Fin ℓ₀ ↪ Fin ℓ₁) (κ : Fin r₀ ↪ Fin r₁) :
    G.F.A ⊕ G.F.B → (padGraph G ι κ).F.A ⊕ (padGraph G ι κ).F.B := Sum.map Sum.inl Sum.inl

theorem embPad_injective (G : LabelledPattern ℓ₀ r₀) (ι : Fin ℓ₀ ↪ Fin ℓ₁) (κ : Fin r₀ ↪ Fin r₁) :
    Function.Injective (embPad G ι κ) := by
  intro a b hab
  cases a with
  | inl x0 => cases b with
    | inl x0' => exact congrArg Sum.inl (Sum.inl_injective (Sum.inl_injective hab))
    | inr y0' => exact absurd hab Sum.inl_ne_inr
  | inr y0 => cases b with
    | inl x0' => exact absurd hab.symm Sum.inl_ne_inr
    | inr y0' => exact congrArg Sum.inr (Sum.inl_injective (Sum.inr_injective hab))

theorem isIsolated_embPad_iff (G : LabelledPattern ℓ₀ r₀) (ι : Fin ℓ₀ ↪ Fin ℓ₁)
    (κ : Fin r₀ ↪ Fin r₁) {w : G.F.A ⊕ G.F.B} :
    isIsolated (padGraph G ι κ).F (embPad G ι κ w) ↔ isIsolated G.F w := by
  cases w with
  | inl x0 =>
      constructor
      · intro h y0; exact h (Sum.inl y0)
      · intro h y
        cases y with
        | inl y0 => exact h y0
        | inr j => rfl
  | inr y0 =>
      constructor
      · intro h x0; exact h (Sum.inl x0)
      · intro h x
        cases x with
        | inl x0 => exact h x0
        | inr i => rfl

theorem isIsolated_fresh_inl (G : LabelledPattern ℓ₀ r₀) (ι : Fin ℓ₀ ↪ Fin ℓ₁)
    (κ : Fin r₀ ↪ Fin r₁) (x0 : ↥(Set.range (⇑ι))ᶜ) :
    isIsolated (padGraph G ι κ).F (Sum.inl (Sum.inr x0)) := fun _ => rfl

theorem isIsolated_fresh_inr (G : LabelledPattern ℓ₀ r₀) (ι : Fin ℓ₀ ↪ Fin ℓ₁)
    (κ : Fin r₀ ↪ Fin r₁) (y0 : ↥(Set.range (⇑κ))ᶜ) :
    isIsolated (padGraph G ι κ).F (Sum.inr (Sum.inr y0)) := by
  intro x
  cases x with
  | inl x0 => rfl
  | inr i => rfl

theorem labelVertex_padGraph_inl_ι (G : LabelledPattern ℓ₀ r₀) (ι : Fin ℓ₀ ↪ Fin ℓ₁)
    (κ : Fin r₀ ↪ Fin r₁) (i : Fin ℓ₀) :
    (padGraph G ι κ).labelVertex (Sum.inl (ι i)) = embPad G ι κ (G.labelVertex (Sum.inl i)) := by
  show Sum.inl (padA G ι (ι i)) = Sum.inl (Sum.inl (G.a i))
  rw [padA_apply_ι]

theorem labelVertex_padGraph_inl_fresh (G : LabelledPattern ℓ₀ r₀) (ι : Fin ℓ₀ ↪ Fin ℓ₁)
    (κ : Fin r₀ ↪ Fin r₁) {p : Fin ℓ₁} (h : p ∉ Set.range (⇑ι)) :
    (padGraph G ι κ).labelVertex (Sum.inl p) = Sum.inl (Sum.inr (⟨p, h⟩ : ↥(Set.range (⇑ι))ᶜ)) := by
  show Sum.inl (padA G ι p) = Sum.inl (Sum.inr ⟨p, h⟩)
  rw [padA_apply_of_notMem G ι h]

theorem labelVertex_padGraph_inr_κ (G : LabelledPattern ℓ₀ r₀) (ι : Fin ℓ₀ ↪ Fin ℓ₁)
    (κ : Fin r₀ ↪ Fin r₁) (j : Fin r₀) :
    (padGraph G ι κ).labelVertex (Sum.inr (κ j)) = embPad G ι κ (G.labelVertex (Sum.inr j)) := by
  show Sum.inr (padB G κ (κ j)) = Sum.inr (Sum.inl (G.b j))
  rw [padB_apply_κ]

theorem labelVertex_padGraph_inr_fresh (G : LabelledPattern ℓ₀ r₀) (ι : Fin ℓ₀ ↪ Fin ℓ₁)
    (κ : Fin r₀ ↪ Fin r₁) {p : Fin r₁} (h : p ∉ Set.range (⇑κ)) :
    (padGraph G ι κ).labelVertex (Sum.inr p) =
      Sum.inr (Sum.inr (⟨p, h⟩ : ↥(Set.range (⇑κ))ᶜ)) := by
  show Sum.inr (padB G κ p) = Sum.inr (Sum.inr ⟨p, h⟩)
  rw [padB_apply_of_notMem G κ h]

/-- The label support of `padGraph G ι κ` is exactly the image, under `embPad`, of `G`'s own
label support: every fresh vertex is isolated, hence never contributes. -/
theorem labelSupport_padGraph (G : LabelledPattern ℓ₀ r₀) (ι : Fin ℓ₀ ↪ Fin ℓ₁)
    (κ : Fin r₀ ↪ Fin r₁) :
    (padGraph G ι κ).labelSupport = G.labelSupport.image (embPad G ι κ) := by
  ext v
  simp only [LabelledPattern.labelSupport, Finset.mem_sdiff, Finset.mem_image]
  constructor
  · rintro ⟨⟨p, -, hp⟩, hniso⟩
    rcases p with i | j
    · by_cases hmem : i ∈ Set.range (⇑ι)
      · obtain ⟨i0, rfl⟩ := hmem
        rw [labelVertex_padGraph_inl_ι] at hp
        refine ⟨G.labelVertex (Sum.inl i0), ⟨⟨Sum.inl i0, Finset.mem_univ _, rfl⟩,
          not_isIsolated_iff_notMem.mp ?_⟩, hp⟩
        rw [← hp] at hniso
        exact fun h => hniso (mem_isolatedSet.mpr ((isIsolated_embPad_iff G ι κ).mpr h))
      · exfalso
        rw [labelVertex_padGraph_inl_fresh G ι κ hmem] at hp
        rw [← hp] at hniso
        exact hniso (mem_isolatedSet.mpr (isIsolated_fresh_inl G ι κ ⟨i, hmem⟩))
    · by_cases hmem : j ∈ Set.range (⇑κ)
      · obtain ⟨j0, rfl⟩ := hmem
        rw [labelVertex_padGraph_inr_κ] at hp
        refine ⟨G.labelVertex (Sum.inr j0), ⟨⟨Sum.inr j0, Finset.mem_univ _, rfl⟩,
          not_isIsolated_iff_notMem.mp ?_⟩, hp⟩
        rw [← hp] at hniso
        exact fun h => hniso (mem_isolatedSet.mpr ((isIsolated_embPad_iff G ι κ).mpr h))
      · exfalso
        rw [labelVertex_padGraph_inr_fresh G ι κ hmem] at hp
        rw [← hp] at hniso
        exact hniso (mem_isolatedSet.mpr (isIsolated_fresh_inr G ι κ ⟨j, hmem⟩))
  · rintro ⟨w, ⟨⟨p, -, hp⟩, hniso⟩, rfl⟩
    rcases p with i | j
    · exact ⟨⟨Sum.inl (ι i), Finset.mem_univ _, by
        rw [labelVertex_padGraph_inl_ι, hp]⟩,
        not_isIsolated_iff_notMem.mp
          (fun h => hniso (mem_isolatedSet.mpr ((isIsolated_embPad_iff G ι κ).mp h)))⟩
    · exact ⟨⟨Sum.inr (κ j), Finset.mem_univ _, by
        rw [labelVertex_padGraph_inr_κ, hp]⟩,
        not_isIsolated_iff_notMem.mp
          (fun h => hniso (mem_isolatedSet.mpr ((isIsolated_embPad_iff G ι κ).mp h)))⟩

/-- **`padGraph` preserves `InClass Δ k`** (no depth increase): the same root-exact
decomposition works, with bags pushed forward along `embPad`. -/
theorem inClass_padGraph {G : LabelledPattern ℓ₀ r₀} {Δ k : ℕ} (h : InClass Δ k G)
    (ι : Fin ℓ₀ ↪ Fin ℓ₁) (κ : Fin r₀ ↪ Fin r₁) : InClass Δ k (padGraph G ι κ) := by
  obtain ⟨D⟩ := h
  refine ⟨{ Node := D.Node
            root := D.root
            parent := D.parent
            parent_root := D.parent_root
            depth_le := D.depth_le
            bag := fun t => (D.bag t).image (embPad G ι κ)
            bag_root := by rw [D.bag_root, labelSupport_padGraph]
            card_bag_le := fun t => Finset.card_image_le.trans (D.card_bag_le t)
            exists_mem_bag := ?_
            exists_edge_mem_bag := ?_
            connected := ?_ }⟩
  · rintro v hv
    rcases v with (x0 | i) | (y0 | j)
    · obtain ⟨t, ht⟩ := D.exists_mem_bag (Sum.inl x0)
        (fun h => hv ((isIsolated_embPad_iff G ι κ).mpr h))
      exact ⟨t, Finset.mem_image.mpr ⟨Sum.inl x0, ht, rfl⟩⟩
    · exact absurd (isIsolated_fresh_inl G ι κ i) hv
    · obtain ⟨t, ht⟩ := D.exists_mem_bag (Sum.inr y0)
        (fun h => hv ((isIsolated_embPad_iff G ι κ).mpr h))
      exact ⟨t, Finset.mem_image.mpr ⟨Sum.inr y0, ht, rfl⟩⟩
    · exact absurd (isIsolated_fresh_inr G ι κ j) hv
  · rintro (x0 | i) (y0 | j) hxy
    · obtain ⟨t, htx, hty⟩ := D.exists_edge_mem_bag x0 y0 hxy
      exact ⟨t, Finset.mem_image.mpr ⟨Sum.inl x0, htx, rfl⟩,
        Finset.mem_image.mpr ⟨Sum.inr y0, hty, rfl⟩⟩
    · exact absurd rfl hxy
    · exact absurd rfl hxy
    · exact absurd rfl hxy
  · rintro v t1 t2 ht1 hd1 ht2 hd2
    rcases v with (x0 | i) | (y0 | j)
    · obtain ⟨w1, hw1mem, hw1eq⟩ := Finset.mem_image.mp ht1
      obtain ⟨w2, hw2mem, hw2eq⟩ := Finset.mem_image.mp ht2
      have hweq : w1 = w2 := embPad_injective G ι κ (hw1eq.trans hw2eq.symm)
      subst hweq
      refine D.connected w1 t1 t2 hw1mem ?_ hw2mem ?_
      · rcases hd1 with hd1 | hd1
        · exact Or.inl hd1
        · exact Or.inr (fun hc => hd1 (by rw [← hw1eq]; exact Finset.mem_image.mpr ⟨w1, hc, rfl⟩))
      · rcases hd2 with hd2 | hd2
        · exact Or.inl hd2
        · exact Or.inr (fun hc => hd2 (by rw [← hw2eq]; exact Finset.mem_image.mpr ⟨w1, hc, rfl⟩))
    · obtain ⟨w1, -, hw1eq⟩ := Finset.mem_image.mp ht1
      cases w1 with
      | inl x1 => exact absurd (Sum.inl_injective hw1eq) Sum.inl_ne_inr
      | inr y1 => exact absurd hw1eq.symm Sum.inl_ne_inr
    · obtain ⟨w1, hw1mem, hw1eq⟩ := Finset.mem_image.mp ht1
      obtain ⟨w2, hw2mem, hw2eq⟩ := Finset.mem_image.mp ht2
      have hweq : w1 = w2 := embPad_injective G ι κ (hw1eq.trans hw2eq.symm)
      subst hweq
      refine D.connected w1 t1 t2 hw1mem ?_ hw2mem ?_
      · rcases hd1 with hd1 | hd1
        · exact Or.inl hd1
        · exact Or.inr (fun hc => hd1 (by rw [← hw1eq]; exact Finset.mem_image.mpr ⟨w1, hc, rfl⟩))
      · rcases hd2 with hd2 | hd2
        · exact Or.inl hd2
        · exact Or.inr (fun hc => hd2 (by rw [← hw2eq]; exact Finset.mem_image.mpr ⟨w1, hc, rfl⟩))
    · obtain ⟨w1, -, hw1eq⟩ := Finset.mem_image.mp ht1
      cases w1 with
      | inl x1 => exact absurd hw1eq Sum.inl_ne_inr
      | inr y1 => exact absurd (Sum.inr_injective hw1eq) Sum.inl_ne_inr

/-- **`padGraph` preserves `InClassP`, transporting the label-position restriction along
`Sum.map ι κ`.** If `G`'s labelled non-isolated vertices are labelled only at positions in `P₀`,
the same holds for `padGraph G ι κ`, at positions in the image of `P₀` under `Sum.map ι κ`. -/
theorem inClassP_padGraph {G : LabelledPattern ℓ₀ r₀} {Δ k : ℕ} {P₀ : Finset (Fin ℓ₀ ⊕ Fin r₀)}
    (h : InClassP Δ k P₀ G) (ι : Fin ℓ₀ ↪ Fin ℓ₁) (κ : Fin r₀ ↪ Fin r₁) :
    InClassP Δ k (P₀.image (Sum.map (⇑ι) (⇑κ))) (padGraph G ι κ) := by
  refine ⟨inClass_padGraph h.1 ι κ, ?_⟩
  rw [labelSupport_padGraph]
  intro w hw
  obtain ⟨w0, hw0, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp (h.2 hw0)
  refine Finset.mem_image.mpr
    ⟨⟨Sum.map (⇑ι) (⇑κ) p.1, Finset.mem_image.mpr ⟨p.1, p.2, rfl⟩⟩, Finset.mem_univ _, ?_⟩
  rcases p with ⟨i | j, hmem⟩
  · show (padGraph G ι κ).labelVertex (Sum.inl (ι i)) = embPad G ι κ w0
    rw [labelVertex_padGraph_inl_ι, hp]
  · show (padGraph G ι κ).labelVertex (Sum.inr (κ j)) = embPad G ι κ w0
    rw [labelVertex_padGraph_inr_κ, hp]

/-! ### The polynomial identity -/

/-- Splitting a universally quantified statement over `Fin ℓ₁` into the "hit by `ι`" and
"fresh" parts. -/
theorem forall_padCases_iff (ι : Fin ℓ₀ ↪ Fin ℓ₁) (P : Fin ℓ₁ → Prop) :
    (∀ p, P p) ↔ (∀ i : Fin ℓ₀, P (ι i)) ∧ (∀ μ0 : ↥(Set.range (⇑ι))ᶜ, P (μ0 : Fin ℓ₁)) := by
  constructor
  · intro h; exact ⟨fun i => h _, fun μ0 => h _⟩
  · rintro ⟨h1, h2⟩ p
    by_cases hp : p ∈ Set.range (⇑ι)
    · obtain ⟨i, rfl⟩ := hp; exact h1 i
    · exact h2 ⟨p, hp⟩

/-- The big product over `padGraph`'s vertex sets, specialised to a colouring built from
`Sum.elim`, collapses to the big product over `G`'s own vertex sets: the fresh vertices
contribute only trivial (exponent-`0`) factors. -/
theorem padMult_prod_eq (G : LabelledPattern ℓ₀ r₀) (ι : Fin ℓ₀ ↪ Fin ℓ₁) (κ : Fin r₀ ↪ Fin r₁)
    (n : ℕ) (K : Type*) [CommSemiring K]
    (hA0 : G.F.A → Fin n) (hA1 : ↥(Set.range (⇑ι))ᶜ → Fin n)
    (hB0 : G.F.B → Fin n) (hB1 : ↥(Set.range (⇑κ))ᶜ → Fin n) :
    (∏ x : G.F.A ⊕ ↥(Set.range (⇑ι))ᶜ, ∏ y : G.F.B ⊕ ↥(Set.range (⇑κ))ᶜ,
      (MvPolynomial.X (Sum.elim hA0 hA1 x, Sum.elim hB0 hB1 y) : MvPolynomial (Fin n × Fin n) K) ^
        (padGraph G ι κ).F.mult x y)
      = ∏ x0 : G.F.A, ∏ y0 : G.F.B,
          (MvPolynomial.X (hA0 x0, hB0 y0) : MvPolynomial (Fin n × Fin n) K) ^ G.F.mult x0 y0 := by
  show (∏ x : G.F.A ⊕ ↥(Set.range (⇑ι))ᶜ, ∏ y : G.F.B ⊕ ↥(Set.range (⇑κ))ᶜ,
      (MvPolynomial.X (Sum.elim hA0 hA1 x, Sum.elim hB0 hB1 y) : MvPolynomial (Fin n × Fin n) K) ^
        Sum.elim (fun x0 => Sum.elim (G.F.mult x0) (fun _ => 0)) (fun _ => fun _ => 0) x y)
      = _
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, pow_zero, Finset.prod_const_one,
    mul_one]

open MvPolynomial in
/-- **The reindexing lemma's polynomial identity**: `padGraph`'s homomorphism polynomial at
`(v, w)` equals `G`'s own at `(v ∘ ι, w ∘ κ)`, exactly (no sum over the fresh positions: their
values are pinned down uniquely by `v`/`w`, not left free). -/
theorem labelledHom_padGraph (G : LabelledPattern ℓ₀ r₀) (ι : Fin ℓ₀ ↪ Fin ℓ₁)
    (κ : Fin r₀ ↪ Fin r₁) (n : ℕ) (K : Type*) [CommSemiring K] (v : Fin ℓ₁ → Fin n)
    (w : Fin r₁ → Fin n) :
    labelledHom K (padGraph G ι κ) n v w = labelledHom K G n (v ∘ ι) (w ∘ κ) := by
  set μ := ↥(Set.range (⇑ι))ᶜ
  set μ' := ↥(Set.range (⇑κ))ᶜ
  set target1 : μ → Fin n := fun μ0 => v (μ0 : Fin ℓ₁) with htarget1
  set target2 : μ' → Fin n := fun μ0 => w (μ0 : Fin r₁) with htarget2
  have hcondA : ∀ (hA0 : G.F.A → Fin n) (hA1 : μ → Fin n),
      (∀ p, Sum.elim hA0 hA1 (padA G ι p) = v p) ↔
        (∀ i, hA0 (G.a i) = (v ∘ ι) i) ∧ hA1 = target1 := by
    intro hA0 hA1
    rw [forall_padCases_iff ι]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, funext fun μ0 => ?_⟩
      · have := h1 i; rwa [padA_apply_ι, Sum.elim_inl] at this
      · have := h2 μ0; rwa [padA_apply_of_notMem G ι μ0.2, Sum.elim_inr] at this
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun μ0 => ?_⟩
      · rw [padA_apply_ι, Sum.elim_inl]; exact h1 i
      · rw [padA_apply_of_notMem G ι μ0.2, Sum.elim_inr, h2]
  have hcondB : ∀ (hB0 : G.F.B → Fin n) (hB1 : μ' → Fin n),
      (∀ q, Sum.elim hB0 hB1 (padB G κ q) = w q) ↔
        (∀ j, hB0 (G.b j) = (w ∘ κ) j) ∧ hB1 = target2 := by
    intro hB0 hB1
    rw [forall_padCases_iff κ]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun j => ?_, funext fun μ0 => ?_⟩
      · have := h1 j; rwa [padB_apply_κ, Sum.elim_inl] at this
      · have := h2 μ0; rwa [padB_apply_of_notMem G κ μ0.2, Sum.elim_inr] at this
    · rintro ⟨h1, h2⟩
      refine ⟨fun j => ?_, fun μ0 => ?_⟩
      · rw [padB_apply_κ, Sum.elim_inl]; exact h1 j
      · rw [padB_apply_of_notMem G κ μ0.2, Sum.elim_inr, h2]
  have key : ∀ (hA0 : G.F.A → Fin n) (hB0 : G.F.B → Fin n),
      (∑ hA1 : μ → Fin n, ∑ hB1 : μ' → Fin n,
        if (∀ p, Sum.elim hA0 hA1 (padA G ι p) = v p) ∧
            (∀ q, Sum.elim hB0 hB1 (padB G κ q) = w q) then
          (∏ x, ∏ y, MvPolynomial.X (Sum.elim hA0 hA1 x, Sum.elim hB0 hB1 y) ^
            (padGraph G ι κ).F.mult x y : MvPolynomial (Fin n × Fin n) K)
        else 0) =
        if (∀ i, hA0 (G.a i) = (v ∘ ι) i) ∧ (∀ j, hB0 (G.b j) = (w ∘ κ) j) then
          (∏ x0, ∏ y0, MvPolynomial.X (hA0 x0, hB0 y0) ^ G.F.mult x0 y0 :
            MvPolynomial (Fin n × Fin n) K)
        else 0 := by
    intro hA0 hB0
    simp only [hcondA hA0, hcondB hB0]
    by_cases hA0cond : ∀ i, hA0 (G.a i) = (v ∘ ι) i
    · by_cases hB0cond : ∀ j, hB0 (G.b j) = (w ∘ κ) j
      · rw [if_pos ⟨hA0cond, hB0cond⟩]
        rw [Finset.sum_eq_single target1]
        · rw [Finset.sum_eq_single target2]
          · rw [if_pos ⟨⟨hA0cond, rfl⟩, ⟨hB0cond, rfl⟩⟩]
            exact padMult_prod_eq G ι κ n K hA0 target1 hB0 target2
          · intro hB1 _ hne; exact if_neg (fun h => hne h.2.2)
          · intro h; exact absurd (Finset.mem_univ target2) h
        · intro hA1 _ hne
          apply Finset.sum_eq_zero
          intro hB1 _
          exact if_neg (fun h => hne h.1.2)
        · intro h; exact absurd (Finset.mem_univ target1) h
      · rw [if_neg (fun h : _ ∧ _ => hB0cond h.2)]
        apply Finset.sum_eq_zero; intro hA1 _
        apply Finset.sum_eq_zero; intro hB1 _
        exact if_neg (fun h => hB0cond h.2.1)
    · rw [if_neg (fun h : _ ∧ _ => hA0cond h.1)]
      apply Finset.sum_eq_zero; intro hA1 _
      apply Finset.sum_eq_zero; intro hB1 _
      exact if_neg (fun h => hA0cond h.1.1)
  calc labelledHom K (padGraph G ι κ) n v w
      = ∑ hA0 : G.F.A → Fin n, ∑ hA1 : μ → Fin n, ∑ hB : G.F.B ⊕ μ' → Fin n,
          if (∀ p, Sum.elim hA0 hA1 (padA G ι p) = v p) ∧ (∀ q, hB (padB G κ q) = w q) then
            (∏ x, ∏ y, MvPolynomial.X (Sum.elim hA0 hA1 x, hB y) ^
              (padGraph G ι κ).F.mult x y : MvPolynomial (Fin n × Fin n) K)
          else 0 :=
        sum_sumArrow (fun hA => ∑ hB : G.F.B ⊕ μ' → Fin n,
          if (∀ p, hA (padA G ι p) = v p) ∧ (∀ q, hB (padB G κ q) = w q) then
            (∏ x, ∏ y, MvPolynomial.X (hA x, hB y) ^ (padGraph G ι κ).F.mult x y :
              MvPolynomial (Fin n × Fin n) K)
          else 0)
    _ = ∑ hA0 : G.F.A → Fin n, ∑ hA1 : μ → Fin n, ∑ hB0 : G.F.B → Fin n, ∑ hB1 : μ' → Fin n,
          if (∀ p, Sum.elim hA0 hA1 (padA G ι p) = v p) ∧
              (∀ q, Sum.elim hB0 hB1 (padB G κ q) = w q) then
            (∏ x, ∏ y, MvPolynomial.X (Sum.elim hA0 hA1 x, Sum.elim hB0 hB1 y) ^
              (padGraph G ι κ).F.mult x y : MvPolynomial (Fin n × Fin n) K)
          else 0 := by
        refine Finset.sum_congr rfl (fun hA0 _ => Finset.sum_congr rfl (fun hA1 _ => ?_))
        exact sum_sumArrow (fun hB =>
          if (∀ p, Sum.elim hA0 hA1 (padA G ι p) = v p) ∧ (∀ q, hB (padB G κ q) = w q) then
            (∏ x, ∏ y, MvPolynomial.X (Sum.elim hA0 hA1 x, hB y) ^
              (padGraph G ι κ).F.mult x y : MvPolynomial (Fin n × Fin n) K)
          else 0)
    _ = ∑ hA0 : G.F.A → Fin n, ∑ hB0 : G.F.B → Fin n, ∑ hA1 : μ → Fin n, ∑ hB1 : μ' → Fin n,
          if (∀ p, Sum.elim hA0 hA1 (padA G ι p) = v p) ∧
              (∀ q, Sum.elim hB0 hB1 (padB G κ q) = w q) then
            (∏ x, ∏ y, MvPolynomial.X (Sum.elim hA0 hA1 x, Sum.elim hB0 hB1 y) ^
              (padGraph G ι κ).F.mult x y : MvPolynomial (Fin n × Fin n) K)
          else 0 :=
        Finset.sum_congr rfl (fun hA0 _ => Finset.sum_comm)
    _ = ∑ hA0 : G.F.A → Fin n, ∑ hB0 : G.F.B → Fin n,
          if (∀ i, hA0 (G.a i) = (v ∘ ι) i) ∧ (∀ j, hB0 (G.b j) = (w ∘ κ) j) then
            (∏ x0, ∏ y0, MvPolynomial.X (hA0 x0, hB0 y0) ^ G.F.mult x0 y0 :
              MvPolynomial (Fin n × Fin n) K)
          else 0 :=
        Finset.sum_congr rfl (fun hA0 _ => Finset.sum_congr rfl (fun hB0 _ => key hA0 hB0))
    _ = labelledHom K G n (v ∘ ι) (w ∘ κ) := rfl

/-! ### Lifting to the span -/

/-- **The reindexing lemma, at the span level.** If `φ ∈ 𝔗^{Δ,k}_n(ℓ₀,r₀)` (unrestricted) and
`ι : Fin ℓ₀ ↪ Fin ℓ₁`, `κ : Fin r₀ ↪ Fin r₁` are injective, then the reindexed function
`(v, w) ↦ φ (v ∘ ι) (w ∘ κ)` lies in `𝔗^{Δ,k}_n(ℓ₁,r₁)` (unrestricted), at the *same* depth
bound `Δ`. -/
theorem span𝔗P_pad_mem {K : Type*} [Field K] {Δ k n : ℕ} (ι : Fin ℓ₀ ↪ Fin ℓ₁)
    (κ : Fin r₀ ↪ Fin r₁)
    (φ : (Fin ℓ₀ → Fin n) → (Fin r₀ → Fin n) → MvPolynomial (Fin n × Fin n) K)
    (hφ : φ ∈ span𝔗P K Δ k n (Finset.univ : Finset (Fin ℓ₀ ⊕ Fin r₀))) :
    (fun v w => φ (v ∘ ι) (w ∘ κ)) ∈
      span𝔗P K Δ k n (Finset.univ : Finset (Fin ℓ₁ ⊕ Fin r₁)) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨G, hG, rfl⟩ := hx
      have heq : (fun v w => labelledHom K G n (v ∘ ι) (w ∘ κ)) =
          labelledHom K (padGraph G ι κ) n := by
        funext v w
        exact (labelledHom_padGraph G ι κ n K v w).symm
      rw [heq]
      exact Submodule.subset_span
        ⟨padGraph G ι κ, inClassP_univ_of_inClass (inClass_padGraph hG.1 ι κ), rfl⟩
  | zero =>
      have heq : (fun v w => (0 : (Fin ℓ₀ → Fin n) → (Fin r₀ → Fin n) →
          MvPolynomial (Fin n × Fin n) K) (v ∘ ι) (w ∘ κ)) =
          (0 : (Fin ℓ₁ → Fin n) → (Fin r₁ → Fin n) → MvPolynomial (Fin n × Fin n) K) := by
        funext v w; rfl
      rw [heq]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      have heq : (fun v w => (x + y) (v ∘ ι) (w ∘ κ)) =
          (fun v w => x (v ∘ ι) (w ∘ κ)) + (fun v w => y (v ∘ ι) (w ∘ κ)) := by
        funext v w; rfl
      rw [heq]; exact Submodule.add_mem _ ihx ihy
  | smul c x _ ih =>
      have heq : (fun v w => (c • x) (v ∘ ι) (w ∘ κ)) = c • (fun v w => x (v ∘ ι) (w ∘ κ)) := by
        funext v w; rfl
      rw [heq]; exact Submodule.smul_mem _ c ih

/-- **The `P`-restricted reindexing lemma, at the span level.** If `φ ∈ 𝔗^{Δ,k}_{n,P₀}(ℓ₀,r₀)`
and `ι, κ` are injective, then the reindexed function lies in `𝔗^{Δ,k}_{n,P}(ℓ₁,r₁)` for
`P := P₀.image (Sum.map ι κ)`, at the *same* depth bound `Δ`: unlike `span𝔗P_pad_mem`, this
tracks exactly which label positions of the padded arity are actually used, which is needed
whenever a subsequent step (e.g. `PatternsRestrictedSum.exists_ψSum`) requires `P.card ≤ k`
at the padded arity, not merely at the original one. -/
theorem span𝔗P_pad_mem_restrict {K : Type*} [Field K] {Δ k n : ℕ} {P₀ : Finset (Fin ℓ₀ ⊕ Fin r₀)}
    (ι : Fin ℓ₀ ↪ Fin ℓ₁) (κ : Fin r₀ ↪ Fin r₁)
    (φ : (Fin ℓ₀ → Fin n) → (Fin r₀ → Fin n) → MvPolynomial (Fin n × Fin n) K)
    (hφ : φ ∈ span𝔗P K Δ k n P₀) :
    (fun v w => φ (v ∘ ι) (w ∘ κ)) ∈ span𝔗P K Δ k n (P₀.image (Sum.map (⇑ι) (⇑κ))) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨G, hG, rfl⟩ := hx
      have heq : (fun v w => labelledHom K G n (v ∘ ι) (w ∘ κ)) =
          labelledHom K (padGraph G ι κ) n := by
        funext v w
        exact (labelledHom_padGraph G ι κ n K v w).symm
      rw [heq]
      exact Submodule.subset_span ⟨padGraph G ι κ, inClassP_padGraph hG ι κ, rfl⟩
  | zero =>
      have heq : (fun v w => (0 : (Fin ℓ₀ → Fin n) → (Fin r₀ → Fin n) →
          MvPolynomial (Fin n × Fin n) K) (v ∘ ι) (w ∘ κ)) =
          (0 : (Fin ℓ₁ → Fin n) → (Fin r₁ → Fin n) → MvPolynomial (Fin n × Fin n) K) := by
        funext v w; rfl
      rw [heq]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      have heq : (fun v w => (x + y) (v ∘ ι) (w ∘ κ)) =
          (fun v w => x (v ∘ ι) (w ∘ κ)) + (fun v w => y (v ∘ ι) (w ∘ κ)) := by
        funext v w; rfl
      rw [heq]; exact Submodule.add_mem _ ihx ihy
  | smul c x _ ih =>
      have heq : (fun v w => (c • x) (v ∘ ι) (w ∘ κ)) = c • (fun v w => x (v ∘ ι) (w ∘ κ)) := by
        funext v w; rfl
      rw [heq]; exact Submodule.smul_mem _ c ih

end Lax461425Proofs.PatternsInductionReindex
