import Lax461425Proofs.ConverseGates

/-!
Correctness of the circuit built in `ConverseGates.lean`: the gate `R t γ` computes the
polynomial `P t γ`, and the gate `S c δ` computes the polynomial `Q c δ`, where `P`/`Q` mirror
the recursive structure of the circuit itself:
$$
  P\,t\,\gamma = \Big(\prod_{ab \text{ represented at } t} x_{\gamma(a),\gamma(b)}^{F(a,b)}\Big)
    \cdot \prod_{c \text{ child of } t} Q\,c\,(\gamma|_{\beta(t)\cap\beta(c)}), \qquad
  Q\,c\,\delta = \sum_{\gamma' \supseteq \delta \text{ admissible on } \beta(c)} P\,c\,\gamma'.
-/

namespace Lax461425Proofs

open Classical Lax461425.Circuits Lax461425.Circuits.Circuit Lax461425.HomomorphismPolynomials
open Lax461425.Forestwidth
open MvPolynomial

variable {F : Pattern} {Δ k : ℕ}

section Value

variable (N : NormDecomp F Δ k) (n : ℕ) {K : Type*} [CommSemiring K]

/-- The children of a node `t`: the non-root nodes whose parent is `t`. -/
noncomputable def children (t : N.Node) : Finset (NonRoot N) :=
  Finset.univ.filter (fun c => N.parent c.1 = t)

theorem mem_children {t : N.Node} {c : NonRoot N} : c ∈ children N t ↔ N.parent c.1 = t := by
  simp [children]

/-- Restrict an admissible map on `β(t)` to `β(parent c) ∩ β(c)`, given that `t = parent c`. -/
noncomputable def restrictFromParent {t : N.Node} (c : NonRoot N) (hp : N.parent c.1 = t)
    (γ : Adm F n (N.bag t)) : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1) :=
  fun x => γ ⟨x.1, hp ▸ Finset.inter_subset_left x.2⟩

/-- The value computed at the gate `R t γ`, defined by recursion on the distance from `t` to a
leaf (decreasing `Δ - level t` towards children): the product of the edge variables
represented at `t`, times the product over children `c` of `t` of the sum, over admissible
maps `γ'` on `β(c)` whose restriction to `β(t) ∩ β(c)` agrees with `γ`, of the value at `c`. -/
noncomputable def P : (t : N.Node) → Adm F n (N.bag t) → MvPolynomial (Fin n × Fin n) K
  | t => fun γ =>
      (∏ ab ∈ (edgesAt N t).attach,
          (X (γ ⟨Sum.inl ab.1.1, mem_bag_left N ab.2⟩,
                γ ⟨Sum.inr ab.1.2, mem_bag_right N ab.2⟩) : MvPolynomial (Fin n × Fin n) K)
            ^ F.mult ab.1.1 ab.1.2) *
      ∏ cc ∈ (children N t).attach,
        have hp : N.parent cc.1.1 = t := (mem_children N).mp cc.2
        have hlt : Δ - level N.depth_le cc.1.1 < Δ - level N.depth_le t := by
          have hlev : level N.depth_le cc.1.1 = level N.depth_le t + 1 := by
            rw [level_succ N.depth_le N.parent_root cc.1.2, hp]
          have hle : level N.depth_le cc.1.1 ≤ Δ := level_le N.depth_le cc.1.1
          omega
        ∑ γ' ∈ (Finset.univ : Finset (Adm F n (N.bag cc.1.1))).filter
            (fun γ' => ∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent cc.1.1) ∩ N.bag cc.1.1),
              γ' ⟨x, Finset.inter_subset_right hx⟩ = restrictFromParent N n cc.1 hp γ ⟨x, hx⟩),
          P cc.1.1 γ'
termination_by t => Δ - level N.depth_le t
decreasing_by assumption

/-- The value computed at the gate `S c δ`: the sum, over admissible maps `γ'` on `β(c)` whose
restriction to `β(parent c) ∩ β(c)` agrees with `δ`, of the value at `c`. -/
noncomputable def Q (c : NonRoot N) (δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1)) :
    MvPolynomial (Fin n × Fin n) K :=
  ∑ γ' ∈ (Finset.univ : Finset (Adm F n (N.bag c.1))).filter
      (fun γ' => ∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
        γ' ⟨x, Finset.inter_subset_right hx⟩ = δ ⟨x, hx⟩),
    P N n c.1 γ'

/-- The defining equation of `P`, unfolded: the recursion step rewritten using `Q`. -/
theorem P_eq (t : N.Node) (γ : Adm F n (N.bag t)) :
    P N n (K := K) t γ =
      (∏ ab ∈ (edgesAt N t).attach,
          (X (γ ⟨Sum.inl ab.1.1, mem_bag_left N ab.2⟩,
                γ ⟨Sum.inr ab.1.2, mem_bag_right N ab.2⟩) : MvPolynomial (Fin n × Fin n) K)
            ^ F.mult ab.1.1 ab.1.2) *
      ∏ cc ∈ (children N t).attach,
        Q N n cc.1 (restrictFromParent N n cc.1 ((mem_children N).mp cc.2) γ) := by
  rw [P]
  simp only [Q, restrictFromParent]

end Value

section Decompose

variable (N : NormDecomp F Δ k) (n : ℕ)

/-- Any product over all gates splits into the product over `R`-gates, the product over
`S`-gates, and the product over input gates. -/
@[to_additive]
theorem prod_cgate {M : Type*} [CommMonoid M] (f : CGate N n → M) :
    ∏ h : CGate N n, f h =
      (∏ t' : N.Node, ∏ γ' : Adm F n (N.bag t'), f (CGate.R t' γ')) *
      (∏ c' : NonRoot N, ∏ δ' : Adm F n (N.bag (N.parent c'.1) ∩ N.bag c'.1), f (CGate.S c' δ')) *
      (∏ i : Fin n, ∏ j : Fin n, f (CGate.inp i j)) := by
  rw [Fintype.prod_equiv (CGate.equivSigma N n) f
    (fun x => Sum.elim (fun p => f (CGate.R p.1 p.2))
      (Sum.elim (fun p => f (CGate.S p.1 p.2)) (fun p => f (CGate.inp p.1 p.2))) x)
    (fun x => by cases x <;> rfl),
    Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sigma, Fintype.prod_sigma,
    Fintype.prod_prod_type, mul_assoc]
  rfl

end Decompose

section EdgeRegroup

variable (N : NormDecomp F Δ k) (n : ℕ) {K : Type*} [CommSemiring K]

/-- Regrouping the product of input-gate values by the pair `(i, j)` they are wired to
recovers the product over represented edges: this is the "nice form" of the input-gate
contribution to `R t γ`. -/
theorem prod_pow_wireRtoInp (t : N.Node) (γ : Adm F n (N.bag t)) :
    ∏ p : Fin n × Fin n, (X p : MvPolynomial (Fin n × Fin n) K) ^ wireRtoInp N n t γ p.1 p.2 =
      ∏ ab ∈ (edgesAt N t).attach,
        (X (γ ⟨Sum.inl ab.1.1, mem_bag_left N ab.2⟩, γ ⟨Sum.inr ab.1.2, mem_bag_right N ab.2⟩) :
          MvPolynomial (Fin n × Fin n) K) ^ F.mult ab.1.1 ab.1.2 := by
  classical
  set g : {ab // ab ∈ edgesAt N t} → Fin n × Fin n :=
    fun ab => (γ ⟨Sum.inl ab.1.1, mem_bag_left N ab.2⟩, γ ⟨Sum.inr ab.1.2, mem_bag_right N ab.2⟩)
    with hg
  have hw : ∀ p : Fin n × Fin n, wireRtoInp N n t γ p.1 p.2 =
      ∑ ab ∈ (edgesAt N t).attach.filter (fun ab => g ab = p), F.mult ab.1.1 ab.1.2 := by
    intro p
    rw [wireRtoInp, ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    apply Finset.filter_congr
    intro ab _
    simp [hg, Prod.ext_iff]
  have hmaps : ∀ ab ∈ (edgesAt N t).attach, g ab ∈ (Finset.univ : Finset (Fin n × Fin n)) :=
    fun ab _ => Finset.mem_univ _
  rw [← Finset.prod_fiberwise_of_maps_to hmaps
    (fun ab => (X (g ab) : MvPolynomial (Fin n × Fin n) K) ^ F.mult ab.1.1 ab.1.2)]
  apply Finset.prod_congr rfl
  intro p _
  rw [hw p]
  rw [show (∏ ab ∈ (edgesAt N t).attach.filter (fun ab => g ab = p),
        (X (g ab) : MvPolynomial (Fin n × Fin n) K) ^ F.mult ab.1.1 ab.1.2) =
      ∏ ab ∈ (edgesAt N t).attach.filter (fun ab => g ab = p),
        (X p : MvPolynomial (Fin n × Fin n) K) ^ F.mult ab.1.1 ab.1.2 from
    Finset.prod_congr rfl (fun ab hab => by rw [(Finset.mem_filter.mp hab).2]),
    Finset.prod_pow_eq_pow_sum]

end EdgeRegroup

section ChildRegroup

variable (N : NormDecomp F Δ k) (n : ℕ)

/-- Regrouping the product, over all non-root nodes `c'` and all admissible `δ'` on
`β(parent c') ∩ β(c')`, of `(V c' δ')^(wireRtoS t γ c' δ')`, by picking out for each child `c'`
of `t` the unique `δ'` agreeing with `γ`: this is the "nice form" of the `S`-gate
contribution to `R t γ`. -/
theorem prod_pow_wireRtoS {M : Type*} [CommMonoid M] (t : N.Node) (γ : Adm F n (N.bag t))
    (V : (c' : NonRoot N) → Adm F n (N.bag (N.parent c'.1) ∩ N.bag c'.1) → M) :
    ∏ c' : NonRoot N, ∏ δ' : Adm F n (N.bag (N.parent c'.1) ∩ N.bag c'.1),
        (V c' δ') ^ (wireRtoS N n t γ c' δ') =
      ∏ cc ∈ (children N t).attach,
        V cc.1 (restrictFromParent N n cc.1 ((mem_children N).mp cc.2) γ) := by
  have hinner : ∀ c' : NonRoot N, (∏ δ' : Adm F n (N.bag (N.parent c'.1) ∩ N.bag c'.1),
      (V c' δ') ^ (wireRtoS N n t γ c' δ')) =
      if h : N.parent c'.1 = t then V c' (restrictFromParent N n c' h γ) else 1 := by
    intro c'
    by_cases hpc : N.parent c'.1 = t
    · rw [dif_pos hpc]
      have hone : wireRtoS N n t γ c' (restrictFromParent N n c' hpc γ) = 1 :=
        wireRtoS_eq_one N n hpc (fun x hx => rfl)
      rw [Fintype.prod_eq_single (restrictFromParent N n c' hpc γ) (fun δ' hne => by
        have h0 : wireRtoS N n t γ c' δ' = 0 := by
          unfold wireRtoS
          rw [dif_pos hpc]
          apply if_neg
          intro hmatch
          apply hne
          funext x
          exact (hmatch x.1 x.2).symm
        rw [h0, pow_zero]), hone, pow_one]
    · rw [dif_neg hpc]
      apply Finset.prod_eq_one
      intro δ' _
      have h0 : wireRtoS N n t γ c' δ' = 0 := by
        show wireRtoS N n t γ c' δ' = 0
        unfold wireRtoS
        rw [dif_neg hpc]
      rw [h0, pow_zero]
  calc ∏ c' : NonRoot N, ∏ δ', (V c' δ') ^ (wireRtoS N n t γ c' δ')
      = ∏ c' : NonRoot N,
          (if h : N.parent c'.1 = t then V c' (restrictFromParent N n c' h γ) else 1) :=
        Finset.prod_congr rfl (fun c' _ => hinner c')
    _ = ∏ c' ∈ children N t,
          (if h : N.parent c'.1 = t then V c' (restrictFromParent N n c' h γ) else 1) := by
        symm
        apply Finset.prod_subset (Finset.subset_univ _)
        intro x _ hx
        exact dif_neg (fun h => hx ((mem_children N).mpr h))
    _ = ∏ cc ∈ (children N t).attach,
          (if h : N.parent cc.1.1 = t then V cc.1 (restrictFromParent N n cc.1 h γ) else 1) :=
        (Finset.prod_attach _ _).symm
    _ = ∏ cc ∈ (children N t).attach,
          V cc.1 (restrictFromParent N n cc.1 ((mem_children N).mp cc.2) γ) :=
        Finset.prod_congr rfl (fun cc _ => dif_pos ((mem_children N).mp cc.2))

end ChildRegroup

section ParentRegroup

variable (N : NormDecomp F Δ k) (n : ℕ)

/-- Regrouping the sum, over all nodes `t'` and all admissible `γ'` on `β(t')`, of
`(wireStoR c δ t' γ') • V t' γ'`, picks out the single node `c.1` and sums over the `γ'`
extending `δ`: this is the "nice form" of the `S`-gate's unique child. -/
theorem sum_wireStoR {M : Type*} [AddCommMonoid M] (c : NonRoot N)
    (δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1))
    (V : (t' : N.Node) → Adm F n (N.bag t') → M) :
    ∑ t' : N.Node, ∑ γ' : Adm F n (N.bag t'), (wireStoR N n c δ t' γ') • V t' γ' =
      ∑ γ' ∈ (Finset.univ : Finset (Adm F n (N.bag c.1))).filter
          (fun γ' => ∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
            γ' ⟨x, Finset.inter_subset_right hx⟩ = δ ⟨x, hx⟩),
        V c.1 γ' := by
  have hzero : ∀ t' : N.Node, t' ≠ c.1 →
      (∑ γ' : Adm F n (N.bag t'), (wireStoR N n c δ t' γ') • V t' γ') = 0 := by
    intro t' hne
    apply Finset.sum_eq_zero
    intro γ' _
    have h0 : wireStoR N n c δ t' γ' = 0 := by
      unfold wireStoR
      exact dif_neg (fun h => hne h.symm)
    rw [h0, zero_smul]
  rw [Fintype.sum_eq_single c.1 hzero]
  have hwire : ∀ γ' : Adm F n (N.bag c.1), wireStoR N n c δ c.1 γ' =
      if (∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
            γ' ⟨x, Finset.inter_subset_right hx⟩ = δ ⟨x, hx⟩) then 1 else 0 := by
    intro γ'
    show wireStoR N n c δ c.1 γ' = _
    unfold wireStoR
    rw [dif_pos rfl]
  rw [show (∑ γ' : Adm F n (N.bag c.1), (wireStoR N n c δ c.1 γ') • V c.1 γ') =
      ∑ γ' : Adm F n (N.bag c.1),
        (if (∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
              γ' ⟨x, Finset.inter_subset_right hx⟩ = δ ⟨x, hx⟩) then V c.1 γ' else 0) from
    Finset.sum_congr rfl (fun γ' _ => by rw [hwire γ']; split <;> simp),
    Finset.sum_filter]

end ParentRegroup

section ComputesAt

variable (N : NormDecomp F Δ k) (n : ℕ) {K : Type*} [CommSemiring K]

/-- The value the circuit should compute at each gate: `P` at `R`-gates, `Q` at `S`-gates, the
corresponding variable at input gates. -/
noncomputable def val : CGate N n → MvPolynomial (Fin n × Fin n) K
  | .R t γ => P N n t γ
  | .S c δ => Q N n c δ
  | .inp i j => X (i, j)

set_option maxHeartbeats 1000000 in
/-- The generic wire-weighted product at `R t γ` equals `P t γ`. -/
theorem prod_val_wire_R (t : N.Node) (γ : Adm F n (N.bag t)) :
    ∏ h : CGate N n, (val N n (K := K) h) ^ (wire N n (CGate.R t γ) h) = P N n t γ := by
  rw [prod_cgate]
  have h1 : (∏ t' : N.Node, ∏ γ' : Adm F n (N.bag t'),
      (val N n (K := K) (CGate.R t' γ')) ^ (wire N n (CGate.R t γ) (CGate.R t' γ'))) = 1 := by
    apply Finset.prod_eq_one
    intro t' _
    apply Finset.prod_eq_one
    intro γ' _
    rw [show wire N n (CGate.R t γ) (CGate.R t' γ') = 0 from rfl, pow_zero]
  have h2 : (∏ c' : NonRoot N, ∏ δ' : Adm F n (N.bag (N.parent c'.1) ∩ N.bag c'.1),
      (val N n (K := K) (CGate.S c' δ')) ^ (wire N n (CGate.R t γ) (CGate.S c' δ'))) =
      ∏ cc ∈ (children N t).attach,
        Q N n cc.1 (restrictFromParent N n cc.1 ((mem_children N).mp cc.2) γ) :=
    prod_pow_wireRtoS N n t γ (fun c' δ' => Q N n c' δ')
  have h3 : (∏ i : Fin n, ∏ j : Fin n,
      (val N n (K := K) (CGate.inp i j)) ^ (wire N n (CGate.R t γ) (CGate.inp i j))) =
      ∏ ab ∈ (edgesAt N t).attach,
        (X (γ ⟨Sum.inl ab.1.1, mem_bag_left N ab.2⟩, γ ⟨Sum.inr ab.1.2, mem_bag_right N ab.2⟩) :
          MvPolynomial (Fin n × Fin n) K) ^ F.mult ab.1.1 ab.1.2 := by
    have step1 : (∏ i : Fin n, ∏ j : Fin n,
        (val N n (K := K) (CGate.inp i j)) ^ (wire N n (CGate.R t γ) (CGate.inp i j))) =
        ∏ i : Fin n, ∏ j : Fin n,
          (X (i, j) : MvPolynomial (Fin n × Fin n) K) ^ wireRtoInp N n t γ i j :=
      Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => rfl))
    have step2 : (∏ i : Fin n, ∏ j : Fin n,
        (X (i, j) : MvPolynomial (Fin n × Fin n) K) ^ wireRtoInp N n t γ i j) =
        ∏ p : Fin n × Fin n, (X p : MvPolynomial (Fin n × Fin n) K) ^ wireRtoInp N n t γ p.1 p.2 :=
      (Fintype.prod_prod_type
        (fun p : Fin n × Fin n => (X p : MvPolynomial (Fin n × Fin n) K) ^ wireRtoInp N n t γ p.1 p.2)).symm
    rw [step1, step2]
    exact prod_pow_wireRtoInp N n t γ
  rw [h1, h2, h3, one_mul, P_eq]
  ring

set_option maxHeartbeats 1000000 in
/-- The generic wire-weighted sum at `S c δ` equals `Q c δ`. -/
theorem sum_val_wire_S (c : NonRoot N) (δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1)) :
    ∑ h : CGate N n, (wire N n (CGate.S c δ) h) • (val N n (K := K) h) = Q N n c δ := by
  rw [sum_cgate]
  have h1 : (∑ t' : N.Node, ∑ γ' : Adm F n (N.bag t'),
      (wire N n (CGate.S c δ) (CGate.R t' γ')) • (val N n (K := K) (CGate.R t' γ'))) =
      Q N n c δ := by
    have step : (∑ t' : N.Node, ∑ γ' : Adm F n (N.bag t'),
          (wire N n (CGate.S c δ) (CGate.R t' γ')) • (val N n (K := K) (CGate.R t' γ'))) =
        ∑ t' : N.Node, ∑ γ' : Adm F n (N.bag t'), (wireStoR N n c δ t' γ') • (P N n t' γ') :=
      Finset.sum_congr rfl (fun t' _ => Finset.sum_congr rfl (fun γ' _ => rfl))
    rw [step, sum_wireStoR]
    simp only [Q]
  have h2 : (∑ c' : NonRoot N, ∑ δ' : Adm F n (N.bag (N.parent c'.1) ∩ N.bag c'.1),
      (wire N n (CGate.S c δ) (CGate.S c' δ')) • (val N n (K := K) (CGate.S c' δ'))) = 0 := by
    apply Finset.sum_eq_zero
    intro c' _
    apply Finset.sum_eq_zero
    intro δ' _
    rw [show wire N n (CGate.S c δ) (CGate.S c' δ') = 0 from rfl, zero_smul]
  have h3 : (∑ i : Fin n, ∑ j : Fin n,
      (wire N n (CGate.S c δ) (CGate.inp i j)) • (val N n (K := K) (CGate.inp i j))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [show wire N n (CGate.S c δ) (CGate.inp i j) = 0 from rfl, zero_smul]
  rw [h1, h2, h3, add_zero, add_zero]

variable (hn0 : 0 < n) (hE : ∃ a b, F.mult a b ≠ 0)

set_option maxHeartbeats 1000000 in
/-- **Correctness, gate-by-gate.** Every `R`-gate `R t γ` computes `P t γ` and every `S`-gate
`S c δ` computes `Q c δ`, proven by well-founded recursion on the distance from the node to a
leaf (the same measure used to define `P`): the `R`-part uses the `S`-part at children, and the
`S`-part (for the same node) uses the `R`-part just established. -/
theorem computesAt_RS : ∀ t : N.Node,
    (∀ γ : Adm F n (N.bag t), (circuit N n K hn0 hE).ComputesAt (CGate.R t γ) (P N n t γ)) ∧
    (∀ (hroot : t ≠ N.root) (δ : Adm F n (N.bag (N.parent t) ∩ N.bag t)),
      (circuit N n K hn0 hE).ComputesAt
        (CGate.S (⟨t, hroot⟩ : NonRoot N) δ) (Q N n ⟨t, hroot⟩ δ))
  | t => by
      have hRpart : ∀ γ : Adm F n (N.bag t),
          (circuit N n K hn0 hE).ComputesAt (CGate.R t γ) (P N n t γ) := by
        intro γ
        rw [← prod_val_wire_R N n t γ]
        refine ComputesAt.mul (C := circuit N n K hn0 hE) (g := CGate.R t γ) (val N n (K := K))
          rfl ?_
        intro h hpos0
        have hpos : 0 < wire N n (CGate.R t γ) h := hpos0
        cases h with
        | inp i j => exact ComputesAt.var rfl
        | R t' γ' =>
            exact absurd hpos (by rw [show wire N n (CGate.R t γ) (CGate.R t' γ') = 0 from rfl]; omega)
        | S c' δ' =>
            show (circuit N n K hn0 hE).ComputesAt (CGate.S c' δ') (val N n (K := K) (CGate.S c' δ'))
            show (circuit N n K hn0 hE).ComputesAt (CGate.S c' δ') (Q N n c' δ')
            have hlt : Δ - level N.depth_le c'.1 < Δ - level N.depth_le t := by
              have hmu := wire_pos_lt N n hpos
              simp only [mu] at hmu
              omega
            have := (computesAt_RS c'.1).2 c'.2 δ'
            exact this
      refine ⟨hRpart, ?_⟩
      intro hroot δ
      rw [← sum_val_wire_S N n (⟨t, hroot⟩ : NonRoot N) δ]
      refine ComputesAt.add (C := circuit N n K hn0 hE) (g := CGate.S (⟨t, hroot⟩ : NonRoot N) δ)
        (val N n (K := K)) rfl ?_
      intro h hpos0
      have hpos : 0 < wire N n (CGate.S (⟨t, hroot⟩ : NonRoot N) δ) h := hpos0
      cases h with
      | R t' γ' =>
          show (circuit N n K hn0 hE).ComputesAt (CGate.R t' γ') (val N n (K := K) (CGate.R t' γ'))
          show (circuit N n K hn0 hE).ComputesAt (CGate.R t' γ') (P N n t' γ')
          have heq : (⟨t, hroot⟩ : NonRoot N).1 = t' := by
            by_contra hne
            exact absurd hpos (by
              simp only [wire, wireStoR]
              rw [dif_neg hne]
              omega)
          simp only at heq
          subst heq
          exact hRpart γ'
      | S c' δ' =>
          exact absurd hpos
            (by rw [show wire N n (CGate.S (⟨t, hroot⟩ : NonRoot N) δ) (CGate.S c' δ') = 0 from rfl]; omega)
      | inp i j =>
          exact absurd hpos
            (by rw [show wire N n (CGate.S (⟨t, hroot⟩ : NonRoot N) δ) (CGate.inp i j) = 0 from rfl]; omega)
termination_by t => Δ - level N.depth_le t
decreasing_by assumption

/-- **Correctness.** The gate `R t γ` computes `P t γ`. -/
theorem computesAt_R (t : N.Node) (γ : Adm F n (N.bag t)) :
    (circuit N n K hn0 hE).ComputesAt (CGate.R t γ) (P N n t γ) :=
  (computesAt_RS N n hn0 hE t).1 γ

/-- **Correctness.** The gate `S c δ` computes `Q c δ`. -/
theorem computesAt_S (c : NonRoot N) (δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1)) :
    (circuit N n K hn0 hE).ComputesAt (CGate.S c δ) (Q N n c δ) := by
  obtain ⟨t, hroot⟩ := c
  exact (computesAt_RS N n hn0 hE t).2 hroot δ

end ComputesAt

end Lax461425Proofs
