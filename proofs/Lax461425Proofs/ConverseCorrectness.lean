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

open Classical Lax461425.Circuits Lax461425.HomomorphismPolynomials Lax461425.Forestwidth
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

end Lax461425Proofs
