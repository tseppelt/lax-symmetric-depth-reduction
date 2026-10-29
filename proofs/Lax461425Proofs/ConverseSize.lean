import Lax461425Proofs.ConverseGates

/-!
The size bound for the circuit built in `ConverseGates.lean`:
`(circuit N n K hn0 hE).size ≤ 5 * n ^ k * (|F.A| + |F.B| + |E(F)|)`, where `|E(F)|` is the
total edge multiplicity `∑ a, ∑ b, F.mult a b`. This is a direct counting argument from the
construction, using only the cardinality bounds on bags (`card_bag_le`) and nodes
(`NormDecomp.card_node_le`), not correctness.
-/

namespace Lax461425Proofs

open Classical Lax461425.Circuits Lax461425.HomomorphismPolynomials Lax461425.Forestwidth

variable {F : Pattern} {Δ k : ℕ}

section SizeBound

variable (N : NormDecomp F Δ k) (n : ℕ)

/-! ### Cardinality of admissible maps -/

/-- The number of admissible maps on a finset `S` is `n ^ S.card`. -/
theorem card_Adm (S : Finset (F.A ⊕ F.B)) : Fintype.card (Adm F n S) = n ^ S.card := by
  show Fintype.card (↥S → Fin n) = n ^ S.card
  rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]

/-- If `S.card ≤ k`, there are at most `n ^ k` admissible maps on `S`. -/
theorem card_Adm_le {S : Finset (F.A ⊕ F.B)} (hS : S.card ≤ k) (hn0 : 0 < n) :
    Fintype.card (Adm F n S) ≤ n ^ k := by
  rw [card_Adm]
  exact Nat.pow_le_pow_right hn0 hS

/-- The card of the intersection bag at a non-root node is also at most `k`. -/
theorem card_inter_le (c : NonRoot N) : (N.bag (N.parent c.1) ∩ N.bag c.1).card ≤ k :=
  le_trans (Finset.card_le_card Finset.inter_subset_right) (N.card_bag_le c.1)

/-! ### Counting the gates -/

/-- The number of `R`-gates. -/
noncomputable def numR : ℕ := ∑ t : N.Node, Fintype.card (Adm F n (N.bag t))

/-- The number of `S`-gates. -/
noncomputable def numS : ℕ := ∑ c : NonRoot N, Fintype.card (Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1))

theorem card_CGate_eq : Fintype.card (CGate N n) = numR N n + numS N n + n * n := by
  unfold numR numS
  rw [Fintype.card_congr (CGate.equivSigma N n), Fintype.card_sum, Fintype.card_sigma,
    Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  ring

theorem numR_le (hn0 : 0 < n) : numR N n ≤ Fintype.card N.Node * n ^ k := by
  unfold numR
  calc ∑ t : N.Node, Fintype.card (Adm F n (N.bag t))
      ≤ ∑ _t : N.Node, n ^ k :=
        Finset.sum_le_sum (fun t _ => card_Adm_le n (N.card_bag_le t) hn0)
    _ = Fintype.card N.Node * n ^ k := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]

theorem numS_le (hn0 : 0 < n) : numS N n ≤ Fintype.card N.Node * n ^ k := by
  unfold numS
  calc ∑ c : NonRoot N, Fintype.card (Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1))
      ≤ ∑ _c : NonRoot N, n ^ k :=
        Finset.sum_le_sum (fun c _ => card_Adm_le n (card_inter_le N c) hn0)
    _ = Fintype.card (NonRoot N) * n ^ k := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
    _ ≤ Fintype.card N.Node * n ^ k :=
        Nat.mul_le_mul_right _ (Fintype.card_subtype_le _)

theorem card_CGate_le (hn0 : 0 < n) (hk : 2 ≤ k) :
    Fintype.card (CGate N n) ≤ 2 * Fintype.card N.Node * n ^ k + n ^ k := by
  rw [card_CGate_eq]
  have h1 := numR_le N n hn0
  have h2 := numS_le N n hn0
  have h3 : n * n ≤ n ^ k := by
    calc n * n = n ^ 2 := (sq n).symm
    _ ≤ n ^ k := Nat.pow_le_pow_right hn0 hk
  have h4 : 2 * Fintype.card N.Node * n ^ k
      = Fintype.card N.Node * n ^ k + Fintype.card N.Node * n ^ k := by ring
  omega

/-! ### Counting the wires -/

/-- Collapsing a double sum over `Fin n × Fin n` indexed by a conjunction of point-equalities:
only the term at `(p, q)` survives. -/
theorem sum_prod_ite_eq (p q : Fin n) (c : ℕ) :
    ∑ i : Fin n, ∑ j : Fin n, (if p = i ∧ q = j then c else 0) = c := by
  have hinner : ∀ i : Fin n, (∑ j : Fin n, if p = i ∧ q = j then c else 0)
      = if p = i then c else 0 := by
    intro i
    by_cases h : p = i
    · simp [h]
    · simp [h]
  simp [hinner]

/-- The total multiplicity of wires from `R t γ` to all input gates equals the total
multiplicity of edges represented at `t` (independent of `γ`). -/
theorem sum_wireRtoInp_eq (t : N.Node) (γ : Adm F n (N.bag t)) :
    ∑ i : Fin n, ∑ j : Fin n, wireRtoInp N n t γ i j = ∑ ab ∈ edgesAt N t, F.mult ab.1 ab.2 := by
  rw [← Finset.sum_attach (edgesAt N t) (fun ab => F.mult ab.1 ab.2)]
  have step1 : ∑ i : Fin n, ∑ j : Fin n, wireRtoInp N n t γ i j
      = ∑ i : Fin n, ∑ ab ∈ (edgesAt N t).attach, ∑ j : Fin n,
          (if γ ⟨Sum.inl ab.1.1, mem_bag_left N ab.2⟩ = i ∧
              γ ⟨Sum.inr ab.1.2, mem_bag_right N ab.2⟩ = j then F.mult ab.1.1 ab.1.2 else 0) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [wireRtoInp]
    exact Finset.sum_comm
  rw [step1, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun ab _ => sum_prod_ite_eq n _ _ _)

/-- Any sum over all gates splits into the sum over `R`-gates, `S`-gates, and input gates. -/
theorem sum_CGate_eq (f : CGate N n → ℕ) :
    ∑ g : CGate N n, f g =
      (∑ t : N.Node, ∑ γ : Adm F n (N.bag t), f (CGate.R t γ)) +
      (∑ c : NonRoot N, ∑ δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1), f (CGate.S c δ)) +
      (∑ i : Fin n, ∑ j : Fin n, f (CGate.inp i j)) := by
  have heq : ∑ g : CGate N n, f g = ∑ x : (Σ t : N.Node, Adm F n (N.bag t)) ⊕
      (Σ c : NonRoot N, Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1)) ⊕ (Fin n × Fin n),
      (match x with
        | Sum.inl ⟨t, γ⟩ => f (CGate.R t γ)
        | Sum.inr (Sum.inl ⟨c, δ⟩) => f (CGate.S c δ)
        | Sum.inr (Sum.inr (i, j)) => f (CGate.inp i j)) :=
    Fintype.sum_equiv (CGate.equivSigma N n) _ _ (fun g => by cases g <;> rfl)
  rw [heq]
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma]
  rw [show (∑ x : Fin n × Fin n, f (CGate.inp x.1 x.2)) = ∑ i, ∑ j, f (CGate.inp i j) from
    Fintype.sum_prod_type' (fun i j => f (CGate.inp i j))]
  ring

/-- The edges represented at the nodes of `N` partition `A × B` (weighted by multiplicity): the
total multiplicity represented across all nodes equals the total multiplicity `∑ a, ∑ b, mult`.
-/
theorem sum_edgesAt_eq :
    ∑ t : N.Node, ∑ ab ∈ edgesAt N t, F.mult ab.1 ab.2 = ∑ a : F.A, ∑ b : F.B, F.mult a b := by
  have step : ∀ t : N.Node, ∑ ab ∈ edgesAt N t, F.mult ab.1 ab.2 =
      ∑ ab : F.A × F.B,
        (if F.mult ab.1 ab.2 ≠ 0 ∧ N.rep ab.1 ab.2 = t then F.mult ab.1 ab.2 else 0) := by
    intro t
    unfold edgesAt
    rw [Finset.sum_filter]
  simp_rw [step]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type' F.mult]
  apply Finset.sum_congr rfl
  intro ab _
  by_cases hmult : F.mult ab.1 ab.2 = 0
  · simp [hmult]
  · rw [Finset.sum_eq_single (N.rep ab.1 ab.2)
      (fun t _ ht => if_neg (fun h => ht h.2.symm))
      (fun hnm => absurd (Finset.mem_univ _) hnm),
      if_pos ⟨hmult, rfl⟩]

/-- At most one admissible map `δ` on the intersection bag gives a nonzero wire from `R t γ`
into `S c δ`: this bounds the total by the indicator of `c` being a child of `t`. -/
theorem sum_wireRtoS_le (t : N.Node) (γ : Adm F n (N.bag t)) (c : NonRoot N) :
    ∑ δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1), wireRtoS N n t γ c δ
      ≤ if N.parent c.1 = t then 1 else 0 := by
  by_cases h : N.parent c.1 = t
  · rw [if_pos h]
    have hzero : ∀ δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1),
        δ ≠ (fun x => γ ⟨x.1, h ▸ Finset.inter_subset_left x.2⟩) → wireRtoS N n t γ c δ = 0 := by
      intro δ hδ
      unfold wireRtoS
      rw [dif_pos h]
      refine if_neg (fun hcond => hδ ?_)
      funext x
      obtain ⟨x1, hx1⟩ := x
      exact (hcond x1 hx1).symm
    have hval : wireRtoS N n t γ c (fun x => γ ⟨x.1, h ▸ Finset.inter_subset_left x.2⟩) = 1 :=
      wireRtoS_eq_one N n h (fun x hx => rfl)
    rw [Finset.sum_eq_single _ (fun δ _ hδ => hzero δ hδ)
      (fun hnm => absurd (Finset.mem_univ _) hnm), hval]
  · rw [if_neg h]
    refine le_of_eq (Finset.sum_eq_zero (fun δ _ => ?_))
    unfold wireRtoS
    rw [dif_neg h]

/-- At most one admissible map `δ` on the intersection bag gives a nonzero wire from `S c δ`
into `R t γ`: this bounds the total (summed over `δ`, for fixed `t, γ`) by the indicator of
`t = c`. -/
theorem sum_wireStoR_le (c : NonRoot N) (t : N.Node) (γ : Adm F n (N.bag t)) :
    ∑ δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1), wireStoR N n c δ t γ
      ≤ if c.1 = t then 1 else 0 := by
  by_cases h : c.1 = t
  · rw [if_pos h]
    have hzero : ∀ δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1),
        δ ≠ (fun x => γ ⟨x.1, h ▸ Finset.inter_subset_right x.2⟩) → wireStoR N n c δ t γ = 0 := by
      intro δ hδ
      unfold wireStoR
      rw [dif_pos h]
      refine if_neg (fun hcond => hδ ?_)
      funext x
      obtain ⟨x1, hx1⟩ := x
      exact (hcond x1 hx1).symm
    have hval : wireStoR N n c (fun x => γ ⟨x.1, h ▸ Finset.inter_subset_right x.2⟩) t γ = 1 :=
      wireStoR_eq_one N n h (fun x hx => rfl)
    rw [Finset.sum_eq_single _ (fun δ _ hδ => hzero δ hδ)
      (fun hnm => absurd (Finset.mem_univ _) hnm), hval]
  · rw [if_neg h]
    refine le_of_eq (Finset.sum_eq_zero (fun δ _ => ?_))
    unfold wireStoR
    rw [dif_neg h]

end SizeBound

end Lax461425Proofs
