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

/-- The number of children of `t` among the non-root nodes. -/
noncomputable def numChildren (t : N.Node) : ℕ :=
  ∑ c : NonRoot N, if N.parent c.1 = t then 1 else 0

theorem sum_numChildren_eq : ∑ t : N.Node, numChildren N t = Fintype.card (NonRoot N) := by
  unfold numChildren
  rw [Finset.sum_comm]
  simp

/-- The total multiplicity of wires out of a single `R`-gate is at most the number of children
of its node plus the total edge multiplicity represented there. -/
theorem wireOut_R_le (t : N.Node) (γ : Adm F n (N.bag t)) :
    ∑ h : CGate N n, wire N n (CGate.R t γ) h
      ≤ numChildren N t + ∑ ab ∈ edgesAt N t, F.mult ab.1 ab.2 := by
  rw [sum_CGate_eq N n (wire N n (CGate.R t γ))]
  have h1 : ∑ t' : N.Node, ∑ γ' : Adm F n (N.bag t'),
      wire N n (CGate.R t γ) (CGate.R t' γ') = 0 := by
    refine Finset.sum_eq_zero (fun t' _ => Finset.sum_eq_zero (fun γ' _ => ?_))
    simp [wire]
  have h2 : ∑ c : NonRoot N, ∑ δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1),
      wire N n (CGate.R t γ) (CGate.S c δ) ≤ numChildren N t := by
    unfold numChildren
    exact Finset.sum_le_sum (fun c _ => sum_wireRtoS_le N n t γ c)
  have h3 : ∑ i : Fin n, ∑ j : Fin n, wire N n (CGate.R t γ) (CGate.inp i j)
      = ∑ ab ∈ edgesAt N t, F.mult ab.1 ab.2 :=
    sum_wireRtoInp_eq N n t γ
  omega

/-- Every input gate has no outgoing wires. -/
theorem sum_wireOut_inp_eq :
    ∑ i : Fin n, ∑ j : Fin n, ∑ h : CGate N n, wire N n (CGate.inp i j) h = 0 := by
  refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
  refine Finset.sum_eq_zero (fun h _ => ?_)
  exact wire_eq_zero_of_isInput_aux N n (K := ℕ) (CGate.inp i j) h
    (by simp [CGate.label, GateLabel.IsInput])

/-- The total multiplicity of wires out of all `R`-gates is at most
`n ^ k * (|non-root nodes| + total edge multiplicity)`. -/
theorem sum_wireOut_R_le (hn0 : 0 < n) :
    ∑ t : N.Node, ∑ γ : Adm F n (N.bag t), ∑ h : CGate N n, wire N n (CGate.R t γ) h
      ≤ n ^ k * (Fintype.card (NonRoot N) + ∑ a : F.A, ∑ b : F.B, F.mult a b) := by
  calc ∑ t : N.Node, ∑ γ : Adm F n (N.bag t), ∑ h : CGate N n, wire N n (CGate.R t γ) h
      ≤ ∑ t : N.Node, ∑ _γ : Adm F n (N.bag t),
          (numChildren N t + ∑ ab ∈ edgesAt N t, F.mult ab.1 ab.2) :=
        Finset.sum_le_sum (fun t _ => Finset.sum_le_sum (fun γ _ => wireOut_R_le N n t γ))
    _ = ∑ t : N.Node, Fintype.card (Adm F n (N.bag t)) *
          (numChildren N t + ∑ ab ∈ edgesAt N t, F.mult ab.1 ab.2) :=
        Finset.sum_congr rfl
          (fun t _ => by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ])
    _ ≤ ∑ t : N.Node, n ^ k * (numChildren N t + ∑ ab ∈ edgesAt N t, F.mult ab.1 ab.2) :=
        Finset.sum_le_sum
          (fun t _ => Nat.mul_le_mul_right _ (card_Adm_le n (N.card_bag_le t) hn0))
    _ = n ^ k * ∑ t : N.Node, (numChildren N t + ∑ ab ∈ edgesAt N t, F.mult ab.1 ab.2) := by
        rw [Finset.mul_sum]
    _ = n ^ k *
          (∑ t : N.Node, numChildren N t + ∑ t : N.Node, ∑ ab ∈ edgesAt N t, F.mult ab.1 ab.2) := by
        rw [Finset.sum_add_distrib]
    _ = n ^ k * (Fintype.card (NonRoot N) + ∑ a : F.A, ∑ b : F.B, F.mult a b) := by
        rw [sum_numChildren_eq, sum_edgesAt_eq]

/-- The total multiplicity of wires out of all `S`-gates is at most `n ^ k` times the number of
non-root nodes. -/
theorem sum_wireOut_S_le (hn0 : 0 < n) :
    ∑ c : NonRoot N, ∑ δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1),
      ∑ h : CGate N n, wire N n (CGate.S c δ) h
      ≤ Fintype.card (NonRoot N) * n ^ k := by
  have step1 : ∀ (c : NonRoot N) (δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1)),
      ∑ h : CGate N n, wire N n (CGate.S c δ) h
        = ∑ t : N.Node, ∑ γ : Adm F n (N.bag t), wireStoR N n c δ t γ := by
    intro c δ
    rw [sum_CGate_eq N n (wire N n (CGate.S c δ))]
    have h2 : ∑ c' : NonRoot N, ∑ δ' : Adm F n (N.bag (N.parent c'.1) ∩ N.bag c'.1),
        wire N n (CGate.S c δ) (CGate.S c' δ') = 0 := by
      refine Finset.sum_eq_zero (fun c' _ => Finset.sum_eq_zero (fun δ' _ => ?_))
      simp [wire]
    have h3 : ∑ i : Fin n, ∑ j : Fin n, wire N n (CGate.S c δ) (CGate.inp i j) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
      simp [wire]
    have h1 : ∑ t : N.Node, ∑ γ : Adm F n (N.bag t), wire N n (CGate.S c δ) (CGate.R t γ)
        = ∑ t : N.Node, ∑ γ : Adm F n (N.bag t), wireStoR N n c δ t γ := rfl
    omega
  simp_rw [step1]
  calc ∑ c : NonRoot N, ∑ δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1),
        ∑ t : N.Node, ∑ γ : Adm F n (N.bag t), wireStoR N n c δ t γ
      ≤ ∑ _c : NonRoot N, n ^ k := by
        refine Finset.sum_le_sum (fun c _ => ?_)
        have swap1 : (∑ δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1), ∑ t : N.Node,
            ∑ γ : Adm F n (N.bag t), wireStoR N n c δ t γ)
            = ∑ t : N.Node, ∑ δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1),
                ∑ γ : Adm F n (N.bag t), wireStoR N n c δ t γ :=
          Finset.sum_comm
        have swap2 : ∀ t : N.Node, (∑ δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1),
            ∑ γ : Adm F n (N.bag t), wireStoR N n c δ t γ)
            = ∑ γ : Adm F n (N.bag t), ∑ δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1),
                wireStoR N n c δ t γ := fun t => Finset.sum_comm
        rw [show (∑ δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1), ∑ t : N.Node,
            ∑ γ : Adm F n (N.bag t), wireStoR N n c δ t γ)
            = ∑ t : N.Node, ∑ γ : Adm F n (N.bag t),
                ∑ δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1), wireStoR N n c δ t γ from
          swap1.trans (Finset.sum_congr rfl (fun t _ => swap2 t))]
        calc ∑ t : N.Node, ∑ γ : Adm F n (N.bag t),
              ∑ δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1), wireStoR N n c δ t γ
            ≤ ∑ t : N.Node, ∑ γ : Adm F n (N.bag t), (if c.1 = t then 1 else 0) :=
              Finset.sum_le_sum
                (fun t _ => Finset.sum_le_sum (fun γ _ => sum_wireStoR_le N n c t γ))
          _ = ∑ t : N.Node, (if c.1 = t then Fintype.card (Adm F n (N.bag t)) else 0) :=
              Finset.sum_congr rfl (fun t _ => by by_cases h : c.1 = t <;> simp [h])
          _ = Fintype.card (Adm F n (N.bag c.1)) := by
              rw [Finset.sum_ite_eq Finset.univ c.1 (fun t => Fintype.card (Adm F n (N.bag t)))]
              simp
          _ ≤ n ^ k := card_Adm_le n (N.card_bag_le c.1) hn0
    _ = Fintype.card (NonRoot N) * n ^ k := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]

/-- **Item 2 (size bound).** The constructed circuit has size at most
`5 * n ^ k * (|F.A| + |F.B| + |E(F)|)`, where `|E(F)| = ∑ a, ∑ b, F.mult a b` counts edges with
multiplicity. -/
theorem circuit_size_le (K : Type*) (hn0 : 0 < n) (hk : 2 ≤ k) (hE : ∃ a b, F.mult a b ≠ 0) :
    (circuit N n K hn0 hE).size
      ≤ 5 * n ^ k * (Fintype.card F.A + Fintype.card F.B + ∑ a, ∑ b, F.mult a b) := by
  show Fintype.card (CGate N n) + ∑ g : CGate N n, ∑ h, wire N n g h ≤ _
  rw [sum_CGate_eq N n (fun g => ∑ h, wire N n g h)]
  have hR := sum_wireOut_R_le N n hn0
  have hS := sum_wireOut_S_le N n hn0
  have hI := sum_wireOut_inp_eq N n
  have hgates := card_CGate_le N n hn0 hk
  have hnonroot : Fintype.card (NonRoot N) ≤ Fintype.card N.Node := Fintype.card_subtype_le _
  have hnode : Fintype.card N.Node ≤ Fintype.card F.A + Fintype.card F.B + 1 := by
    have := N.card_node_le
    rwa [Fintype.card_sum] at this
  obtain ⟨a0, b0, hmult⟩ := hE
  have hA1 : 1 ≤ Fintype.card F.A := Fintype.card_pos_iff.mpr ⟨a0⟩
  have hB1 : 1 ≤ Fintype.card F.B := Fintype.card_pos_iff.mpr ⟨b0⟩
  have hE1 : 1 ≤ ∑ a : F.A, ∑ b : F.B, F.mult a b := by
    have hb : F.mult a0 b0 ≤ ∑ b, F.mult a0 b :=
      Finset.single_le_sum (fun b _ => Nat.zero_le _) (Finset.mem_univ b0)
    have ha : (∑ b, F.mult a0 b) ≤ ∑ a : F.A, ∑ b, F.mult a b :=
      Finset.single_le_sum (f := fun a => ∑ b, F.mult a b) (fun a _ => Nat.zero_le _)
        (Finset.mem_univ a0)
    omega
  set P := n ^ k with hP
  set Nd := Fintype.card N.Node with hNd
  set Nd' := Fintype.card (NonRoot N) with hNd'
  set A := Fintype.card F.A with hA
  set B := Fintype.card F.B with hB
  set E := ∑ a : F.A, ∑ b : F.B, F.mult a b with hE2
  -- Step 1: combine the gate-count and wire-out bounds into `4 * Nd * P + P + P * E`.
  have e1 : P * (Nd' + E) = P * Nd' + P * E := by ring
  have e2 : Nd' * P = P * Nd' := mul_comm _ _
  have e3 : 2 * Nd * P = 2 * (Nd * P) := by ring
  have e4 : 4 * Nd * P = 4 * (Nd * P) := by ring
  have key1 : Nd' * P ≤ Nd * P := Nat.mul_le_mul_right P hnonroot
  have step1 : Fintype.card (CGate N n) +
      (∑ t, ∑ γ, ∑ h, wire N n (CGate.R t γ) h + ∑ c, ∑ δ, ∑ h, wire N n (CGate.S c δ) h +
        ∑ i, ∑ j, ∑ h, wire N n (CGate.inp i j) h) ≤ 4 * Nd * P + P + P * E := by
    omega
  -- Step 2: `4 * Nd * P + P + P * E ≤ 5 * P * (A + B + E)`, using `Nd ≤ A + B + 1` and
  -- `A, B, E ≥ 1`.
  have key2 : Nd * P ≤ A * P + B * P + P := by
    have := Nat.mul_le_mul_right P hnode
    rwa [add_mul, add_mul, one_mul] at this
  have key2' : 4 * (Nd * P) ≤ 4 * (A * P) + 4 * (B * P) + 4 * P := by
    have := Nat.mul_le_mul_left 4 key2
    rwa [Nat.mul_add, Nat.mul_add] at this
  have key4 : P * 6 ≤ P * (A + B + 4 * E) := Nat.mul_le_mul_left P (by omega)
  have key4' : 6 * P ≤ A * P + B * P + 4 * (P * E) := by
    have e5 : P * 6 = 6 * P := by ring
    have e6 : P * (A + B + 4 * E) = A * P + B * P + 4 * (P * E) := by ring
    rwa [e5, e6] at key4
  have step2 : 4 * Nd * P + P + P * E ≤ 5 * P * (A + B + E) := by
    have goalEq : 5 * P * (A + B + E)
        = 4 * (A * P) + 4 * (B * P) + (A * P + B * P + 4 * (P * E)) + P * E := by ring
    have hfinal : 5 * P ≤ A * P + B * P + 4 * (P * E) := by
      have h5P6P : 5 * P ≤ 6 * P := by omega
      omega
    calc 4 * Nd * P + P + P * E
        = 4 * (Nd * P) + P + P * E := by rw [e4]
      _ ≤ (4 * (A * P) + 4 * (B * P) + 4 * P) + P + P * E := by omega
      _ = 4 * (A * P) + 4 * (B * P) + 5 * P + P * E := by ring
      _ ≤ 4 * (A * P) + 4 * (B * P) + (A * P + B * P + 4 * (P * E)) + P * E := by omega
      _ = 5 * P * (A + B + E) := goalEq.symm
  calc Fintype.card (CGate N n) +
        (∑ t, ∑ γ, ∑ h, wire N n (CGate.R t γ) h + ∑ c, ∑ δ, ∑ h, wire N n (CGate.S c δ) h +
          ∑ i, ∑ j, ∑ h, wire N n (CGate.inp i j) h)
      ≤ 4 * Nd * P + P + P * E := step1
    _ ≤ 5 * P * (A + B + E) := step2

end SizeBound

end Lax461425Proofs
