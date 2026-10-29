import Lax461425Proofs.ConverseSubtreeInduction

/-!
**Step 2 of the correctness proof** (see the module docstring of `ConverseCorrectness.lean`):
specialising `P_eq_sum_ExtV` at the root and matching the result with `hom K F n`.

At `t = N.root`, `γ` is forced to be `rootAdm N n` (the unique map on the empty root bag), so
`P N.root (rootAdm N n) = ∑_{h admissible on V N.root} ∏_{all represented edges} x_{h(e)}`
(`ExtV`'s extension condition is vacuous since `bag root = ∅`). The set `V N.root` is, by
`represented_below`/`rep_mem`, exactly the set of non-isolated vertices of `F`.

**Route taken for isolated vertices.** Rather than adding wrapper gates to `CGate`
(`ConverseGates.lean`), this file follows route (a) recommended in the session plan: it proves
`(circuit N n K hn0 hE).Computes (hom K F n)` under the *additional* hypothesis that `F` has no
isolated vertices (`hNI`, stated below), so that `V N.root` is *all* of `F.A ⊕ F.B` and no
correction factor is needed. The reduction of a general pattern to one without isolated
vertices (`hom K F n = n ^ j * hom K F' n` for `F'` with the isolated vertices deleted, and the
easy transfer of `ForestwidthLE`) is left, as planned, to whoever assembles the final
`CircuitsForPatterns.exists_circuit`.
-/

namespace Lax461425Proofs

open Classical Lax461425.Circuits Lax461425.Circuits.Circuit Lax461425.HomomorphismPolynomials
open Lax461425.Forestwidth
open MvPolynomial

variable {F : Pattern} {Δ k : ℕ}

/-- `F` has no isolated vertices: every vertex is incident with some edge. -/
def NoIsolatedVertices (F : Pattern) : Prop :=
  ∀ v : F.A ⊕ F.B, ∃ a b, F.mult a b ≠ 0 ∧ (v = Sum.inl a ∨ v = Sum.inr b)

section RootMatch

variable (N : NormDecomp F Δ k) (n : ℕ)

/-- Every node is "above" the root: the root is reachable by iterating `parent` from any node
(in `Δ` steps). -/
theorem above_root (t : N.Node) : Above N t N.root := ⟨Δ, N.depth_le t⟩

/-- **`V N.root` is all of `F.A ⊕ F.B`, given no isolated vertices.** -/
theorem V_root_eq_univ (hNI : NoIsolatedVertices F) : V N N.root = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  obtain ⟨a, b, hmult, hv⟩ := hNI v
  rcases hv with hv | hv
  · exact (mem_V N).mpr ⟨N.rep a b, above_root N _, hv ▸ (N.rep_mem a b hmult).1⟩
  · exact (mem_V N).mpr ⟨N.rep a b, above_root N _, hv ▸ (N.rep_mem a b hmult).2⟩

/-- **`ExtV` at the root is everything**: the extension condition on the empty root bag is
vacuous. -/
theorem ExtV_root_eq_univ (γ : Adm F n (N.bag N.root)) : ExtV N n N.root γ = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro h
  rw [mem_ExtV]
  funext x
  exact absurd x.2 (not_mem_bag_root N x.1)

/-- **`edgesBelow` at the root is every edge of `F`** (with multiplicity, as a set of pairs
with nonzero multiplicity): every node is above the root. -/
theorem edgesBelow_root_eq_filter :
    edgesBelow N N.root = Finset.univ.filter (fun ab : F.A × F.B => F.mult ab.1 ab.2 ≠ 0) := by
  ext ab
  simp only [mem_edgesBelow_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.1, fun h => ⟨h, above_root N _⟩⟩

end RootMatch

section PairEquiv

variable (N : NormDecomp F Δ k) (n : ℕ) {hVroot : V N N.root = Finset.univ}

/-- The pair of maps `(h_A, h_B)` on `F.A`/`F.B` corresponding to an admissible map on
`V N.root = F.A ⊕ F.B`. -/
noncomputable def pairOfAdm (h : Adm F n (V N N.root)) : (F.A → Fin n) × (F.B → Fin n) :=
  (fun a => h ⟨Sum.inl a, hVroot ▸ Finset.mem_univ _⟩,
    fun b => h ⟨Sum.inr b, hVroot ▸ Finset.mem_univ _⟩)

/-- The admissible map on `V N.root = F.A ⊕ F.B` corresponding to a pair of maps. -/
noncomputable def admOfPair (p : (F.A → Fin n) × (F.B → Fin n)) : Adm F n (V N N.root) :=
  fun x => Sum.elim p.1 p.2 x.1

theorem admOfPair_pairOfAdm (h : Adm F n (V N N.root)) :
    admOfPair N n (pairOfAdm N n (hVroot := hVroot) h) = h := by
  funext x
  obtain ⟨v, hv⟩ := x
  cases v with
  | inl a => rfl
  | inr b => rfl

theorem pairOfAdm_admOfPair (p : (F.A → Fin n) × (F.B → Fin n)) :
    pairOfAdm N n (hVroot := hVroot) (admOfPair N n p) = p := rfl

/-- The bijection between admissible maps on `V N.root` and pairs `(h_A, h_B)`. -/
noncomputable def admRootEquiv : Adm F n (V N N.root) ≃ (F.A → Fin n) × (F.B → Fin n) where
  toFun := pairOfAdm N n (hVroot := hVroot)
  invFun := admOfPair N n
  left_inv := admOfPair_pairOfAdm N n
  right_inv := pairOfAdm_admOfPair N n

end PairEquiv

section Hom

variable (N : NormDecomp F Δ k) (n : ℕ) {K : Type*} [CommSemiring K]
variable {hVroot : V N N.root = Finset.univ}

/-- `Gval` at the root, evaluated at the map corresponding to a pair `(h_A, h_B)`, is the
homomorphism-counting product. -/
theorem Gval_root_admOfPair (p : (F.A → Fin n) × (F.B → Fin n)) :
    Gval N n (K := K) N.root (admOfPair N n p) =
      ∏ a : F.A, ∏ b : F.B, (X (p.1 a, p.2 b) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a b := by
  have hterm : ∀ ab : F.A × F.B,
      (if hab : ab ∈ edgesBelow N N.root then
          (X ((admOfPair N n p) ⟨Sum.inl ab.1, mem_V_left N hab⟩,
                (admOfPair N n p) ⟨Sum.inr ab.2, mem_V_right N hab⟩) :
            MvPolynomial (Fin n × Fin n) K) ^ F.mult ab.1 ab.2
        else 1) = (X (p.1 ab.1, p.2 ab.2) : MvPolynomial (Fin n × Fin n) K) ^ F.mult ab.1 ab.2 := by
    intro ab
    by_cases hab : ab ∈ edgesBelow N N.root
    · rw [dif_pos hab]; rfl
    · rw [dif_neg hab]
      have hmult : F.mult ab.1 ab.2 = 0 := by
        by_contra hmult
        exact hab ((mem_edgesBelow_iff N).mpr ⟨hmult, above_root N _⟩)
      rw [hmult, pow_zero]
  calc Gval N n (K := K) N.root (admOfPair N n p)
      = ∏ ab ∈ edgesBelow N N.root, edgeTerm N n (K := K) N.root (admOfPair N n p) ab :=
        Gval_eq_prod_edgeTerm N n N.root (admOfPair N n p)
    _ = ∏ ab : F.A × F.B, edgeTerm N n (K := K) N.root (admOfPair N n p) ab := by
        rw [Finset.prod_subset (Finset.subset_univ _)]
        intro ab _ hab
        unfold edgeTerm
        rw [dif_neg hab]
    _ = ∏ ab : F.A × F.B, (X (p.1 ab.1, p.2 ab.2) : MvPolynomial (Fin n × Fin n) K) ^ F.mult ab.1 ab.2 :=
        Finset.prod_congr rfl (fun ab _ => hterm ab)
    _ = ∏ a : F.A, ∏ b : F.B, (X (p.1 a, p.2 b) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a b :=
        Fintype.prod_prod_type _

/-- **Step 2, the main theorem.** `P N.root (rootAdm N n)` equals `hom K F n`, given `F` has no
isolated vertices. -/
theorem P_root_eq_hom (hn0 : 0 < n) (hNI : NoIsolatedVertices F) :
    P N n (K := K) N.root (rootAdm N n) = hom K F n := by
  have hVroot : V N N.root = Finset.univ := V_root_eq_univ N hNI
  rw [P_eq_sum_ExtV N n hn0 N.root (rootAdm N n), ExtV_root_eq_univ N n (rootAdm N n)]
  rw [show (∑ h ∈ (Finset.univ : Finset (Adm F n (V N N.root))), Gval N n (K := K) N.root h) =
      ∑ h : Adm F n (V N N.root), Gval N n (K := K) N.root h from rfl]
  rw [Fintype.sum_equiv (admRootEquiv N n (hVroot := hVroot))
    (Gval N n (K := K) N.root)
    (fun p => ∏ a : F.A, ∏ b : F.B, (X (p.1 a, p.2 b) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a b)
    (fun h => by
      show Gval N n (K := K) N.root h = _
      rw [show h = admOfPair N n (admRootEquiv N n (hVroot := hVroot) h) from
        (admOfPair_pairOfAdm N n (hVroot := hVroot) h).symm]
      exact Gval_root_admOfPair N n (admRootEquiv N n (hVroot := hVroot) h)),
    Fintype.sum_prod_type]
  rfl

variable (hE : ∃ a b, F.mult a b ≠ 0)

/-- **The main correctness theorem.** The circuit built from a normalised decomposition of `F`
computes `hom K F n`, provided `F` has no isolated vertices. -/
theorem circuit_computes_hom (hn0 : 0 < n) (hNI : NoIsolatedVertices F) :
    (circuit N n K hn0 hE).Computes (hom K F n) := by
  show (circuit N n K hn0 hE).ComputesAt (out N n) (hom K F n)
  show (circuit N n K hn0 hE).ComputesAt (CGate.R N.root (rootAdm N n)) (hom K F n)
  rw [← P_root_eq_hom N n hn0 hNI]
  exact computesAt_R N n hn0 hE N.root (rootAdm N n)

end Hom

end Lax461425Proofs
