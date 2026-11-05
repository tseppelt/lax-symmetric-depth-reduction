import Lax461425.SymmetricABPs
import Mathlib.Tactic

/-!
Finite paths in an acyclic ABP. In particular the bound used by `PathData` discards no
directed paths, and extending a source path along one edge remains within that bound.
-/

namespace Lax461425Proofs.SymmetricABPPaths

open Lax461425.SymmetricABPs

variable {V K : Type*} (G : ABP V K)

theorem walk_reaches {l : ℕ} (f : Fin (l + 1) → G.Vertex)
    (he : ∀ i : Fin l, G.edge (f i.castSucc) (f i.succ))
    {i j : Fin (l + 1)} (hij : i < j) : Relation.TransGen G.edge (f i) (f j) := by
  have h : ∀ j (hj : j ≤ l) i (hi : i < j),
      Relation.TransGen G.edge (f ⟨i, by omega⟩) (f ⟨j, by omega⟩) := by
    intro j
    induction j with
    | zero => intro hj i hi; omega
    | succ j ih =>
      intro hj i hi
      have hlast := he ⟨j, by omega⟩
      by_cases hEq : i = j
      · subst i
        exact Relation.TransGen.single hlast
      · exact Relation.TransGen.tail (ih (by omega) i (by omega)) hlast
  exact h j.val (by omega) i.val hij

/-- A walk in a DAG never repeats a vertex. -/
theorem walk_injective {l : ℕ} (f : Fin (l + 1) → G.Vertex)
    (he : ∀ i : Fin l, G.edge (f i.castSucc) (f i.succ)) : Function.Injective f := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hr := walk_reaches G f he hlt
    rw [hij] at hr
    exact G.acyclic _ hr
  · have hr := walk_reaches G f he hlt
    rw [hij] at hr
    exact G.acyclic _ hr

/-- Every walk has strictly fewer edges than the number of vertices. -/
theorem walk_length_lt_card {l : ℕ} (f : Fin (l + 1) → G.Vertex)
    (he : ∀ i : Fin l, G.edge (f i.castSucc) (f i.succ)) :
    l < Fintype.card G.Vertex := by
  have := Fintype.card_le_of_injective f (walk_injective G f he)
  simp only [Fintype.card_fin] at this
  omega

/-- Append a final vertex to a vertex sequence. -/
def appendVertex {l : ℕ} (f : Fin (l + 1) → G.Vertex) (v : G.Vertex) :
    Fin (l + 1 + 1) → G.Vertex := Fin.lastCases v f

@[simp] theorem appendVertex_castSucc {l : ℕ} (f : Fin (l + 1) → G.Vertex)
    (v : G.Vertex) (i : Fin (l + 1)) : appendVertex G f v i.castSucc = f i := by
  simp [appendVertex]

@[simp] theorem appendVertex_last {l : ℕ} (f : Fin (l + 1) → G.Vertex)
    (v : G.Vertex) : appendVertex G f v (Fin.last (l + 1)) = v := by
  simp [appendVertex]

theorem appendVertex_edges {l : ℕ} (f : Fin (l + 1) → G.Vertex) (v : G.Vertex)
    (he : ∀ i : Fin l, G.edge (f i.castSucc) (f i.succ))
    (hv : G.edge (f (Fin.last l)) v) :
    ∀ i : Fin (l + 1),
      G.edge (appendVertex G f v i.castSucc) (appendVertex G f v i.succ) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hv
  · change G.edge (appendVertex G f v j.castSucc.castSucc)
      (appendVertex G f v j.succ.castSucc)
    rw [appendVertex_castSucc, appendVertex_castSucc]
    exact he j

/-- A path can be extended along a final edge; acyclicity proves the new length bound. -/
def append {u v : G.Vertex} (p : G.PathTo u) (huv : G.edge u v) : G.PathTo v := by
  let f := appendVertex G p.1.2 v
  have he : ∀ i : Fin (p.1.1.val + 1), G.edge (f i.castSucc) (f i.succ) :=
    appendVertex_edges G p.1.2 v p.2.2.2 (by simpa [p.2.2.1] using huv)
  have hcard := walk_length_lt_card G f he
  refine ⟨⟨⟨p.1.1.val + 1, hcard⟩, f⟩, ?_⟩
  refine ⟨?_, ?_, he⟩
  · change appendVertex G p.1.2 v (0 : Fin (p.1.1.val + 1 + 1)) = G.source
    change appendVertex G p.1.2 v (0 : Fin (p.1.1.val + 1)).castSucc = G.source
    rw [appendVertex_castSucc]
    exact p.2.1
  · exact appendVertex_last G p.1.2 v

/-- Paths are determined by their length and vertex sequence. -/
theorem path_ext {v : G.Vertex} {p q : G.PathTo v}
    (hl : p.1.1.val = q.1.1.val)
    (hf : ∀ i j, i.val = j.val → p.1.2 i = q.1.2 j) : p = q := by
  rcases p with ⟨⟨⟨l, hl'⟩, f⟩, hp⟩
  rcases q with ⟨⟨⟨m, hm'⟩, g⟩, hq⟩
  change l = m at hl
  subst m
  have hfg : f = g := by funext i; exact hf i i rfl
  subst g
  rfl

theorem length_pos_of_ne_source {v : G.Vertex} (hv : v ≠ G.source) (p : G.PathTo v) :
    0 < p.1.1.val := by
  by_contra h
  have h0 : p.1.1.val = 0 := by omega
  have hi : (0 : Fin (p.1.1.val + 1)) = Fin.last p.1.1.val := by
    apply Fin.ext
    simp [h0]
  exact hv (p.2.2.1.symm.trans ((congrArg p.1.2 hi).symm.trans p.2.1))

/-- The unique zero-length path at the source. -/
def nilPath : G.PathTo G.source :=
  ⟨⟨⟨0, Fintype.card_pos_iff.mpr ⟨G.source⟩⟩, fun _ => G.source⟩,
    rfl, rfl, fun i => Fin.elim0 i⟩

theorem length_eq_zero_at_source (p : G.PathTo G.source) : p.1.1.val = 0 := by
  by_contra h
  have hpos : (0 : Fin (p.1.1.val + 1)) < Fin.last p.1.1.val := by
    change 0 < p.1.1.val
    omega
  have hr := walk_reaches G p.1.2 p.2.2.2 hpos
  rw [p.2.1, p.2.2.1] at hr
  exact G.acyclic _ hr

theorem eq_nilPath (p : G.PathTo G.source) : p = nilPath G := by
  apply path_ext G (length_eq_zero_at_source G p)
  intro i j hij
  change p.1.2 i = G.source
  have hz := length_eq_zero_at_source G p
  have hi : i = 0 := by apply Fin.ext; have := i.isLt; change i.val = 0; omega
  subst i
  exact p.2.1

/-- A non-source path has a last edge. -/
def predecessor {v : G.Vertex} (hv : v ≠ G.source) (p : G.PathTo v) : G.Vertex :=
  p.1.2 ⟨p.1.1.val - 1, by have := length_pos_of_ne_source G hv p; omega⟩

theorem predecessor_edge {v : G.Vertex} (hv : v ≠ G.source) (p : G.PathTo v) :
    G.edge (predecessor G hv p) v := by
  have hpos := length_pos_of_ne_source G hv p
  have he := p.2.2.2 ⟨p.1.1.val - 1, by omega⟩
  have hi : (⟨p.1.1.val - 1, by omega⟩ : Fin p.1.1.val).succ =
      Fin.last p.1.1.val := by apply Fin.ext; simp; omega
  rw [hi, p.2.2.1] at he
  exact he

/-- Delete the last edge of a non-source path. -/
def dropLast {v : G.Vertex} (hv : v ≠ G.source) (p : G.PathTo v) :
    G.PathTo (predecessor G hv p) := by
  have hpos := length_pos_of_ne_source G hv p
  have hcard := p.1.1.isLt
  let f : Fin (p.1.1.val - 1 + 1) → G.Vertex :=
    fun i => p.1.2 ⟨i.val, by have := i.isLt; omega⟩
  refine ⟨⟨⟨p.1.1.val - 1, by omega⟩, f⟩, ?_⟩
  refine ⟨p.2.1, rfl, ?_⟩
  intro i
  change Fin (p.1.1.val - 1) at i
  exact p.2.2.2 ⟨i.val, by have := i.isLt; omega⟩

theorem append_prefix {v : G.Vertex} (hv : v ≠ G.source) (p : G.PathTo v) :
    append G (dropLast G hv p) (predecessor_edge G hv p) = p := by
  have hpos := length_pos_of_ne_source G hv p
  apply path_ext G (by change p.1.1.val - 1 + 1 = p.1.1.val; omega)
  intro i j hij
  change Fin (p.1.1.val - 1 + 1 + 1) at i
  change Fin.lastCases v (fun k : Fin (p.1.1.val - 1 + 1) =>
    p.1.2 ⟨k.val, by have := k.isLt; omega⟩) i = p.1.2 j
  change i.val = j.val at hij
  revert j
  refine Fin.lastCases ?_ (fun k => ?_) i
  · intro j hij
    have hj : j = Fin.last p.1.1.val := by apply Fin.ext; simp at hij ⊢; omega
    simp only [Fin.lastCases_last]
    rw [hj, p.2.2.1]
  · intro j hij
    simp only [Fin.lastCases_castSucc]
    change p.1.2 ⟨k.val, _⟩ = p.1.2 j
    exact congrArg p.1.2 (Fin.ext hij)

theorem vertex_eq_of_path_eq {v : G.Vertex} {p q : G.PathTo v} (h : p = q)
    (i : Fin (p.1.1.val + 1)) (j : Fin (q.1.1.val + 1)) (hij : i.val = j.val) :
    p.1.2 i = q.1.2 j := by
  subst q
  exact congrArg p.1.2 (Fin.ext hij)

/-- A source path to a predecessor together with the final edge into `v`. -/
abbrev IncomingPath (v : G.Vertex) :=
  (u : {u : G.Vertex // G.edge u v}) × G.PathTo u.val

theorem append_injective (v : G.Vertex) :
    Function.Injective (fun p : IncomingPath G v => append G p.2 p.1.2) := by
  rintro ⟨⟨u, hu⟩, p⟩ ⟨⟨w, hw⟩, q⟩ hpq
  have hl : p.1.1.val = q.1.1.val := by
    have h := congrArg (fun r : G.PathTo v => r.1.1.val) hpq
    change p.1.1.val + 1 = q.1.1.val + 1 at h
    omega
  have hvertex : ∀ (i : Fin (p.1.1.val + 1)) (j : Fin (q.1.1.val + 1)),
      i.val = j.val → p.1.2 i = q.1.2 j := by
    intro i j hij
    have hh := vertex_eq_of_path_eq G hpq i.castSucc j.castSucc hij
    change appendVertex G p.1.2 v i.castSucc = appendVertex G q.1.2 v j.castSucc at hh
    rw [appendVertex_castSucc, appendVertex_castSucc] at hh
    exact hh
  have huw : u = w := by
    have hh := hvertex (Fin.last p.1.1.val) (Fin.last q.1.1.val) hl
    rwa [p.2.2.1, q.2.2.1] at hh
  subst w
  have hp : p = q := path_ext G hl hvertex
  subst q
  rfl

/-- Decomposing a non-source path into its last edge is a bijection. -/
noncomputable def incomingEquiv {v : G.Vertex} (hv : v ≠ G.source) :
    IncomingPath G v ≃ G.PathTo v :=
  Equiv.ofBijective (fun p => append G p.2 p.1.2)
    ⟨append_injective G v, fun p =>
      ⟨⟨⟨predecessor G hv p, predecessor_edge G hv p⟩, dropLast G hv p⟩,
        append_prefix G hv p⟩⟩

section Weights

variable [Fintype V] [CommSemiring K]

theorem polynomial_eq_sum_pathWeight : G.polynomial = ∑ p : G.Path, G.pathWeight p := rfl

theorem computes_of_pathEquiv {H : Type*} [Fintype H] (e : H ≃ G.Path)
    (f : H → MvPolynomial V K) (hf : ∀ h, G.pathWeight (e h) = f h) :
    G.Computes (∑ h, f h) := by
  unfold ABP.Computes
  rw [polynomial_eq_sum_pathWeight, ← e.sum_comp]
  exact Finset.sum_congr rfl (fun h _ => hf h)

theorem polynomialAt_source : G.polynomialAt G.source = 1 := by
  classical
  unfold ABP.polynomialAt
  rw [Finset.sum_eq_single (nilPath G)]
  · change (∏ _ : Fin 0, (G.label G.source G.source).polynomial) = 1
    simp
  · intro p hp hne
    exact False.elim (hne (eq_nilPath G p))
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem pathWeight_append {u v : G.Vertex} (p : G.PathTo u) (huv : G.edge u v) :
    G.pathWeightTo (append G p huv) = G.pathWeightTo p * (G.label u v).polynomial := by
  classical
  change (∏ i : Fin (p.1.1.val + 1),
    (G.label (appendVertex G p.1.2 v i.castSucc)
      (appendVertex G p.1.2 v i.succ)).polynomial) = _
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    change (G.label (appendVertex G p.1.2 v i.castSucc.castSucc)
      (appendVertex G p.1.2 v i.succ.castSucc)).polynomial = _
    rw [appendVertex_castSucc, appendVertex_castSucc]
  · rw [appendVertex_castSucc]
    change (G.label (p.1.2 (Fin.last p.1.1.val))
      (appendVertex G p.1.2 v (Fin.last (p.1.1.val + 1)))).polynomial = _
    rw [appendVertex_last, p.2.2.1]

/-- The dynamic-programming recurrence is a theorem about the literal path-sum semantics. -/
theorem polynomialAt_eq_sum_predecessors {v : G.Vertex} (hv : v ≠ G.source) :
    G.polynomialAt v = ∑ u : {u : G.Vertex // G.edge u v},
      G.polynomialAt u.val * (G.label u.val v).polynomial := by
  classical
  unfold ABP.polynomialAt
  rw [← (incomingEquiv G hv).sum_comp (fun p => G.pathWeightTo p)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro u hu
  change (∑ p : G.PathTo u.val, G.pathWeightTo (append G p u.2)) = _
  simp only [pathWeight_append]
  rw [Finset.sum_mul]

/-- The edge relation of a finite acyclic ABP is well founded. -/
theorem wellFounded_edge : WellFounded G.edge := by
  letI : Std.Irrefl (Relation.TransGen G.edge) := ⟨G.acyclic⟩
  have hsub : Subrelation G.edge (Relation.TransGen G.edge) :=
    fun h => Relation.TransGen.single h
  exact Subrelation.wf hsub
    (Finite.wellFounded_of_trans_of_irrefl _)

/-- Local path-sum equations determine all vertex values uniquely. -/
theorem polynomialAt_eq_of_local (q : G.Vertex → MvPolynomial V K)
    (hsource : q G.source = 1)
    (hlocal : ∀ v, v ≠ G.source → q v =
      ∑ u : {u : G.Vertex // G.edge u v}, q u.val * (G.label u.val v).polynomial) :
    ∀ v, q v = G.polynomialAt v := by
  intro v
  induction v using (wellFounded_edge G).induction with
  | h v ih =>
    by_cases hv : v = G.source
    · subst v
      rw [hsource, polynomialAt_source]
    · rw [hlocal v hv, polynomialAt_eq_sum_predecessors G hv]
      apply Finset.sum_congr rfl
      intro u hu
      rw [ih u.val u.property]

end Weights

end Lax461425Proofs.SymmetricABPPaths
