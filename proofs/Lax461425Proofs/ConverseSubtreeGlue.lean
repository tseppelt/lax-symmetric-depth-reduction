import Lax461425Proofs.ConverseSubtreeEdges

/-!
**Step 1 of the correctness proof** (see the module docstring of `ConverseCorrectness.lean`):
relating `P t γ` to a sum over admissible maps on the subtree vertex set `V t`, extending `γ`,
of the product over all edges represented at-or-below `t`:
$$
  P\,t\,\gamma = \sum_{h \supseteq \gamma \text{ admissible on } V\,t}
    \ \prod_{ab : \mathrm{rep}(a,b) \succeq t} x_{h(a),h(b)}^{F.mult\,a\,b}.
$$

This is `P_eq_sum_ExtV`, proved by well-founded recursion on `Δ - level t` (mirroring `P`'s own
recursion). The inductive step glues an admissible map on `V t` from admissible maps on each
child's `V c`, using the independence facts of `ConverseSubtree.lean`/`ConverseSubtreeEdges.lean`:
the key gluing/un-gluing pair is `glueBack`/the pointwise restriction `restrictVchild'`, shown
to be mutually inverse on the relevant Finsets (`toChildren_glueBack`, `glueBack_toChildren`),
and the distribution identity combines this with `Finset.prod_univ_sum` (product of sums =
sum over a Pi type of products) and the edge decomposition `Gval_eq_mul_prod`.
-/

namespace Lax461425Proofs

open Classical Lax461425.Circuits Lax461425.Circuits.Circuit Lax461425.HomomorphismPolynomials
open Lax461425.Forestwidth
open MvPolynomial

variable {F : Pattern} {Δ k : ℕ}

section Defs

variable (N : NormDecomp F Δ k) (n : ℕ)

/-- Restriction of an admissible map on `V t` to `bag t`. -/
noncomputable def restrictV {t : N.Node} (h : Adm F n (V N t)) : Adm F n (N.bag t) :=
  fun x => h ⟨x.1, bag_subset_V N t x.2⟩

/-- Restriction of an admissible map on `V t` to a child's subtree `V c`. -/
noncomputable def restrictVchild' {t c : N.Node} (hp : N.parent c = t) (h : Adm F n (V N t)) :
    Adm F n (V N c) :=
  fun x => h ⟨x.1, V_subset_of_child N hp x.2⟩

/-- The Finset of admissible maps on `V t` that extend `γ` on `bag t`. -/
noncomputable def ExtV (t : N.Node) (γ : Adm F n (N.bag t)) : Finset (Adm F n (V N t)) :=
  Finset.univ.filter (fun h => restrictV N n h = γ)

theorem mem_ExtV {t : N.Node} {γ : Adm F n (N.bag t)} {h : Adm F n (V N t)} :
    h ∈ ExtV N n t γ ↔ restrictV N n h = γ := by simp [ExtV]

/-- The Finset of admissible maps on `V c` that extend `δ` on `bag(parent c) ∩ bag c`. -/
noncomputable def ExtVchild (c : NonRoot N) (δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1)) :
    Finset (Adm F n (V N c.1)) :=
  Finset.univ.filter (fun h => ∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
    h ⟨x, bag_subset_V N c.1 (Finset.mem_of_mem_inter_right hx)⟩ = δ ⟨x, hx⟩)

theorem mem_ExtVchild {c : NonRoot N} {δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1)}
    {h : Adm F n (V N c.1)} :
    h ∈ ExtVchild N n c δ ↔
      ∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
        h ⟨x, bag_subset_V N c.1 (Finset.mem_of_mem_inter_right hx)⟩ = δ ⟨x, hx⟩ := by
  simp [ExtVchild]

variable {K : Type*} [CommSemiring K]

/-- The product, over all edges represented at-or-below `t`, of the corresponding variable
(raised to the edge's multiplicity), evaluated at `h`. -/
noncomputable def Gval (t : N.Node) (h : Adm F n (V N t)) : MvPolynomial (Fin n × Fin n) K :=
  ∏ ab ∈ (edgesBelow N t).attach,
    (X (h ⟨Sum.inl ab.1.1, mem_V_left N ab.2⟩, h ⟨Sum.inr ab.1.2, mem_V_right N ab.2⟩) :
      MvPolynomial (Fin n × Fin n) K) ^ F.mult ab.1.1 ab.1.2

/-- The product, over the edges represented exactly at `t`, of the corresponding variable. -/
noncomputable def GvalAt (t : N.Node) (h : Adm F n (V N t)) : MvPolynomial (Fin n × Fin n) K :=
  ∏ ab ∈ (edgesAt N t).attach,
    (X (h ⟨Sum.inl ab.1.1, bag_subset_V N t (mem_bag_left N ab.2)⟩,
          h ⟨Sum.inr ab.1.2, bag_subset_V N t (mem_bag_right N ab.2)⟩) :
      MvPolynomial (Fin n × Fin n) K) ^ F.mult ab.1.1 ab.1.2

end Defs

section EdgeDecomp

variable (N : NormDecomp F Δ k) (n : ℕ) {K : Type*} [CommSemiring K]

/-- The total edge term at `ab`, as a function of `ab` alone (not of a membership proof),
agreeing with the summand of `Gval` whenever `ab ∈ edgesBelow N t`. -/
noncomputable def edgeTerm (t : N.Node) (h : Adm F n (V N t)) (ab : F.A × F.B) :
    MvPolynomial (Fin n × Fin n) K :=
  if hab : ab ∈ edgesBelow N t then
    (X (h ⟨Sum.inl ab.1, mem_V_left N hab⟩, h ⟨Sum.inr ab.2, mem_V_right N hab⟩) :
      MvPolynomial (Fin n × Fin n) K) ^ F.mult ab.1 ab.2
  else 1

theorem Gval_eq_prod_edgeTerm (t : N.Node) (h : Adm F n (V N t)) :
    Gval N n (K := K) t h = ∏ ab ∈ edgesBelow N t, edgeTerm N n (K := K) t h ab := by
  rw [← Finset.prod_attach (edgesBelow N t) (edgeTerm N n (K := K) t h)]
  apply Finset.prod_congr rfl
  intro ab _
  show _ = edgeTerm N n (K := K) t h ab.1
  rw [edgeTerm, dif_pos ab.2]

theorem edgesBelow_subset_of_child {t c : N.Node} (hp : N.parent c = t) :
    edgesBelow N c ⊆ edgesBelow N t := by
  intro ab hab
  obtain ⟨hmult, hAbove⟩ := (mem_edgesBelow_iff N).mp hab
  exact (mem_edgesBelow_iff N).mpr ⟨hmult, above_trans N hAbove (above_of_parent_eq N hp)⟩

theorem prod_edgeTerm_edgesAt (t : N.Node) (h : Adm F n (V N t)) :
    ∏ ab ∈ edgesAt N t, edgeTerm N n (K := K) t h ab = GvalAt N n (K := K) t h := by
  rw [GvalAt, ← Finset.prod_attach (edgesAt N t) (edgeTerm N n (K := K) t h)]
  apply Finset.prod_congr rfl
  intro ab _
  show edgeTerm N n (K := K) t h ab.1 = _
  rw [edgeTerm, dif_pos (edgesAt_subset_edgesBelow N t ab.2)]

theorem prod_edgeTerm_edgesBelow_child {t c : N.Node} (hp : N.parent c = t)
    (h : Adm F n (V N t)) :
    ∏ ab ∈ edgesBelow N c, edgeTerm N n (K := K) t h ab = Gval N n (K := K) c (restrictVchild' N n hp h) := by
  rw [Gval, ← Finset.prod_attach (edgesBelow N c) (edgeTerm N n (K := K) t h)]
  apply Finset.prod_congr rfl
  intro ab _
  show edgeTerm N n (K := K) t h ab.1 = _
  rw [edgeTerm, dif_pos (edgesBelow_subset_of_child N hp ab.2)]
  rfl

/-- **The pointwise edge decomposition.** For any `h` admissible on `V t`, the product over
edges below `t` splits as the product over edges at `t` times the product over children of the
products over edges below each child. -/
theorem Gval_eq_mul_prod (t : N.Node) (h : Adm F n (V N t)) :
    Gval N n (K := K) t h = GvalAt N n (K := K) t h *
      ∏ cc ∈ (children N t).attach,
        Gval N n (K := K) cc.1.1 (restrictVchild' N n ((mem_children N).mp cc.2) h) := by
  rw [Gval_eq_prod_edgeTerm, edgesBelow_eq_union, Finset.prod_union (edgesAt_disjoint_biUnion N t),
    prod_edgeTerm_edgesAt, Finset.prod_biUnion (edgesBelow_pairwiseDisjoint_set N t),
    ← Finset.prod_attach (children N t) (fun c => ∏ i ∈ edgesBelow N c.1, edgeTerm N n (K := K) t h i)]
  congr 1
  apply Finset.prod_congr rfl
  intro cc _
  exact prod_edgeTerm_edgesBelow_child N n ((mem_children N).mp cc.2) h

end EdgeDecomp

section GlueMaps

variable (N : NormDecomp F Δ k) (n : ℕ)

/-- Data package: the (unique, as shown by `toChildren_glueBack`) child of `t` whose subtree
contains `v`, when `v ∈ V t` but `v ∉ bag t`. -/
noncomputable def childOfData {t : N.Node} (v : F.A ⊕ F.B) (hv : v ∈ V N t) (hvt : v ∉ N.bag t) :
    {c : NonRoot N // N.parent c.1 = t ∧ v ∈ V N c.1} :=
  have hex := (mem_V N).mp hv
  have htne : hex.choose ≠ t := fun h => hvt (h ▸ hex.choose_spec.2)
  have hex2 := exists_child_of_above_ne N hex.choose_spec.1 htne
  ⟨hex2.choose, hex2.choose_spec.1,
    (mem_V N).mpr ⟨hex.choose, hex2.choose_spec.2, hex.choose_spec.2⟩⟩

/-- The specific child of `t` whose subtree contains `v`, when `v ∈ V t \ bag t`. -/
noncomputable def childOf {t : N.Node} (v : F.A ⊕ F.B) (hv : v ∈ V N t) (hvt : v ∉ N.bag t) :
    NonRoot N :=
  (childOfData N v hv hvt).1

theorem childOf_parent {t : N.Node} {v : F.A ⊕ F.B} (hv : v ∈ V N t) (hvt : v ∉ N.bag t) :
    N.parent (childOf N v hv hvt).1 = t :=
  (childOfData N v hv hvt).2.1

theorem mem_V_childOf {t : N.Node} {v : F.A ⊕ F.B} (hv : v ∈ V N t) (hvt : v ∉ N.bag t) :
    v ∈ V N (childOf N v hv hvt).1 :=
  (childOfData N v hv hvt).2.2

/-- Gluing: given `γ` on `bag t` and, for every child `c` of `t`, an admissible map on `V c`,
assemble an admissible map on `V t`: use `γ` on `bag t`, and on the rest of `V t` use the
unique child whose subtree contains the point. -/
noncomputable def glueBack {t : N.Node} (γ : Adm F n (N.bag t))
    (x : (c : NonRoot N) → Adm F n (V N c.1)) : Adm F n (V N t) :=
  fun v =>
    if hvt : v.1 ∈ N.bag t then γ ⟨v.1, hvt⟩
    else x (childOf N v.1 v.2 hvt) ⟨v.1, mem_V_childOf N v.2 hvt⟩

/-- Computing `glueBack` at a point of `bag t`. -/
theorem glueBack_apply_mem_bag {t : N.Node} (γ : Adm F n (N.bag t))
    (x : (c : NonRoot N) → Adm F n (V N c.1)) {v : F.A ⊕ F.B} (hv : v ∈ V N t)
    (hvt : v ∈ N.bag t) : glueBack N n γ x ⟨v, hv⟩ = γ ⟨v, hvt⟩ := by
  unfold glueBack
  rw [dif_pos hvt]

/-- Computing `glueBack` at a point outside `bag t`. -/
theorem glueBack_apply_not_mem_bag {t : N.Node} (γ : Adm F n (N.bag t))
    (x : (c : NonRoot N) → Adm F n (V N c.1)) {v : F.A ⊕ F.B} (hv : v ∈ V N t)
    (hvt : v ∉ N.bag t) :
    glueBack N n γ x ⟨v, hv⟩ = x (childOf N v hv hvt) ⟨v, mem_V_childOf N hv hvt⟩ := by
  unfold glueBack
  rw [dif_neg hvt]

/-- Applying `x` at two provably-equal children agrees, regardless of the (proof-irrelevant)
membership witnesses used. Stated as a standalone fact (rather than inlined via `subst`) since
the point's own type otherwise depends on the child being substituted. -/
theorem x_apply_eq_of_child_eq (x : (c : NonRoot N) → Adm F n (V N c.1)) {c0 c : NonRoot N}
    (hc0 : c0 = c) {v0 : F.A ⊕ F.B} (h0 : v0 ∈ V N c0.1) (h1 : v0 ∈ V N c.1) :
    x c0 ⟨v0, h0⟩ = x c ⟨v0, h1⟩ := by
  subst hc0
  rfl

theorem restrictV_glueBack {t : N.Node} (γ : Adm F n (N.bag t))
    (x : (c : NonRoot N) → Adm F n (V N c.1)) : restrictV N n (glueBack N n γ x) = γ := by
  funext y
  exact glueBack_apply_mem_bag N n γ x (bag_subset_V N t y.2) y.2

/-- **The gluing/restriction left inverse.** If `x c` extends the right restriction of `γ`,
restricting the glued map on `V t` back to `V c` recovers `x c`. -/
theorem restrictVchild'_glueBack {t : N.Node} (γ : Adm F n (N.bag t))
    (x : (c : NonRoot N) → Adm F n (V N c.1))
    (c : NonRoot N) (hp : N.parent c.1 = t)
    (hxc : x c ∈ ExtVchild N n c (restrictFromParent N n c hp γ)) :
    restrictVchild' N n hp (glueBack N n γ x) = x c := by
  funext v
  show glueBack N n γ x ⟨v.1, V_subset_of_child N hp v.2⟩ = x c v
  by_cases hvt : v.1 ∈ N.bag t
  · rw [glueBack_apply_mem_bag N n γ x (V_subset_of_child N hp v.2) hvt]
    have hmem' : v.1 ∈ N.bag c.1 ∩ N.bag t :=
      (V_inter_bag_eq_of_parent N hp) ▸ Finset.mem_inter.mpr ⟨v.2, hvt⟩
    have hmem : v.1 ∈ N.bag (N.parent c.1) ∩ N.bag c.1 :=
      Finset.mem_inter.mpr ⟨hp ▸ hvt, (Finset.mem_inter.mp hmem').1⟩
    have hval := (mem_ExtVchild N n).mp hxc v.1 hmem
    rw [hval]
    show γ ⟨v.1, hvt⟩ = (restrictFromParent N n c hp γ) ⟨v.1, hmem⟩
    simp [restrictFromParent]
  · rw [glueBack_apply_not_mem_bag N n γ x (V_subset_of_child N hp v.2) hvt]
    set c0 := childOf N v.1 (V_subset_of_child N hp v.2) hvt with hc0def
    have hp0 : N.parent c0.1 = t := childOf_parent N (V_subset_of_child N hp v.2) hvt
    have hmem0 : v.1 ∈ V N c0.1 := mem_V_childOf N (V_subset_of_child N hp v.2) hvt
    have hc0 : c0 = c := by
      by_contra hne
      have hboth : v.1 ∈ V N c0.1 ∩ V N c.1 := Finset.mem_inter.mpr ⟨hmem0, v.2⟩
      have hne0 : c0.1 ≠ c.1 := fun h => hne (Subtype.ext h)
      exact hvt (V_inter_V_subset_bag N hp0 hp hne0 hboth)
    exact x_apply_eq_of_child_eq N n x hc0 hmem0 v.2

end GlueMaps

end Lax461425Proofs
