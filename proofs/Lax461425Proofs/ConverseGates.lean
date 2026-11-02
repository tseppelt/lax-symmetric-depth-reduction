import Lax461425.Circuits
import Lax461425Proofs.ConverseDecomposition

/-!
The gate type and circuit construction for `thm:converse` (Appendix B), built from a
`NormDecomp F Δ k`: for every node `t` and admissible map `γ : β(t) → [n]` there is a gate
`R t γ`, and for every non-root node `c` and admissible map `δ` on `β(parent c) ∩ β(c)` there is
a gate `S c δ`, together with input gates `inp i j` for the variables `x_{i,j}`. Here an
"admissible map on `S`" is represented simply as a function `↥S → Fin n`: since `S` is a finset
of `F.A ⊕ F.B`, the bipartition membership of each point already determines whether it names a
row or a column index, so there is nothing further to impose.

This file builds the gate type, the wiring, and verifies the three structural axioms of
`Circuit` (`wire_eq_zero_of_isInput`, `acyclic`, `reaches_out`). Correctness (computing
`hom K F n`), depth/size bounds, matrix symmetry and orbit size, and supports are left to later
files.
-/

namespace Lax461425Proofs

open Classical Lax461425.Circuits Lax461425.HomomorphismPolynomials Lax461425.Forestwidth

variable {F : Pattern} {Δ k : ℕ}

/-- An admissible map on a finset `S` of vertices of `F`: a function to `Fin n`, read as the
row-coordinate on `A`-vertices and the column-coordinate on `B`-vertices. -/
abbrev Adm (F : Pattern) (n : ℕ) (S : Finset (F.A ⊕ F.B)) : Type := (↥S) → Fin n

section Gates

variable (N : NormDecomp F Δ k) (n : ℕ)

noncomputable instance instDecidableEqNode : DecidableEq N.Node := Classical.decEq _

/-- The non-root nodes of `N`. -/
def NonRoot (N : NormDecomp F Δ k) : Type := {c : N.Node // c ≠ N.root}

noncomputable instance : Fintype (NonRoot N) := Subtype.fintype _

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The gates of the circuit: `R t γ` for a node `t` and admissible `γ` on `β(t)`, `S c δ` for a
non-root node `c` and admissible `δ` on `β(parent c) ∩ β(c)`, and input gates `inp i j` for the
variables `x_{i,j}`. -/
inductive CGate (N : NormDecomp F Δ k) (n : ℕ) : Type where
  | R (t : N.Node) (γ : Adm F n (N.bag t)) : CGate N n
  | S (c : NonRoot N) (δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1)) : CGate N n
  | inp (i j : Fin n) : CGate N n

/-- The gates are equivalent to a sigma/sum type, used only to transfer the `Fintype` instance.
-/
def CGate.equivSigma :
    CGate N n ≃ (Σ t : N.Node, Adm F n (N.bag t)) ⊕
      (Σ c : NonRoot N, Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1)) ⊕ (Fin n × Fin n) where
  toFun g := match g with
    | .R t γ => Sum.inl ⟨t, γ⟩
    | .S c δ => Sum.inr (Sum.inl ⟨c, δ⟩)
    | .inp i j => Sum.inr (Sum.inr (i, j))
  invFun x := match x with
    | Sum.inl ⟨t, γ⟩ => .R t γ
    | Sum.inr (Sum.inl ⟨c, δ⟩) => .S c δ
    | Sum.inr (Sum.inr (i, j)) => .inp i j
  left_inv g := by cases g <;> rfl
  right_inv x := by rcases x with ⟨t, γ⟩ | ⟨c, δ⟩ | ⟨i, j⟩ <;> rfl

noncomputable instance instFintypeCGate : Fintype (CGate N n) :=
  Fintype.ofEquiv _ (CGate.equivSigma N n).symm

/-- The label of a gate: `R`-gates are products, `S`-gates are sums, input gates carry the
corresponding variable. -/
def CGate.label {K : Type*} : CGate N n → GateLabel (Fin n × Fin n) K
  | .R _ _ => .mul
  | .S _ _ => .add
  | .inp i j => .var (i, j)

/-- The edges of `F` represented at the node `t`. -/
noncomputable def edgesAt (t : N.Node) : Finset (F.A × F.B) :=
  Finset.univ.filter (fun ab => F.mult ab.1 ab.2 ≠ 0 ∧ N.rep ab.1 ab.2 = t)

theorem mem_edgesAt_iff {t : N.Node} {ab : F.A × F.B} :
    ab ∈ edgesAt N t ↔ F.mult ab.1 ab.2 ≠ 0 ∧ N.rep ab.1 ab.2 = t := by
  simp [edgesAt]

theorem mem_bag_left {t : N.Node} {ab : F.A × F.B} (h : ab ∈ edgesAt N t) :
    Sum.inl ab.1 ∈ N.bag t := by
  obtain ⟨hmult, hrep⟩ := (mem_edgesAt_iff N).mp h
  rw [← hrep]
  exact (N.rep_mem ab.1 ab.2 hmult).1

theorem mem_bag_right {t : N.Node} {ab : F.A × F.B} (h : ab ∈ edgesAt N t) :
    Sum.inr ab.2 ∈ N.bag t := by
  obtain ⟨hmult, hrep⟩ := (mem_edgesAt_iff N).mp h
  rw [← hrep]
  exact (N.rep_mem ab.1 ab.2 hmult).2

/-- The multiplicity of the wire from `R t γ` to the input gate `inp i j`: the total
multiplicity of edges represented at `t` which `γ` sends to `(i, j)`. -/
noncomputable def wireRtoInp (t : N.Node) (γ : Adm F n (N.bag t)) (i j : Fin n) : ℕ :=
  ∑ ab ∈ (edgesAt N t).attach,
    if γ ⟨Sum.inl ab.1.1, mem_bag_left N ab.2⟩ = i ∧ γ ⟨Sum.inr ab.1.2, mem_bag_right N ab.2⟩ = j
    then F.mult ab.1.1 ab.1.2 else 0

/-- The multiplicity of the wire from `R t γ` to `S c δ`: `1` if `c` is a child of `t` and `δ`
agrees with `γ` on `β(t) ∩ β(c)`, else `0`. -/
noncomputable def wireRtoS (t : N.Node) (γ : Adm F n (N.bag t)) (c : NonRoot N)
    (δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1)) : ℕ :=
  if h : N.parent c.1 = t then
    (if ∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
        γ ⟨x, h ▸ Finset.inter_subset_left hx⟩ = δ ⟨x, hx⟩
      then 1 else 0)
  else 0

/-- The multiplicity of the wire from `S c δ` to `R t γ`: `1` if `t = c` and `γ` extends `δ`,
else `0`. -/
noncomputable def wireStoR (c : NonRoot N) (δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1))
    (t : N.Node) (γ : Adm F n (N.bag t)) : ℕ :=
  if h : c.1 = t then
    (if ∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
        γ ⟨x, h ▸ Finset.inter_subset_right hx⟩ = δ ⟨x, hx⟩
      then 1 else 0)
  else 0

/-- The wire multiplicities: `R` gates wire into represented input gates (with the
multiplicity from `F.mult`) and into the `S`-gates of their children (multiplicity `1`); `S`
gates wire into the `R`-gates of the same node that extend them (multiplicity `1`); input gates
have no children. -/
noncomputable def wire : CGate N n → CGate N n → ℕ
  | .R t γ, .inp i j => wireRtoInp N n t γ i j
  | .R t γ, .S c δ => wireRtoS N n t γ c δ
  | .S c δ, .R t γ => wireStoR N n c δ t γ
  | _, _ => 0

theorem wire_eq_zero_of_isInput_aux {K : Type*} :
    ∀ g h : CGate N n, (CGate.label (N := N) (n := n) (K := K) g).IsInput → wire N n g h = 0 := by
  intro g h hg
  cases g with
  | R t γ => simp [CGate.label, GateLabel.IsInput] at hg
  | S c δ => simp [CGate.label, GateLabel.IsInput] at hg
  | inp i j => cases h <;> simp [wire]

/-- Every point of the empty root bag gives a contradiction. -/
theorem not_mem_bag_root (x : F.A ⊕ F.B) : x ∉ N.bag N.root :=
  (N.bag_root.symm ▸ Finset.notMem_empty x : x ∉ N.bag N.root)

/-- The canonical (unique) admissible map on the empty root bag. -/
noncomputable def rootAdm : Adm F n (N.bag N.root) :=
  fun x => absurd x.2 (not_mem_bag_root N x.1)

theorem R_root_eq (γ : Adm F n (N.bag N.root)) :
    CGate.R (N := N) (n := n) N.root γ = CGate.R N.root (rootAdm N n) := by
  congr 1
  funext x
  exact absurd x.2 (not_mem_bag_root N x.1)

/-- The output gate: `R` at the root with the canonical empty-bag admissible map. -/
noncomputable def out : CGate N n := .R N.root (rootAdm N n)

/-! ### Acyclicity -/

/-- The depth-to-leaves-style measure used to order the gates: `R`-gates at a node of level `ℓ`
get `2(Δ - ℓ) + 1`, `S`-gates at a node of level `ℓ` get `2(Δ - ℓ) + 2`, and input gates get `0`.
Every wire strictly decreases this measure, which both gives acyclicity and bounds the depth of
the circuit by `2Δ + 1` (the value at the output). -/
noncomputable def mu : CGate N n → ℕ
  | .R t _ => 2 * (Δ - level N.depth_le t) + 1
  | .S c _ => 2 * (Δ - level N.depth_le c.1) + 2
  | .inp _ _ => 0

theorem mu_le (g : CGate N n) : mu N n g ≤ 2 * Δ + 1 := by
  cases g with
  | R t γ => simp only [mu]; omega
  | S c δ =>
      have hpos : 1 ≤ level N.depth_le c.1 := by
        rcases Nat.eq_zero_or_pos (level N.depth_le c.1) with h0 | hpos
        · exact absurd ((level_eq_zero_iff N.depth_le N.parent_root c.1).mp h0) c.2
        · exact hpos
      have hle : level N.depth_le c.1 ≤ Δ := level_le N.depth_le c.1
      simp only [mu]
      omega
  | inp i j => simp only [mu]; omega

/-- Every wire strictly decreases the measure `mu`. -/
theorem wire_pos_lt {g h : CGate N n} (hgh : 0 < wire N n g h) : mu N n h < mu N n g := by
  cases g with
  | R t γ =>
      cases h with
      | R t' γ' => simp [wire] at hgh
      | S c δ =>
          by_cases hpar : N.parent c.1 = t
          · have hlev : level N.depth_le c.1 = level N.depth_le t + 1 := by
              rw [← hpar]; exact level_succ N.depth_le N.parent_root c.2
            have hle : level N.depth_le t ≤ Δ := level_le N.depth_le t
            have hle2 : level N.depth_le c.1 ≤ Δ := level_le N.depth_le c.1
            simp only [mu]
            omega
          · exact absurd hgh (by simp [wire, wireRtoS, hpar])
      | inp i j => simp only [mu]; omega
  | S c δ =>
      cases h with
      | R t' γ' =>
          by_cases heq : c.1 = t'
          · have hlev : level N.depth_le c.1 = level N.depth_le t' := by rw [heq]
            simp only [mu]
            omega
          · exact absurd hgh (by simp [wire, wireStoR, heq])
      | S c' δ' => simp [wire] at hgh
      | inp i j => simp [wire] at hgh
  | inp i j => simp [wire] at hgh

/-- **Item 1 (acyclicity).** The gate-wiring of the constructed circuit has no directed cycle.
-/
theorem cgate_acyclic (g : CGate N n) :
    ¬ Relation.TransGen (fun h g => 0 < wire N n g h) g g := by
  intro hcycle
  have : IsTrans (CGate N n) (fun a b => mu N n a < mu N n b) :=
    ⟨fun _ _ _ hab hbc => lt_trans hab hbc⟩
  have hmin : Relation.TransGen (fun h g => 0 < wire N n g h) ≤ (fun a b => mu N n a < mu N n b) :=
    Relation.transGen_minimal (fun a b hab => wire_pos_lt N n hab)
  exact absurd (hmin g g hcycle) (lt_irrefl _)

/-! ### Every gate reaches the output -/

/-- The restriction of an admissible map on `β(c)` to `β(parent c) ∩ β(c)`. -/
noncomputable def restrictToS (c : NonRoot N) (γ : Adm F n (N.bag c.1)) :
    Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1) :=
  fun x => γ ⟨x.1, Finset.inter_subset_right x.2⟩

/-- An arbitrary extension of an admissible map `δ` on `β(parent c) ∩ β(c)` to one on
`β(parent c)`, filling in everything outside the intersection with `z0`. -/
noncomputable def extendAdm (c : NonRoot N) (δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1))
    (z0 : Fin n) : Adm F n (N.bag (N.parent c.1)) :=
  fun x => if hx : x.1 ∈ N.bag (N.parent c.1) ∩ N.bag c.1 then δ ⟨x.1, hx⟩ else z0

theorem wireRtoS_eq_one {t : N.Node} {γ : Adm F n (N.bag t)} {c : NonRoot N}
    {δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1)} (h : N.parent c.1 = t)
    (hmatch : ∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
      γ ⟨x, h ▸ Finset.inter_subset_left hx⟩ = δ ⟨x, hx⟩) :
    wireRtoS N n t γ c δ = 1 := by
  unfold wireRtoS
  rw [dif_pos h, if_pos hmatch]

theorem wireStoR_eq_one {c : NonRoot N} {δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1)}
    {t : N.Node} {γ : Adm F n (N.bag t)} (h : c.1 = t)
    (hmatch : ∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
      γ ⟨x, h ▸ Finset.inter_subset_right hx⟩ = δ ⟨x, hx⟩) :
    wireStoR N n c δ t γ = 1 := by
  unfold wireStoR
  rw [dif_pos h, if_pos hmatch]

theorem wireRtoS_extendAdm_self (c : NonRoot N) (δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1))
    (z0 : Fin n) :
    wireRtoS N n (N.parent c.1) (extendAdm N n c δ z0) c δ = 1 := by
  apply wireRtoS_eq_one N n rfl
  intro x hx
  show extendAdm N n c δ z0 ⟨x, Finset.inter_subset_left hx⟩ = δ ⟨x, hx⟩
  simp only [extendAdm]
  rw [dif_pos hx]

theorem wireStoR_restrictToS_self (c : NonRoot N) (γ : Adm F n (N.bag c.1)) :
    wireStoR N n c (restrictToS N n c γ) c.1 γ = 1 := by
  apply wireStoR_eq_one N n rfl
  intro x hx
  show γ ⟨x, Finset.inter_subset_right hx⟩ = restrictToS N n c γ ⟨x, hx⟩
  simp only [restrictToS]

theorem wire_RS_extendAdm_pos (c : NonRoot N) (δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1))
    (z0 : Fin n) :
    0 < wire N n (CGate.R (N.parent c.1) (extendAdm N n c δ z0)) (CGate.S c δ) := by
  show 0 < wireRtoS N n (N.parent c.1) (extendAdm N n c δ z0) c δ
  rw [wireRtoS_extendAdm_self]
  exact Nat.one_pos

theorem wire_SR_restrictToS_pos (c : NonRoot N) (γ : Adm F n (N.bag c.1)) :
    0 < wire N n (CGate.S c (restrictToS N n c γ)) (CGate.R c.1 γ) := by
  show 0 < wireStoR N n c (restrictToS N n c γ) c.1 γ
  rw [wireStoR_restrictToS_self]
  exact Nat.one_pos

/-- **Item 1 (reaches_out), `R`/`S` gates.** Every `R`-gate and every `S`-gate reaches the
output `out N n` by a chain of wires, proved by strong induction on the level of the node.
(`hn0` provides a point of `Fin n` to fill in admissible maps outside the set they are asked to
agree on.) -/
theorem reach_RS (hn0 : 0 < n) : ∀ (t : N.Node),
    (∀ γ : Adm F n (N.bag t), Relation.ReflTransGen (fun h g => 0 < wire N n g h)
        (CGate.R t γ) (out N n)) ∧
    (∀ (hroot : t ≠ N.root) (δ : Adm F n (N.bag (N.parent t) ∩ N.bag t)),
        Relation.ReflTransGen (fun h g => 0 < wire N n g h)
          (CGate.S (⟨t, hroot⟩ : NonRoot N) δ) (out N n))
  | t => by
      have hSpart : ∀ (hroot : t ≠ N.root) (δ : Adm F n (N.bag (N.parent t) ∩ N.bag t)),
          Relation.ReflTransGen (fun h g => 0 < wire N n g h)
            (CGate.S (⟨t, hroot⟩ : NonRoot N) δ) (out N n) := by
        intro hroot δ
        have hlt : level N.depth_le (N.parent t) < level N.depth_le t :=
          level_parent_lt N.depth_le N.parent_root hroot
        obtain ⟨hR, _⟩ := reach_RS hn0 (N.parent t)
        have hreachParent := hR (extendAdm N n (⟨t, hroot⟩ : NonRoot N) δ ⟨0, hn0⟩)
        refine Relation.ReflTransGen.head ?_ hreachParent
        exact wire_RS_extendAdm_pos N n (⟨t, hroot⟩ : NonRoot N) δ ⟨0, hn0⟩
      refine ⟨?_, hSpart⟩
      intro γ
      by_cases hroot : t = N.root
      · subst hroot
        rw [R_root_eq N n γ]
        exact Relation.ReflTransGen.refl
      · have hreachS := hSpart hroot (restrictToS N n (⟨t, hroot⟩ : NonRoot N) γ)
        refine Relation.ReflTransGen.head ?_ hreachS
        exact wire_SR_restrictToS_pos N n (⟨t, hroot⟩ : NonRoot N) γ
  termination_by t => level N.depth_le t
  decreasing_by assumption

/-- **Item 1 (reaches_out), input gates.** Every input gate reaches the output, using that `F`
has at least one edge. -/
theorem reach_inp (hn0 : 0 < n) (hE : ∃ a b, F.mult a b ≠ 0) (i j : Fin n) :
    Relation.ReflTransGen (fun h g => 0 < wire N n g h) (CGate.inp i j : CGate N n) (out N n) := by
  obtain ⟨a0, b0, hmult⟩ := hE
  set t0 : N.Node := N.rep a0 b0 with ht0
  have hmema : Sum.inl a0 ∈ N.bag t0 := (N.rep_mem a0 b0 hmult).1
  have hmemb : Sum.inr b0 ∈ N.bag t0 := (N.rep_mem a0 b0 hmult).2
  let γ : Adm F n (N.bag t0) := fun x =>
    if x.1 = Sum.inl a0 then i else if x.1 = Sum.inr b0 then j else ⟨0, hn0⟩
  have hreachR := (reach_RS N n hn0 t0).1 γ
  refine Relation.ReflTransGen.head ?_ hreachR
  show 0 < wireRtoInp N n t0 γ i j
  rw [wireRtoInp]
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _)
    ⟨⟨(a0, b0), (mem_edgesAt_iff N).mpr ⟨hmult, ht0 ▸ rfl⟩⟩, Finset.mem_attach _ _, ?_⟩
  have hγa : γ ⟨Sum.inl a0, hmema⟩ = i := by simp [γ]
  have hγb : γ ⟨Sum.inr b0, hmemb⟩ = j := by simp [γ]
  rw [if_pos ⟨hγa, hγb⟩]
  exact Nat.pos_of_ne_zero hmult

/-- **Item 1 (reaches_out).** Every gate reaches the output. -/
theorem reaches_out (hn0 : 0 < n) (hE : ∃ a b, F.mult a b ≠ 0) (g : CGate N n) :
    Relation.ReflTransGen (fun h g => 0 < wire N n g h) g (out N n) := by
  cases g with
  | R t γ => exact (reach_RS N n hn0 t).1 γ
  | S c δ => exact (reach_RS N n hn0 c.1).2 c.2 δ
  | inp i j => exact reach_inp N n hn0 hE i j

/-- **The circuit.** For a normalised decomposition `N` of `F` and `n ≥ 1`, with `F` having at
least one edge, the gates `R`/`S`/`inp` and their wiring form a `Circuit (Fin n × Fin n) K`,
for any ring of constants `K` (no constant gates are used). -/
noncomputable def circuit (K : Type*) (hn0 : 0 < n) (hE : ∃ a b, F.mult a b ≠ 0) :
    Circuit (Fin n × Fin n) K where
  Gate := CGate N n
  label := CGate.label N n
  wire := wire N n
  out := out N n
  wire_eq_zero_of_isInput := wire_eq_zero_of_isInput_aux N n
  acyclic := cgate_acyclic N n
  reaches_out := reaches_out N n hn0 hE

end Gates

end Lax461425Proofs
