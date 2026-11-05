import Lax461425.CircuitProperties
import Lax461425.SymmetricABPs
import Lax461425.SymmetricFamilies
import Mathlib.Tactic

open Lax461425.CircuitProperties

/-!
The graph underlying the ABP-to-skew-circuit conversion in Section 6. There is a sum gate
for each ABP vertex and a product gate for every affine term of every edge. Zero coefficients
are retained. Input occurrences are private to their product gate; this keeps the finite gate
type independent of the universe of the coefficient field.
-/

namespace Lax461425Proofs.Section6ABPToSkew

open Lax461425.Circuits Lax461425.SymmetricABPs
open scoped Classical

noncomputable section

variable {V : Type} {K : Type*} [Fintype V]

/-- An actual ABP edge, with both endpoints retained in its index. -/
abbrev Edge (G : ABP V K) := {uv : G.Vertex × G.Vertex // G.edge uv.1 uv.2}

noncomputable instance (G : ABP V K) : Fintype (Edge G) := Fintype.ofFinite _

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The gates in the conversion. A `none` term is the constant term of an affine label. -/
inductive Gate (G : ABP V K) where
  | vertex (v : G.Vertex)
  | term (e : Edge G) (x : Option V)
  | coeff (e : Edge G) (x : Option V)
  | inputVar (e : Edge G) (x : V)
  | sourceOne

theorem Gate.vertex_eq_vertex {G : ABP V K} {u v : G.Vertex} :
    (Gate.vertex u : Gate G) = .vertex v ↔ u = v :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ rfl⟩

/-- An explicit finite enumeration of the five gate kinds. -/
def gateEquiv (G : ABP V K) : Gate G ≃
    G.Vertex ⊕ ((Edge G × Option V) ⊕ ((Edge G × Option V) ⊕ ((Edge G × V) ⊕ Unit))) where
  toFun
    | .vertex v => .inl v
    | .term e x => .inr (.inl (e, x))
    | .coeff e x => .inr (.inr (.inl (e, x)))
    | .inputVar e x => .inr (.inr (.inr (.inl (e, x))))
    | .sourceOne => .inr (.inr (.inr (.inr ())))
  invFun
    | .inl v => .vertex v
    | .inr (.inl (e, x)) => .term e x
    | .inr (.inr (.inl (e, x))) => .coeff e x
    | .inr (.inr (.inr (.inl (e, x)))) => .inputVar e x
    | .inr (.inr (.inr (.inr _))) => .sourceOne
  left_inv := by intro g; cases g <;> rfl
  right_inv := by
    intro g
    rcases g with v | (p | (p | (p | u))) <;> rfl

noncomputable instance (G : ABP V K) : Fintype (Gate G) :=
  Fintype.ofEquiv _ (gateEquiv G).symm

noncomputable instance (G : ABP V K) : DecidableEq (Gate G) := Classical.decEq _

/-- The affine coefficient used in a term. -/
def coefficient (G : ABP V K) (e : Edge G) : Option V → K
  | none => (G.label e.1.1 e.1.2).constant
  | some x => (G.label e.1.1 e.1.2).coeff x

/-- Gate labels for the translation. -/
def label [One K] (G : ABP V K) : Gate G → GateLabel V K
  | .vertex _ => .add
  | .term _ _ => .mul
  | .coeff e x => .const (coefficient G e x)
  | .inputVar _ x => .var x
  | .sourceOne => .const 1

/-- Multiplicities of wires; the conversion has no parallel wires. -/
noncomputable def wire (G : ABP V K) : Gate G → Gate G → ℕ
  | .vertex v, .sourceOne => if v = G.source then 1 else 0
  | .vertex v, .term e _ => if e.1.2 = v then 1 else 0
  | .term e _, .vertex u => if e.1.1 = u then 1 else 0
  | .term e x, .coeff f y => if e = f ∧ x = y then 1 else 0
  | .term e (some x), .inputVar f y => if e = f ∧ x = y then 1 else 0
  | _, _ => 0

/-- The predecessor relation of a finite acyclic ABP is well founded. -/
theorem wellFounded_edge (G : ABP V K) : WellFounded (fun u v => G.edge u v) := by
  letI : Std.Irrefl (Relation.TransGen G.edge) := ⟨G.acyclic⟩
  exact Subrelation.wf (fun h => Relation.TransGen.single h)
    (Finite.wellFounded_of_trans_of_irrefl _)

/-- Height above the source, used only to certify the constructed circuit is acyclic. -/
noncomputable def height (G : ABP V K) : G.Vertex → ℕ :=
  (wellFounded_edge G).fix fun v ih =>
    Finset.univ.sup fun u => if h : G.edge u v then ih u h + 1 else 0

theorem height_eq (G : ABP V K) (v : G.Vertex) :
    height G v = Finset.univ.sup (fun u => if G.edge u v then height G u + 1 else 0) :=
  WellFounded.fix_eq _ _ _

theorem height_lt (G : ABP V K) {u v : G.Vertex} (h : G.edge u v) :
    height G u < height G v := by
  have hh := Finset.le_sup (s := Finset.univ)
    (f := fun u => if G.edge u v then height G u + 1 else 0) (Finset.mem_univ u)
  rw [if_pos h, ← height_eq] at hh
  omega

/-- Three ranks per ABP level separate the sum and product gates. -/
noncomputable def rank (G : ABP V K) : Gate G → ℕ
  | .vertex v => 3 * height G v + 1
  | .term e _ => 3 * height G e.1.1 + 2
  | _ => 0

theorem rank_lt_of_wire_pos (G : ABP V K) {g h : Gate G} (hw : 0 < wire G g h) :
    rank G h < rank G g := by
  cases g with
  | vertex v =>
    cases h with
    | vertex _ => simp [wire] at hw
    | term e x =>
      have he : e.1.2 = v := by by_contra h; simp [wire, h] at hw
      have hh := height_lt G e.2
      simp only [rank]
      rw [he] at hh
      omega
    | coeff _ _ => simp [wire] at hw
    | inputVar _ _ => simp [wire] at hw
    | sourceOne => simp [rank]
  | term e x =>
    cases h with
    | vertex v =>
      have he : e.1.1 = v := by by_contra h; simp [wire, h] at hw
      simp [rank, he]
    | term _ _ => simp [wire] at hw
    | coeff _ _ => simp [rank]
    | inputVar _ _ => simp [rank]
    | sourceOne => simp [wire] at hw
  | coeff _ _ => cases h <;> simp [wire] at hw
  | inputVar _ _ => cases h <;> simp [wire] at hw
  | sourceOne => cases h <;> simp [wire] at hw

theorem wire_acyclic (G : ABP V K) (g : Gate G) :
    ¬ Relation.TransGen (fun h g => 0 < wire G g h) g g := by
  intro hh
  have hlt : ∀ {a b : Gate G},
      Relation.TransGen (fun h g => 0 < wire G g h) a b → rank G a < rank G b := by
    intro a b h
    induction h with
    | single h => exact rank_lt_of_wire_pos G h
    | tail _ h ih => exact lt_trans ih (rank_lt_of_wire_pos G h)
  exact (Nat.lt_irrefl _) (hlt hh)

theorem vertex_reaches (G : ABP V K) {u v : G.Vertex}
    (h : Relation.ReflTransGen G.edge u v) :
    Relation.ReflTransGen (fun h g => 0 < wire G g h) (.vertex u) (.vertex v) := by
  induction h with
  | refl => exact .refl
  | tail h huv ih =>
    let e : Edge G := ⟨(_, _), huv⟩
    exact ih.trans ((Relation.ReflTransGen.single (r := fun h g : Gate G => 0 < wire G g h) (show 0 < wire G (.term e none) (.vertex _) by
      simp [wire, e])).trans (Relation.ReflTransGen.single (r := fun h g : Gate G => 0 < wire G g h) (by simp [wire, e])))

theorem reaches_output (G : ABP V K) (g : Gate G) :
    Relation.ReflTransGen (fun h g => 0 < wire G g h) g (.vertex G.sink) := by
  cases g with
  | vertex v => exact vertex_reaches G (G.reaches_sink v)
  | term e x =>
    exact (Relation.ReflTransGen.single (r := fun h g : Gate G => 0 < wire G g h) (by simp [wire])).trans
      (vertex_reaches G (G.reaches_sink e.1.2))
  | coeff e x =>
    exact (Relation.ReflTransGen.single (r := fun h g : Gate G => 0 < wire G g h) (show 0 < wire G (.term e x) (.coeff e x) by
      simp [wire])).trans ((Relation.ReflTransGen.single (r := fun h g : Gate G => 0 < wire G g h) (by simp [wire])).trans
      (vertex_reaches G (G.reaches_sink e.1.2)))
  | inputVar e x =>
    exact (Relation.ReflTransGen.single (r := fun h g : Gate G => 0 < wire G g h)
      (show 0 < wire G (.term e (some x)) (.inputVar e x) by simp [wire])).trans
      ((Relation.ReflTransGen.single (r := fun h g : Gate G => 0 < wire G g h) (by simp [wire])).trans
      (vertex_reaches G (G.reaches_sink e.1.2)))
  | sourceOne =>
    exact (Relation.ReflTransGen.single (r := fun h g : Gate G => 0 < wire G g h) (show 0 < wire G (.vertex G.source) .sourceOne by
      simp [wire])).trans (vertex_reaches G (G.reaches_sink G.source))

/-- The concrete skew-circuit graph associated with an ABP. -/
noncomputable def circuit [One K] (G : ABP V K) : Circuit V K where
  Gate := Gate G
  fintypeGate := by classical exact inferInstance
  label := label G
  wire := wire G
  out := .vertex G.sink
  wire_eq_zero_of_isInput := by
    intro g h hg
    cases g <;> cases h <;> simp_all [label, GateLabel.IsInput, wire]
  acyclic := wire_acyclic G
  reaches_out := reaches_output G

/-- Every product gate has exactly one noninput child. -/
theorem circuit_isSkew [One K] (G : ABP V K) : (IsSkew (circuit G)) := by
  intro g hg
  cases g with
  | vertex _ => simp [circuit, label] at hg
  | coeff _ _ => simp [circuit, label] at hg
  | inputVar _ _ => simp [circuit, label] at hg
  | sourceOne => simp [circuit, label] at hg
  | term e x =>
    change (∑ h : Gate G, if (label G h).IsInput then 0 else wire G (.term e x) h) ≤ 1
    calc
      _ ≤ ∑ h : Gate G, if h = Gate.vertex e.1.1 then 1 else 0 := by
        apply Finset.sum_le_sum
        intro h _
        cases h <;> simp [label, GateLabel.IsInput, wire, eq_comm, Gate.vertex_eq_vertex]
      _ = 1 := by simp

end
end Lax461425Proofs.Section6ABPToSkew
