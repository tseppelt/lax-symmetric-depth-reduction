import Lax461425.Supports

/-!
The "scaled sum" glue circuit: given `m` reduced matrix-symmetric circuits `D 0, …, D (m - 1)`
and coefficients `f 0, …, f (m - 1) : K`, build a single circuit computing
`∑ i, f i • (D i's own output polynomial)` by multiplying each block's output by a new `const
(f i)` input gate (via a new `mul`-gate `scaledG i`), and summing all of these via a new
output `add`-gate.
-/

namespace Lax461425Proofs

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports

open scoped Classical

variable {n m : ℕ} {K : Type*} [Field K] [CharZero K]

/-- The gate type of the glue circuit: a block gate for each of the `m` circuits, a `scaledG i`
(a `mul`-gate per block), a `constG i` (an input gate labelled `.const (f i)`), and a single new
output gate. -/
@[reducible] def GGate (D : Fin m → Circuit (Fin n × Fin n) K) : Type :=
  (Σ i : Fin m, (D i).Gate) ⊕ Fin m ⊕ Fin m ⊕ Unit

noncomputable instance instFintypeGGate (D : Fin m → Circuit (Fin n × Fin n) K) :
    Fintype (GGate D) := by unfold GGate; infer_instance

variable (D : Fin m → Circuit (Fin n × Fin n) K)

/-- The block gate for block `i`. -/
@[reducible] def blk (i : Fin m) (y : (D i).Gate) : GGate D := Sum.inl ⟨i, y⟩

/-- The `mul`-gate scaling block `i`'s output by `f i`. -/
@[reducible] def scaledG (i : Fin m) : GGate D := Sum.inr (Sum.inl i)

/-- The input gate labelled `.const (f i)`. -/
@[reducible] def constG (i : Fin m) : GGate D := Sum.inr (Sum.inr (Sum.inl i))

/-- The new output `add`-gate. -/
@[reducible] def outGG : GGate D := Sum.inr (Sum.inr (Sum.inr ()))

/-- The label of a glue gate. -/
noncomputable def glabel (f : Fin m → K) : GGate D → GateLabel (Fin n × Fin n) K
  | Sum.inl ⟨i, y⟩ => (D i).label y
  | Sum.inr (Sum.inl _i) => .mul
  | Sum.inr (Sum.inr (Sum.inl i)) => .const (f i)
  | Sum.inr (Sum.inr (Sum.inr ())) => .add

/-- The wire multiplicities of the glue circuit: within block `i`, the same as `D i`; a wire of
multiplicity `1` from `scaledG i` to both `blk i (D i).out` and `constG i`; a wire of
multiplicity `1` from `outGG` to every `scaledG i`; everything else `0`. -/
noncomputable def gwire : GGate D → GGate D → ℕ
  | Sum.inl ⟨i, y⟩, Sum.inl ⟨i', y'⟩ => if h : i = i' then (D i).wire y (h ▸ y') else 0
  | Sum.inr (Sum.inl i), Sum.inl ⟨i', y'⟩ =>
      if h : i = i' then (if y' = h ▸ (D i).out then 1 else 0) else 0
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inr (Sum.inl i')) => if i = i' then 1 else 0
  | Sum.inr (Sum.inr (Sum.inr ())), Sum.inr (Sum.inl _) => 1
  | _, _ => 0

theorem gwire_blk_blk (i i' : Fin m) (y : (D i).Gate) (y' : (D i').Gate) :
    gwire D (blk D i y) (blk D i' y') =
      if h : i = i' then (D i).wire y (h ▸ y') else 0 := rfl

theorem gwire_scaled_blk (i i' : Fin m) (y' : (D i').Gate) :
    gwire D (scaledG D i) (blk D i' y') =
      if h : i = i' then (if y' = h ▸ (D i).out then 1 else 0) else 0 := rfl

theorem gwire_scaled_const (i i' : Fin m) :
    gwire D (scaledG D i) (constG D i') = if i = i' then 1 else 0 := rfl

theorem gwire_out_scaled (i : Fin m) : gwire D (outGG D) (scaledG D i) = 1 := rfl

theorem gwire_blk_scaled (i : Fin m) (y : (D i).Gate) (i' : Fin m) :
    gwire D (blk D i y) (scaledG D i') = 0 := rfl

theorem gwire_blk_const (i : Fin m) (y : (D i).Gate) (i' : Fin m) :
    gwire D (blk D i y) (constG D i') = 0 := rfl

theorem gwire_blk_out (i : Fin m) (y : (D i).Gate) : gwire D (blk D i y) (outGG D) = 0 := rfl

theorem gwire_const_any (i : Fin m) (g : GGate D) : gwire D (constG D i) g = 0 := by
  rcases g with ⟨i', y'⟩ | i' | i' | ⟨⟩ <;> rfl

theorem gwire_scaled_scaled (i i' : Fin m) : gwire D (scaledG D i) (scaledG D i') = 0 := rfl

theorem gwire_scaled_out (i : Fin m) : gwire D (scaledG D i) (outGG D) = 0 := rfl

theorem gwire_out_blk (i : Fin m) (y : (D i).Gate) : gwire D (outGG D) (blk D i y) = 0 := rfl

theorem gwire_out_const (i : Fin m) : gwire D (outGG D) (constG D i) = 0 := rfl

theorem gwire_out_out : gwire D (outGG D) (outGG D) = 0 := rfl

end Lax461425Proofs
