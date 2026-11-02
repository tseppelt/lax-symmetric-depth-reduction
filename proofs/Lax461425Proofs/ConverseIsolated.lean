import Lax461425Proofs.ConverseRootMatch
import Lax461425Proofs.ConverseDepth
import Lax461425Proofs.ConverseSize
import Lax461425Proofs.ConverseSupportSize
import Lax461425Proofs.ConverseSupportDepth
import Lax461425Proofs.RigidComputes
import Lax461425Proofs.RigidDepth
import Lax461425Proofs.RigidSize
import Lax461425Proofs.RigidReduced
import Lax461425Proofs.RigidSymmetric
import Lax461425Proofs.ReducedRigid
import Lax461425Proofs.PatternsSupportBasic

/-!
Bridging the gap between `CircuitsForPatterns.exists_circuit` (which must handle patterns `F`
with possibly isolated vertices) and the converse-side gate construction of `ConverseGates.lean`
and friends (which, via `NormDecomp`, only ever produces gates supported on the *non-isolated*
vertices of `F`). See the module docstring of `CircuitsForPatterns.lean` for the overall
assembly; this file collects the reusable pieces:

* generic circuit facts (`wire_to_out_eq_zero`, `eq_out_of_path_head`, `exists_mul_decomp`);
* the sub-pattern `Fiso F` of `F` on its non-isolated vertices, and the polynomial identity
  `hom K F n = n ^ j * hom K (Fiso F) n` where `j` is the number of isolated vertices
  (`hom_eq_pow_mul_hom_Fiso`);
* transferring a `DepthDecomposition` of `F` to one of `Fiso F` (`isoDepthDecomposition`);
* a two-gate "wrapper" circuit construction (`wcircuit`) that, given a reduced matrix-symmetric
  circuit `R0` computing some polynomial `p0`, produces (for `j > 0`) a circuit computing
  `p0 * n ^ j`, adding only `2` gates below the (unchanged) output gate, without increasing depth
  beyond `max R0.depth 2`, and preserving `R0`'s support size / support depth / orbit size
  exactly.
-/

namespace Lax461425Proofs

open Classical Lax461425.Circuits Lax461425.HomomorphismPolynomials Lax461425.Forestwidth
open Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.RigidHeight Lax461425Proofs.RigidEquiv Lax461425Proofs.RigidRep
open Lax461425Proofs.RigidWeight Lax461425Proofs.RigidConstruction Lax461425Proofs.RigidComputes
open Lax461425Proofs.RigidDepth Lax461425Proofs.RigidSize Lax461425Proofs.RigidReduced
open Lax461425Proofs.RigidSymmetric Lax461425Proofs.PatternsSupportAction
open Lax461425Proofs.PatternsSupportBasic
open MvPolynomial

/-! ### Generic circuit facts -/

section GenericCircuitFacts

variable {V K : Type*} (C : Circuit V K)

/-- Height is monotone along a reachability chain (climbing towards the output). -/
theorem height_mono_of_reach {g1 g2 : C.Gate}
    (h : Relation.ReflTransGen (fun h g => 0 < C.wire g h) g1 g2) :
    height C g1 ≤ height C g2 := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih => exact le_trans ih (le_of_lt (height_child_lt C hstep))

/-- No gate wires into the output gate: the output gate has the (strict) maximum height. -/
theorem wire_to_out_eq_zero (y : C.Gate) : C.wire y C.out = 0 := by
  by_contra hne
  have hpos : 0 < C.wire y C.out := Nat.pos_of_ne_zero hne
  have h1 : height C C.out < height C y := height_lt_of_wire_pos C hpos
  have h2 : height C y ≤ height C C.out := height_mono_of_reach C (C.reaches_out y)
  omega

/-- Extracting the data of a `.mul`-labelled `ComputesAt` derivation. -/
theorem exists_mul_decomp [CommSemiring K] {g : C.Gate} {p : MvPolynomial V K}
    (hg : C.label g = .mul) (h : C.ComputesAt g p) :
    ∃ q : C.Gate → MvPolynomial V K, (∀ h', 0 < C.wire g h' → C.ComputesAt h' (q h')) ∧
      p = ∏ h', (q h') ^ C.wire g h' := by
  cases h with
  | var hl => rw [hg] at hl; cases hl
  | const hl => rw [hg] at hl; cases hl
  | add _ hl _ => rw [hg] at hl; cases hl
  | mul q hl hq => exact ⟨q, hq, rfl⟩

end GenericCircuitFacts

/-! ### The sub-pattern on non-isolated vertices -/

section IsolatedVertices

/-- The non-isolated left vertices of `F`. -/
abbrev NonIsoA (F : Pattern) : Type := {a : F.A // ∃ b, F.mult a b ≠ 0}

/-- The non-isolated right vertices of `F`. -/
abbrev NonIsoB (F : Pattern) : Type := {b : F.B // ∃ a, F.mult a b ≠ 0}

/-- The isolated left vertices of `F`. -/
abbrev IsoA (F : Pattern) : Type := {a : F.A // ¬ ∃ b, F.mult a b ≠ 0}

/-- The isolated right vertices of `F`. -/
abbrev IsoB (F : Pattern) : Type := {b : F.B // ¬ ∃ a, F.mult a b ≠ 0}

/-- The sub-pattern of `F` induced on its non-isolated vertices. -/
@[reducible] noncomputable def Fiso (F : Pattern) : Pattern where
  A := NonIsoA F
  B := NonIsoB F
  mult a b := F.mult a.1 b.1

theorem Fiso_mult (F : Pattern) (a0 : NonIsoA F) (b0 : NonIsoB F) :
    (Fiso F).mult a0 b0 = F.mult a0.1 b0.1 := rfl

/-- The number of isolated vertices of `F`. -/
noncomputable def isoJ (F : Pattern) : ℕ := Fintype.card (IsoA F) + Fintype.card (IsoB F)

theorem noIsolatedVertices_Fiso (F : Pattern) : NoIsolatedVertices (Fiso F) := by
  intro v
  cases v with
  | inl a =>
      obtain ⟨b0, hb0⟩ := a.2
      exact ⟨a, ⟨b0, ⟨a.1, hb0⟩⟩, hb0, Or.inl rfl⟩
  | inr b =>
      obtain ⟨a0, ha0⟩ := b.2
      exact ⟨⟨a0, ⟨b.1, ha0⟩⟩, b, ha0, Or.inr rfl⟩

theorem exists_edge_Fiso (F : Pattern) (hE : ∃ a b, F.mult a b ≠ 0) :
    ∃ a b, (Fiso F).mult a b ≠ 0 := by
  obtain ⟨a, b, hab⟩ := hE
  exact ⟨⟨a, b, hab⟩, ⟨b, a, hab⟩, hab⟩

/-! #### The polynomial identity -/

section HomIdentity

variable (F : Pattern) (n : ℕ)

/-- The bijection between `F.A → Fin n` and pairs of a map on the non-isolated vertices and a
map on the isolated vertices. -/
noncomputable def ΦA : (F.A → Fin n) ≃ (NonIsoA F → Fin n) × (IsoA F → Fin n) where
  toFun hA := (fun a => hA a.1, fun a => hA a.1)
  invFun p := fun a => if h : ∃ b, F.mult a b ≠ 0 then p.1 ⟨a, h⟩ else p.2 ⟨a, h⟩
  left_inv hA := by
    funext a
    by_cases h : ∃ b, F.mult a b ≠ 0 <;> simp [h]
  right_inv p := by
    apply Prod.ext
    · funext a; simp [a.2]
    · funext a; simp [a.2]

/-- The bijection between `F.B → Fin n` and pairs of a map on the non-isolated vertices and a
map on the isolated vertices. -/
noncomputable def ΦB : (F.B → Fin n) ≃ (NonIsoB F → Fin n) × (IsoB F → Fin n) where
  toFun hB := (fun b => hB b.1, fun b => hB b.1)
  invFun p := fun b => if h : ∃ a, F.mult a b ≠ 0 then p.1 ⟨b, h⟩ else p.2 ⟨b, h⟩
  left_inv hB := by
    funext b
    by_cases h : ∃ a, F.mult a b ≠ 0 <;> simp [h]
  right_inv p := by
    apply Prod.ext
    · funext b; simp [b.2]
    · funext b; simp [b.2]

theorem ΦA_symm_apply_of_nonIso (p : (NonIsoA F → Fin n) × (IsoA F → Fin n)) (a0 : NonIsoA F) :
    (ΦA F n).symm p a0.1 = p.1 a0 := by
  show (if h : ∃ b, F.mult a0.1 b ≠ 0 then p.1 ⟨a0.1, h⟩ else p.2 ⟨a0.1, h⟩) = p.1 a0
  rw [dif_pos a0.2]

theorem ΦB_symm_apply_of_nonIso (p : (NonIsoB F → Fin n) × (IsoB F → Fin n)) (b0 : NonIsoB F) :
    (ΦB F n).symm p b0.1 = p.1 b0 := by
  show (if h : ∃ a, F.mult a b0.1 ≠ 0 then p.1 ⟨b0.1, h⟩ else p.2 ⟨b0.1, h⟩) = p.1 b0
  rw [dif_pos b0.2]

variable {K : Type*} [CommSemiring K]

/-- The homomorphism-counting product only depends on the restriction of `hA`, `hB` to the
non-isolated vertices. -/
theorem prod_eq_prod_nonIso (hA : F.A → Fin n) (hB : F.B → Fin n) :
    (∏ a : F.A, ∏ b : F.B, (X (hA a, hB b) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a b) =
      ∏ a0 : NonIsoA F, ∏ b0 : NonIsoB F,
        (X (hA a0.1, hB b0.1) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a0.1 b0.1 := by
  have step1 : (∏ a : F.A, ∏ b : F.B, (X (hA a, hB b) : MvPolynomial (Fin n × Fin n) K) ^
        F.mult a b) =
      ∏ a0 : NonIsoA F, ∏ b : F.B, (X (hA a0.1, hB b) : MvPolynomial (Fin n × Fin n) K) ^
        F.mult a0.1 b := by
    have heq : (∏ a ∈ Finset.univ.filter (fun a : F.A => ∃ b, F.mult a b ≠ 0),
          ∏ b : F.B, (X (hA a, hB b) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a b) =
        ∏ a0 : NonIsoA F, ∏ b : F.B,
          (X (hA a0.1, hB b) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a0.1 b :=
      Finset.prod_subtype (Finset.univ.filter (fun a : F.A => ∃ b, F.mult a b ≠ 0)) (by simp)
        (fun a => ∏ b : F.B, (X (hA a, hB b) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a b)
    rw [← heq]
    refine (Finset.prod_subset (Finset.filter_subset _ _) (fun a _ ha => ?_)).symm
    have ha' : ¬ ∃ b, F.mult a b ≠ 0 := by simpa using ha
    apply Finset.prod_eq_one
    intro b _
    have : F.mult a b = 0 := by by_contra hc; exact ha' ⟨b, hc⟩
    rw [this, pow_zero]
  rw [step1]
  refine Finset.prod_congr rfl (fun a0 _ => ?_)
  have heq : (∏ b ∈ Finset.univ.filter (fun b : F.B => ∃ a, F.mult a b ≠ 0),
        (X (hA a0.1, hB b) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a0.1 b) =
      ∏ b0 : NonIsoB F, (X (hA a0.1, hB b0.1) : MvPolynomial (Fin n × Fin n) K) ^
        F.mult a0.1 b0.1 :=
    Finset.prod_subtype (Finset.univ.filter (fun b : F.B => ∃ a, F.mult a b ≠ 0)) (by simp)
      (fun b => (X (hA a0.1, hB b) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a0.1 b)
  rw [← heq]
  refine (Finset.prod_subset (Finset.filter_subset _ _) (fun b _ hb => ?_)).symm
  have hb' : ¬ ∃ a, F.mult a b ≠ 0 := by simpa using hb
  have : F.mult a0.1 b = 0 := by by_contra hc; exact hb' ⟨a0.1, hc⟩
  rw [this, pow_zero]

/-- Unfolding `hom K (Fiso F) n` through the identifications `(Fiso F).A = NonIsoA F`,
`(Fiso F).B = NonIsoB F`, `(Fiso F).mult a b = F.mult a.1 b.1`. -/
theorem hom_Fiso_eq : hom K (Fiso F) n = ∑ hA1 : NonIsoA F → Fin n, ∑ hB1 : NonIsoB F → Fin n,
    ∏ a0 : NonIsoA F, ∏ b0 : NonIsoB F,
      (X (hA1 a0, hB1 b0) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a0.1 b0.1 := by
  apply Finset.sum_congr rfl
  intro hA1 _
  apply Finset.sum_congr rfl
  intro hB1 _
  apply Finset.prod_congr rfl
  intro a0 _
  apply Finset.prod_congr rfl
  intro b0 _
  rw [Fiso_mult]

/-- **The polynomial identity.** `hom K F n = n ^ (isoJ F) * hom K (Fiso F) n`. -/
theorem hom_eq_pow_mul_hom_Fiso :
    hom K F n = (n : MvPolynomial (Fin n × Fin n) K) ^ (isoJ F) * hom K (Fiso F) n := by
  have hmain : hom K F n = ∑ hA1 : NonIsoA F → Fin n, ∑ hA2 : IsoA F → Fin n,
      ∑ hB1 : NonIsoB F → Fin n, ∑ hB2 : IsoB F → Fin n,
        ∏ a0 : NonIsoA F, ∏ b0 : NonIsoB F,
          (X (hA1 a0, hB1 b0) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a0.1 b0.1 := by
    show (∑ hA : F.A → Fin n, ∑ hB : F.B → Fin n,
        ∏ a : F.A, ∏ b : F.B, (X (hA a, hB b) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a b) = _
    rw [← Equiv.sum_comp (ΦA F n).symm
      (fun hA => ∑ hB : F.B → Fin n,
        ∏ a : F.A, ∏ b : F.B, (X (hA a, hB b) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a b),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun hA1 _ => Finset.sum_congr rfl (fun hA2 _ => ?_))
    rw [← Equiv.sum_comp (ΦB F n).symm
      (fun hB => ∏ a : F.A, ∏ b : F.B,
        (X (((ΦA F n).symm (hA1, hA2)) a, hB b) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a b),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun hB1 _ => Finset.sum_congr rfl (fun hB2 _ => ?_))
    rw [prod_eq_prod_nonIso F n ((ΦA F n).symm (hA1, hA2)) ((ΦB F n).symm (hB1, hB2))]
    refine Finset.prod_congr rfl (fun a0 _ => Finset.prod_congr rfl (fun b0 _ => ?_))
    rw [ΦA_symm_apply_of_nonIso F n (hA1, hA2) a0, ΦB_symm_apply_of_nonIso F n (hB1, hB2) b0]
  rw [hmain, hom_Fiso_eq]
  have hswap : (∑ hA1 : NonIsoA F → Fin n, ∑ hA2 : IsoA F → Fin n, ∑ hB1 : NonIsoB F → Fin n,
      ∑ hB2 : IsoB F → Fin n, ∏ a0 : NonIsoA F, ∏ b0 : NonIsoB F,
        (X (hA1 a0, hB1 b0) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a0.1 b0.1) =
      ∑ hA1 : NonIsoA F → Fin n, ∑ hB1 : NonIsoB F → Fin n, ∑ hA2 : IsoA F → Fin n,
        ∑ hB2 : IsoB F → Fin n, ∏ a0 : NonIsoA F, ∏ b0 : NonIsoB F,
          (X (hA1 a0, hB1 b0) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a0.1 b0.1 :=
    Finset.sum_congr rfl (fun hA1 _ => Finset.sum_comm)
  rw [hswap]
  have hconst : ∀ hA1 : NonIsoA F → Fin n, ∀ hB1 : NonIsoB F → Fin n,
      (∑ hA2 : IsoA F → Fin n, ∑ hB2 : IsoB F → Fin n,
        ∏ a0 : NonIsoA F, ∏ b0 : NonIsoB F,
          (X (hA1 a0, hB1 b0) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a0.1 b0.1) =
      (n : MvPolynomial (Fin n × Fin n) K) ^ (isoJ F) * ∏ a0 : NonIsoA F, ∏ b0 : NonIsoB F,
        (X (hA1 a0, hB1 b0) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a0.1 b0.1 := by
    intro hA1 hB1
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, smul_smul, nsmul_eq_mul]
    congr 2
    unfold isoJ
    push_cast
    ring
  simp_rw [hconst]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun hA1 _ => ?_)
  rw [Finset.mul_sum]

end HomIdentity

/-! #### Transferring a `DepthDecomposition` to the non-isolated sub-pattern -/

section DecompositionTransfer

variable {F : Pattern} {Δ k : ℕ}

/-- The inclusion of the non-isolated vertices of `F` back into the vertices of `F`. -/
def inclIso (F : Pattern) : NonIsoA F ⊕ NonIsoB F → F.A ⊕ F.B
  | Sum.inl a => Sum.inl a.1
  | Sum.inr b => Sum.inr b.1

theorem inclIso_injective (F : Pattern) : Function.Injective (inclIso F) := by
  intro x y h
  cases x with
  | inl a =>
      cases y with
      | inl a' => exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
      | inr b' => cases h
  | inr b =>
      cases y with
      | inl a' => cases h
      | inr b' => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj h))

/-- Transferring a `DepthDecomposition` of `F` to one of `Fiso F`: the tree is reused verbatim,
and the bag at each node is restricted to its non-isolated vertices. -/
noncomputable def isoDepthDecomposition (D : DepthDecomposition F Δ k) :
    DepthDecomposition (Fiso F) Δ k where
  Node := D.Node
  root := D.root
  parent := D.parent
  parent_root := D.parent_root
  depth_le := D.depth_le
  bag t := Finset.univ.filter (fun x : NonIsoA F ⊕ NonIsoB F => inclIso F x ∈ D.bag t)
  bag_root := by
    ext x
    simp [D.bag_root]
  card_bag_le t := by
    calc (Finset.univ.filter (fun x : NonIsoA F ⊕ NonIsoB F => inclIso F x ∈ D.bag t)).card
        ≤ (D.bag t).card :=
          Finset.card_le_card_of_injOn (inclIso F) (fun x hx => by simpa using hx)
            (fun x _ y _ hxy => inclIso_injective F hxy)
      _ ≤ k := D.card_bag_le t
  exists_mem_bag v := by
    obtain ⟨t, ht⟩ := D.exists_mem_bag (inclIso F v)
    exact ⟨t, by simp [ht]⟩
  exists_edge_mem_bag a b hab := by
    have hab' : F.mult a.1 b.1 ≠ 0 := hab
    obtain ⟨t, ht1, ht2⟩ := D.exists_edge_mem_bag a.1 b.1 hab'
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht2⟩⟩
  connected v t t' h1 h2 h3 h4 :=
    D.connected (inclIso F v) t t' (by simpa using h1) (by simpa using h2) (by simpa using h3)
      (by simpa using h4)

end DecompositionTransfer

end IsolatedVertices

/-! ### The pendant wrapper circuit -/

set_option genSizeOfSpec false in
/-- The two extra gates added by the wrapper: `addG` (an `add`-gate whose value is `n`) and
`constG` (the shared `const 1` input gate `addG` wires into). -/
inductive WrapGate where
  | addG
  | constG
  deriving DecidableEq

instance : Fintype WrapGate where
  elems := {WrapGate.addG, WrapGate.constG}
  complete x := by cases x <;> simp

section Wrapper

variable {n : ℕ} {K : Type*} [Field K] [CharZero K] (R0 : Circuit (Fin n × Fin n) K) (j : ℕ)

/-- The gate type of the wrapper circuit: `R0`'s own gates, plus the two new pendant gates. -/
@[reducible] def WGate := R0.Gate ⊕ WrapGate

noncomputable instance instFintypeWGate : Fintype (WGate R0) := by unfold WGate; infer_instance

/-- The label of a wrapper gate. -/
def wlabel : WGate R0 → GateLabel (Fin n × Fin n) K
  | Sum.inl x => R0.label x
  | Sum.inr .addG => .add
  | Sum.inr .constG => .const 1

/-- The wire multiplicities of the wrapper circuit: `R0`'s own wires, plus a wire of
multiplicity `j` from `R0.out` to the new `addG` gate, plus a wire of multiplicity `n` from
`addG` to `constG`. -/
noncomputable def wwire : WGate R0 → WGate R0 → ℕ
  | Sum.inl x, Sum.inl y => R0.wire x y
  | Sum.inl x, Sum.inr .addG => if x = R0.out then j else 0
  | Sum.inr .addG, Sum.inr .constG => n
  | _, _ => 0

/-- The output gate: unchanged from `R0`. -/
def wout : WGate R0 := Sum.inl R0.out

/-- The acyclicity measure: `R0`'s height (shifted by `2`) on the old part, `1` for `addG`, `0`
for `constG`. -/
noncomputable def wmu : WGate R0 → ℕ
  | Sum.inl x => height R0 x + 2
  | Sum.inr .addG => 1
  | Sum.inr .constG => 0

theorem wwire_pos_lt {g h : WGate R0} (hgh : 0 < wwire R0 j g h) : wmu R0 h < wmu R0 g := by
  cases g with
  | inl x =>
      cases h with
      | inl y =>
          have hxy : 0 < R0.wire x y := hgh
          have hht := height_lt_of_wire_pos R0 hxy
          simp only [wmu]; omega
      | inr w =>
          cases w with
          | addG => simp only [wmu]; omega
          | constG => simp only [wwire] at hgh; omega
  | inr w =>
      cases w with
      | addG =>
          cases h with
          | inl y => simp only [wwire] at hgh; omega
          | inr w' =>
              cases w' with
              | addG => simp only [wwire] at hgh; omega
              | constG => simp only [wmu]; omega
      | constG => simp only [wwire] at hgh; omega

/-- **Acyclicity of the wrapper circuit.** -/
theorem wacyclic (g : WGate R0) :
    ¬ Relation.TransGen (fun h g => 0 < wwire R0 j g h) g g := by
  intro hcycle
  have hmin : Relation.TransGen (fun h g => 0 < wwire R0 j g h) ≤
      (fun a b => wmu R0 a < wmu R0 b) :=
    Relation.transGen_minimal (fun a b hab => wwire_pos_lt R0 j hab)
  exact absurd (hmin g g hcycle) (lt_irrefl _)

/-- **No wire out of an input gate of the wrapper circuit.** -/
theorem wwire_eq_zero_of_isInput (hout : R0.label R0.out = .mul) (g h : WGate R0)
    (hg : (wlabel R0 g).IsInput) : wwire R0 j g h = 0 := by
  cases g with
  | inl x =>
      have hxinput : (R0.label x).IsInput := hg
      cases h with
      | inl y => exact R0.wire_eq_zero_of_isInput x y hxinput
      | inr w =>
          cases w with
          | addG =>
              show (if x = R0.out then j else 0) = 0
              apply if_neg
              intro hxeq
              rw [hxeq, hout] at hxinput
              exact hxinput
          | constG => rfl
  | inr w =>
      cases w with
      | addG => simp only [wlabel, GateLabel.IsInput] at hg
      | constG =>
          cases h with
          | inl y => rfl
          | inr w' => cases w' <;> rfl

/-- **Every gate of the wrapper circuit reaches the output.** -/
theorem wreaches_out (hj : 0 < j) (hn0 : 0 < n) (g : WGate R0) :
    Relation.ReflTransGen (fun h g => 0 < wwire R0 j g h) g (wout R0) := by
  cases g with
  | inl x =>
      show Relation.ReflTransGen (fun h g => 0 < wwire R0 j g h) (Sum.inl x) (Sum.inl R0.out)
      exact Relation.ReflTransGen.lift Sum.inl (fun a b hab => hab) x R0.out (R0.reaches_out x)
  | inr w =>
      have step2 : 0 < wwire R0 j (wout R0) (Sum.inr WrapGate.addG) := by
        show 0 < (if R0.out = R0.out then j else 0)
        rw [if_pos rfl]; exact hj
      cases w with
      | addG => exact Relation.ReflTransGen.head step2 Relation.ReflTransGen.refl
      | constG =>
          have step1 : 0 < wwire R0 j (Sum.inr WrapGate.addG) (Sum.inr WrapGate.constG) := hn0
          exact Relation.ReflTransGen.head step1
            (Relation.ReflTransGen.head step2 Relation.ReflTransGen.refl)

/-- **The wrapper circuit.** Given a reduced matrix-symmetric circuit `R0` with
`R0.label R0.out = .mul`, and `j, n > 0`, the pendant extension with a `j`-fold wire from
`R0.out` into a new `add`-gate, itself wired `n`-fold into a shared new `const 1` gate. -/
@[reducible] noncomputable def wcircuit (hout : R0.label R0.out = .mul) (hj : 0 < j) (hn0 : 0 < n) :
    Circuit (Fin n × Fin n) K where
  Gate := WGate R0
  label := wlabel R0
  wire := wwire R0 j
  out := wout R0
  wire_eq_zero_of_isInput := wwire_eq_zero_of_isInput R0 j hout
  acyclic := wacyclic R0 j
  reaches_out := wreaches_out R0 j hj hn0

/-- A child of a gate is never the output gate. -/
theorem child_ne_out {y x : R0.Gate} (h : 0 < R0.wire y x) : x ≠ R0.out := by
  intro hc
  rw [hc, wire_to_out_eq_zero R0] at h
  exact absurd h (lt_irrefl 0)

/-- For `y ≠ R0.out`, the weighted sum over the wrapper circuit's gates (with the pendant part
filled in by a constant `1`, irrelevant since its multiplicity is always `0`) matches the
weighted sum over `R0`'s own gates exactly. -/
theorem wsum_inl_eq (y : R0.Gate) (hyout : y ≠ R0.out)
    (qf : R0.Gate → MvPolynomial (Fin n × Fin n) K) :
    (∑ h, wwire R0 j (Sum.inl y) h •
        (Sum.elim qf (fun _ => (1 : MvPolynomial (Fin n × Fin n) K))) h) =
      ∑ x, R0.wire y x • qf x := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hz : (∑ w : WrapGate, wwire R0 j (Sum.inl y) (Sum.inr w) •
      (1 : MvPolynomial (Fin n × Fin n) K)) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    have h0 : wwire R0 j (Sum.inl y) (Sum.inr w) = 0 := by
      cases w with
      | addG => show (if y = R0.out then j else 0) = 0; rw [if_neg hyout]
      | constG => rfl
    rw [h0, zero_smul]
  rw [hz, add_zero]
  rfl

/-- The product analogue of `wsum_inl_eq`. -/
theorem wprod_inl_eq (y : R0.Gate) (hyout : y ≠ R0.out)
    (qf : R0.Gate → MvPolynomial (Fin n × Fin n) K) :
    (∏ h, (Sum.elim qf (fun _ => (1 : MvPolynomial (Fin n × Fin n) K))) h ^
        wwire R0 j (Sum.inl y) h) = ∏ x, qf x ^ R0.wire y x := by
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hz : (∏ w : WrapGate,
      (1 : MvPolynomial (Fin n × Fin n) K) ^ wwire R0 j (Sum.inl y) (Sum.inr w)) = 1 :=
    Finset.prod_eq_one (fun w _ => one_pow _)
  rw [hz, mul_one]
  rfl

set_option maxHeartbeats 1000000 in
/-- **The key `Computes` lift.** For every gate `y` of `R0` and every polynomial `p` it
computes, the corresponding wrapper gate `Sum.inl y` computes `p` unchanged if `y ≠ R0.out`, and
computes `p * n ^ j` if `y = R0.out` (absorbing the extra pendant structure). -/
theorem wcircuit_lift_computesAt (hout : R0.label R0.out = .mul) (hj : 0 < j) (hn0 : 0 < n) :
    ∀ y : R0.Gate, ∀ {p : MvPolynomial (Fin n × Fin n) K}, R0.ComputesAt y p →
      (wcircuit R0 j hout hj hn0).ComputesAt (Sum.inl y)
        (if y = R0.out then p * (n : MvPolynomial (Fin n × Fin n) K) ^ j else p) := by
  intro y
  induction y using (wellFounded_child R0).induction with
  | _ y ih =>
    intro p hp
    by_cases hyout : y = R0.out
    · subst hyout
      obtain ⟨q, hq, hpeq⟩ := exists_mul_decomp R0 hout hp
      rw [if_pos rfl]
      set Q : WGate R0 → MvPolynomial (Fin n × Fin n) K := Sum.elim q (fun w => match w with
          | WrapGate.addG => (n : MvPolynomial (Fin n × Fin n) K)
          | WrapGate.constG => 1) with hQdef
      have hchildren : ∀ h'', 0 < (wcircuit R0 j hout hj hn0).wire (Sum.inl R0.out) h'' →
          (wcircuit R0 j hout hj hn0).ComputesAt h'' (Q h'') := by
        rintro (x | w) hpos
        · have hR0x : 0 < R0.wire R0.out x := hpos
          have hihx := ih x hR0x (hq x hR0x)
          rwa [if_neg (child_ne_out R0 hR0x)] at hihx
        · cases w with
        | addG =>
            show (wcircuit R0 j hout hj hn0).ComputesAt (Sum.inr WrapGate.addG)
              (n : MvPolynomial (Fin n × Fin n) K)
            have hval : (wcircuit R0 j hout hj hn0).ComputesAt (Sum.inr WrapGate.addG)
                (∑ h, (wcircuit R0 j hout hj hn0).wire (Sum.inr WrapGate.addG) h •
                  (1 : MvPolynomial (Fin n × Fin n) K)) := by
              apply Circuit.ComputesAt.add (fun _ => (1 : MvPolynomial (Fin n × Fin n) K))
                (show (wcircuit R0 j hout hj hn0).label (Sum.inr WrapGate.addG) = .add from rfl)
              intro h' hpos'
              have hc : h' = Sum.inr WrapGate.constG := by
                by_contra hne
                have h0 : (wcircuit R0 j hout hj hn0).wire (Sum.inr WrapGate.addG) h' = 0 := by
                  cases h' with
                  | inl x => rfl
                  | inr w' => cases w' with | addG => rfl | constG => exact absurd rfl hne
                rw [h0] at hpos'
                exact absurd hpos' (by omega)
              rw [hc]
              exact Circuit.ComputesAt.const
                (show (wcircuit R0 j hout hj hn0).label (Sum.inr WrapGate.constG) = .const 1
                  from rfl)
            have hsum : (∑ h, (wcircuit R0 j hout hj hn0).wire (Sum.inr WrapGate.addG) h •
                  (1 : MvPolynomial (Fin n × Fin n) K)) = (n : MvPolynomial (Fin n × Fin n) K) := by
              rw [Finset.sum_eq_single (Sum.inr WrapGate.constG)]
              · show (n : ℕ) • (1 : MvPolynomial (Fin n × Fin n) K) =
                  (n : MvPolynomial (Fin n × Fin n) K)
                rw [nsmul_eq_mul, mul_one]
              · intro h' _ hne
                have h0 : (wcircuit R0 j hout hj hn0).wire (Sum.inr WrapGate.addG) h' = 0 := by
                  cases h' with
                  | inl x => rfl
                  | inr w' => cases w' with | addG => rfl | constG => exact absurd rfl hne
                rw [h0, zero_smul]
              · intro hnm; exact absurd (Finset.mem_univ _) hnm
            rwa [hsum] at hval
        | constG =>
            exfalso
            have h0 : (wcircuit R0 j hout hj hn0).wire (Sum.inl R0.out) (Sum.inr WrapGate.constG)
                = 0 := rfl
            rw [h0] at hpos
            exact absurd hpos (by omega)
      have hmulcomp := Circuit.ComputesAt.mul Q
        (show (wcircuit R0 j hout hj hn0).label (Sum.inl R0.out) = .mul from hout) hchildren
      have hprodeq : (∏ h : WGate R0, Q h ^ (wcircuit R0 j hout hj hn0).wire (Sum.inl R0.out) h)
          = p * (n : MvPolynomial (Fin n × Fin n) K) ^ j := by
        rw [hpeq]
        show (∏ h : R0.Gate ⊕ WrapGate, Q h ^ wwire R0 j (Sum.inl R0.out) h) =
          (∏ h', q h' ^ R0.wire R0.out h') * (n : MvPolynomial (Fin n × Fin n) K) ^ j
        rw [Fintype.prod_sum_type]
        have hleft : (∏ x : R0.Gate, Q (Sum.inl x) ^ wwire R0 j (Sum.inl R0.out) (Sum.inl x))
            = ∏ h', q h' ^ R0.wire R0.out h' := rfl
        have hright : (∏ w : WrapGate, Q (Sum.inr w) ^ wwire R0 j (Sum.inl R0.out) (Sum.inr w))
            = (n : MvPolynomial (Fin n × Fin n) K) ^ j := by
          have hWG : (Finset.univ : Finset WrapGate) = {WrapGate.addG, WrapGate.constG} := rfl
          rw [hWG, Finset.prod_insert (by decide), Finset.prod_singleton]
          show (n : MvPolynomial (Fin n × Fin n) K) ^ (if R0.out = R0.out then j else 0) *
              (1 : MvPolynomial (Fin n × Fin n) K) ^
                wwire R0 j (Sum.inl R0.out) (Sum.inr WrapGate.constG)
            = (n : MvPolynomial (Fin n × Fin n) K) ^ j
          rw [if_pos rfl]
          show (n : MvPolynomial (Fin n × Fin n) K) ^ j * (1 : MvPolynomial (Fin n × Fin n) K) ^
              (0 : ℕ) = (n : MvPolynomial (Fin n × Fin n) K) ^ j
          rw [pow_zero, mul_one]
        rw [hleft, hright]
      rw [← hprodeq]
      exact hmulcomp
    · rw [if_neg hyout]
      cases hp with
      | var hl =>
          exact Circuit.ComputesAt.var
            (show (wcircuit R0 j hout hj hn0).label (Sum.inl y) = _ from hl)
      | const hl =>
          exact Circuit.ComputesAt.const
            (show (wcircuit R0 j hout hj hn0).label (Sum.inl y) = _ from hl)
      | add qf hl hqf =>
          have hchildren : ∀ h, 0 < (wcircuit R0 j hout hj hn0).wire (Sum.inl y) h →
              (wcircuit R0 j hout hj hn0).ComputesAt h
                ((Sum.elim qf (fun _ => (1 : MvPolynomial (Fin n × Fin n) K))) h) := by
            rintro (x | w) hpos
            · have hR0x : 0 < R0.wire y x := hpos
              have hihx := ih x hR0x (hqf x hR0x)
              rwa [if_neg (child_ne_out R0 hR0x)] at hihx
            · exfalso
              have h0 : (wcircuit R0 j hout hj hn0).wire (Sum.inl y) (Sum.inr w) = 0 := by
                cases w with
                | addG => show (if y = R0.out then j else 0) = 0; rw [if_neg hyout]
                | constG => rfl
              rw [h0] at hpos
              exact absurd hpos (by omega)
          have hval := Circuit.ComputesAt.add
            (Sum.elim qf (fun _ => (1 : MvPolynomial (Fin n × Fin n) K)))
            (show (wcircuit R0 j hout hj hn0).label (Sum.inl y) = .add from hl) hchildren
          rwa [wsum_inl_eq R0 j y hyout qf] at hval
      | mul qf hl hqf =>
          have hchildren : ∀ h, 0 < (wcircuit R0 j hout hj hn0).wire (Sum.inl y) h →
              (wcircuit R0 j hout hj hn0).ComputesAt h
                ((Sum.elim qf (fun _ => (1 : MvPolynomial (Fin n × Fin n) K))) h) := by
            rintro (x | w) hpos
            · have hR0x : 0 < R0.wire y x := hpos
              have hihx := ih x hR0x (hqf x hR0x)
              rwa [if_neg (child_ne_out R0 hR0x)] at hihx
            · exfalso
              have h0 : (wcircuit R0 j hout hj hn0).wire (Sum.inl y) (Sum.inr w) = 0 := by
                cases w with
                | addG => show (if y = R0.out then j else 0) = 0; rw [if_neg hyout]
                | constG => rfl
              rw [h0] at hpos
              exact absurd hpos (by omega)
          have hval := Circuit.ComputesAt.mul
            (Sum.elim qf (fun _ => (1 : MvPolynomial (Fin n × Fin n) K)))
            (show (wcircuit R0 j hout hj hn0).label (Sum.inl y) = .mul from hl) hchildren
          rwa [wprod_inl_eq R0 j y hyout qf] at hval

/-- **The wrapper circuit computes `p0 * n ^ j`** whenever `R0.Computes p0`. -/
theorem wcircuit_computes (hout : R0.label R0.out = .mul) (hj : 0 < j) (hn0 : 0 < n)
    {p0 : MvPolynomial (Fin n × Fin n) K} (hp0 : R0.Computes p0) :
    (wcircuit R0 j hout hj hn0).Computes
      (p0 * (n : MvPolynomial (Fin n × Fin n) K) ^ j) := by
  have := wcircuit_lift_computesAt R0 j hout hj hn0 R0.out hp0
  rwa [if_pos rfl] at this

/-- Only `addG` wires into `constG`, with multiplicity `n`. -/
theorem wwire_to_constG (g : WGate R0) :
    wwire R0 j g (Sum.inr WrapGate.constG) = if g = Sum.inr WrapGate.addG then n else 0 := by
  cases g with
  | inl x => simp [wwire]
  | inr w => cases w with
    | addG => simp [wwire]
    | constG => simp [wwire]

/-- **The wrapper circuit is reduced**, provided `R0` is reduced and never labels a gate
`const`. -/
theorem wcircuit_isReduced (hout : R0.label R0.out = .mul) (hj : 0 < j) (hn0 : 0 < n)
    (hred0 : R0.IsReduced) (hnoconst : ∀ x : R0.Gate, ∀ c, R0.label x ≠ .const c) :
    (wcircuit R0 j hout hj hn0).IsReduced := by
  simp only [Circuit.IsReduced, wcircuit]
  constructor
  · rintro (x | w) (x' | w') hinput heqlabel
    · exact congrArg Sum.inl (hred0.1 x x' hinput heqlabel)
    · exfalso
      cases w' with
      | addG =>
          have hc : (wlabel R0 (Sum.inr WrapGate.addG)).IsInput := heqlabel ▸ hinput
          simp [wlabel, GateLabel.IsInput] at hc
      | constG =>
          have heqlabel' : R0.label x = GateLabel.const 1 := heqlabel
          exact hnoconst x 1 heqlabel'
    · exfalso
      cases w with
      | addG => simp [wlabel, GateLabel.IsInput] at hinput
      | constG =>
          have heqlabel' : R0.label x' = GateLabel.const 1 := heqlabel.symm
          exact hnoconst x' 1 heqlabel'
    · rcases w with _ | _ <;> rcases w' with _ | _
      · rfl
      · exfalso; simp only [wlabel, GateLabel.IsInput] at hinput
      · simp only [wlabel] at heqlabel; cases heqlabel
      · rfl
  · rintro (x | w) (x' | w') hninput heqlabel heqwire
    · have hwireeq : R0.wire x = R0.wire x' := by
        funext h'
        have hcf := congrFun heqwire (Sum.inl h')
        simpa [wwire] using hcf
      exact congrArg Sum.inl (hred0.2 x x' hninput heqlabel hwireeq)
    · exfalso
      cases w' with
      | addG =>
          have hcontra := congrFun heqwire (Sum.inr WrapGate.constG)
          rw [wwire_to_constG, wwire_to_constG, if_pos rfl] at hcontra
          have h0 : wwire R0 j (Sum.inl x) (Sum.inr WrapGate.constG) = 0 := rfl
          rw [if_neg (by simp)] at hcontra
          omega
      | constG =>
          have heqlabel' : R0.label x = GateLabel.const 1 := heqlabel
          exact hnoconst x 1 heqlabel'
    · exfalso
      cases w with
      | addG =>
          have hcontra := congrFun heqwire (Sum.inr WrapGate.constG)
          rw [wwire_to_constG, wwire_to_constG, if_pos rfl] at hcontra
          rw [if_neg (by simp)] at hcontra
          omega
      | constG =>
          have heqlabel' : R0.label x' = GateLabel.const 1 := heqlabel.symm
          exact hnoconst x' 1 heqlabel'
    · rcases w with _ | _ <;> rcases w' with _ | _
      · rfl
      · exfalso
        have hcontra := congrFun heqwire (Sum.inr WrapGate.constG)
        rw [wwire_to_constG, wwire_to_constG, if_pos rfl, if_neg (by simp)] at hcontra
        omega
      · exfalso
        have hcontra := congrFun heqwire (Sum.inr WrapGate.constG)
        rw [wwire_to_constG, wwire_to_constG, if_pos rfl, if_neg (by simp)] at hcontra
        omega
      · rfl

/-- **The wrapper circuit is matrix-symmetric**, given a family `τ` of `R0`-automorphisms
extending every `γ : Γ n` (e.g. the ones witnessing `IsMatrixSymmetric R0`). The pendant part is
fixed by every extension, using that every `R0`-automorphism fixes `R0.out`
(`extends_fixes_out`). -/
theorem wcircuit_isMatrixSymmetric (hout : R0.label R0.out = .mul) (hj : 0 < j) (hn0 : 0 < n)
    (τ : Γ n → R0.Gate ≃ R0.Gate) (hτ : ∀ γ, Extends R0 (τ γ) (actVar γ)) :
    IsMatrixSymmetric (wcircuit R0 j hout hj hn0) := by
  intro γ
  refine ⟨Equiv.sumCongr (τ γ) (Equiv.refl WrapGate), ?_, ?_⟩
  · rintro (x | w)
    · show R0.label (τ γ x) = (R0.label x).map (actVar γ)
      exact (hτ γ).1 x
    · cases w <;> rfl
  · rintro (x | w) (x' | w')
    · show wwire R0 j (Sum.inl (τ γ x)) (Sum.inl (τ γ x')) = wwire R0 j (Sum.inl x) (Sum.inl x')
      show R0.wire (τ γ x) (τ γ x') = R0.wire x x'
      exact (hτ γ).2 x x'
    · show wwire R0 j (Sum.inl (τ γ x)) (Sum.inr w') = wwire R0 j (Sum.inl x) (Sum.inr w')
      cases w' with
      | addG =>
          show (if τ γ x = R0.out then j else 0) = (if x = R0.out then j else 0)
          have hfix : τ γ R0.out = R0.out := extends_fixes_out (hτ γ)
          by_cases hx : x = R0.out
          · rw [hx, hfix]
          · have hx' : τ γ x ≠ R0.out := by
              intro hc
              exact hx ((τ γ).injective (hc.trans hfix.symm))
            rw [if_neg hx, if_neg hx']
      | constG => rfl
    · show wwire R0 j (Sum.inr w) (Sum.inl (τ γ x')) = wwire R0 j (Sum.inr w) (Sum.inl x')
      cases w <;> rfl
    · show wwire R0 j (Sum.inr w) (Sum.inr w') = wwire R0 j (Sum.inr w) (Sum.inr w')
      rfl

variable (hout : R0.label R0.out = .mul) (hj : 0 < j) (hn0 : 0 < n)

/-- Extracting the wire positivity between two consecutive indices of a path, bypassing the
`Fin.castSucc`/`Fin.succ` bookkeeping. -/
theorem wcircuit_step {m : ℕ} (p : Fin (m + 1) → WGate R0)
    (hp : (wcircuit R0 j hout hj hn0).IsPath p) (k : ℕ) (hk : k < m) :
    0 < wwire R0 j (p ⟨k, by omega⟩) (p ⟨k + 1, by omega⟩) := by
  have hcast : (⟨k, hk⟩ : Fin m).castSucc = (⟨k, by omega⟩ : Fin (m + 1)) := by
    apply Fin.ext; simp
  have hsucc : (⟨k, hk⟩ : Fin m).succ = (⟨k + 1, by omega⟩ : Fin (m + 1)) := by
    apply Fin.ext; simp
  have hstep := hp ⟨k, hk⟩
  rwa [hcast, hsucc] at hstep

/-- **Propagation.** If, at some index `i0`, the path is at a non-output `R0`-gate, it stays in
the `R0`-part (at a non-output gate) at every later index: it can never reach the pendant part
(which would require passing through `R0.out`, impossible since nothing wires into `R0.out`,
and `R0.out` itself can never recur after index `0`, so in particular never after `i0` once
`i0`'s gate already differs from `R0.out`). -/
theorem wcircuit_prop_inl_ne_out {m : ℕ} (p : Fin (m + 1) → WGate R0)
    (hp : (wcircuit R0 j hout hj hn0).IsPath p) (i0 : ℕ) (hi0 : i0 ≤ m) (x0 : R0.Gate)
    (hx0 : p ⟨i0, by omega⟩ = Sum.inl x0) (hx0ne : x0 ≠ R0.out) :
    ∀ k, i0 ≤ k → ∀ hk : k ≤ m, ∃ y, p ⟨k, by omega⟩ = Sum.inl y ∧ y ≠ R0.out := by
  intro k hik0
  induction k, hik0 using Nat.le_induction with
  | base => intro hk; exact ⟨x0, hx0, hx0ne⟩
  | succ k hik0' ih =>
      intro hk1
      obtain ⟨y, hy, hyne⟩ := ih (by omega)
      have hwirepos := wcircuit_step R0 j hout hj hn0 p hp k (by omega)
      rw [hy] at hwirepos
      rcases h2 : p ⟨k + 1, by omega⟩ with z | w
      · refine ⟨z, rfl, ?_⟩
        rw [h2] at hwirepos
        intro hzc
        rw [hzc] at hwirepos
        have : wwire R0 j (Sum.inl y) (Sum.inl R0.out) = R0.wire y R0.out := rfl
        rw [this, wire_to_out_eq_zero R0] at hwirepos
        omega
      · exfalso
        rw [h2] at hwirepos
        cases w with
        | addG =>
            have h0 : wwire R0 j (Sum.inl y) (Sum.inr WrapGate.addG) = 0 := by
              show (if y = R0.out then j else 0) = 0
              rw [if_neg hyne]
            omega
        | constG =>
            have h0 : wwire R0 j (Sum.inl y) (Sum.inr WrapGate.constG) = 0 := rfl
            omega

/-- **The wrapper circuit's depth is at most `max R0.depth 2`.** Any path either lies entirely
in the `R0`-part (giving the `R0.depth` bound) or has length at most `2` (the pendant
`addG → constG` chain, which can only be entered from index `0`, immediately after `R0.out`).
-/
theorem wcircuit_depth_le :
    (wcircuit R0 j hout hj hn0).depth ≤ max R0.depth 2 := by
  show sSup {m | ∃ p : Fin (m + 1) → WGate R0, (wcircuit R0 j hout hj hn0).IsPath p} ≤
    max R0.depth 2
  apply csSup_le'
  rintro m ⟨p, hp⟩
  by_cases hall : ∀ i, ∃ x, p i = Sum.inl x
  · choose p' hp' using hall
    have hp'path : R0.IsPath p' := by
      intro i
      have hwi := hp i
      rw [hp' i.castSucc, hp' i.succ] at hwi
      exact hwi
    have hle : m ≤ R0.depth := le_csSup (bddAbove_depth_set R0) ⟨p', hp'path⟩
    omega
  · suffices hm2 : m ≤ 2 by omega
    rcases h0 : p ⟨0, by omega⟩ with x0 | w0
    · by_cases hx0out : x0 = R0.out
      · -- p 0 = wout: the pendant part, if entered, is entered right away.
        by_contra hm2
        push_neg at hm2
        have hw1 := wcircuit_step R0 j hout hj hn0 p hp 0 (by omega)
        rw [h0, hx0out] at hw1
        rcases h1 : p ⟨1, by omega⟩ with x1 | w1
        · -- p 1 = Sum.inl x1: then x1 ≠ R0.out, propagate, contradicting ¬hall.
          have hx1out : x1 ≠ R0.out := by
            rw [h1] at hw1
            intro hc
            rw [hc] at hw1
            have : wwire R0 j (Sum.inl R0.out) (Sum.inl R0.out) = R0.wire R0.out R0.out := rfl
            rw [this, wire_to_out_eq_zero R0] at hw1
            omega
          have hprop := wcircuit_prop_inl_ne_out R0 j hout hj hn0 p hp 1 (by omega) x1 h1 hx1out
          apply hall
          intro i
          rcases Nat.lt_or_ge (i : ℕ) 1 with hi | hi
          · have hi0 : (i : ℕ) = 0 := by omega
            exact ⟨x0, by rw [show i = ⟨0, by omega⟩ from Fin.ext hi0, h0]⟩
          · obtain ⟨y, hy, _⟩ := hprop i hi (by omega)
            exact ⟨y, hy⟩
        · -- p 1 = Sum.inr w1: must be addG (the only nonzero wire out of wout), and then p 2
          -- must be constG, and the path must stop there.
          rw [h1] at hw1
          have hw1addG : w1 = WrapGate.addG := by
            cases w1 with
            | addG => rfl
            | constG => simp only [wwire] at hw1; omega
          have hw2 := wcircuit_step R0 j hout hj hn0 p hp 1 (by omega)
          rw [h1, hw1addG] at hw2
          rcases h2 : p ⟨2, by omega⟩ with x2 | w2
          · rw [h2] at hw2
            simp only [wwire] at hw2
            omega
          · rw [h2] at hw2
            have hw2constG : w2 = WrapGate.constG := by
              cases w2 with
              | addG => simp only [wwire] at hw2; omega
              | constG => rfl
            have hw3 := wcircuit_step R0 j hout hj hn0 p hp 2 (by omega)
            rw [h2, hw2constG] at hw3
            have h0' : wwire R0 j (Sum.inr WrapGate.constG) (p ⟨2 + 1, by omega⟩) = 0 := by
              rcases h3 : p ⟨2 + 1, by omega⟩ with x3 | w3
              · rfl
              · cases w3 <;> rfl
            omega
      · -- p 0 = Sum.inl x0, x0 ≠ R0.out: propagate, contradicting ¬hall.
        exfalso
        apply hall
        intro i
        obtain ⟨y, hy, _⟩ :=
          wcircuit_prop_inl_ne_out R0 j hout hj hn0 p hp 0 (by omega) x0 h0 hx0out i (by omega)
            (by omega)
        exact ⟨y, hy⟩
    · -- p 0 = Sum.inr w0.
      cases w0 with
      | addG =>
          by_contra hm2
          push_neg at hm2
          have hw1 := wcircuit_step R0 j hout hj hn0 p hp 0 (by omega)
          rw [h0] at hw1
          rcases h1 : p ⟨1, by omega⟩ with x1 | w1
          · rw [h1] at hw1; simp only [wwire] at hw1; omega
          · rw [h1] at hw1
            have hw1constG : w1 = WrapGate.constG := by
              cases w1 with
              | addG => simp only [wwire] at hw1; omega
              | constG => rfl
            have hw2 := wcircuit_step R0 j hout hj hn0 p hp 1 (by omega)
            rw [h1, hw1constG] at hw2
            have h0' : wwire R0 j (Sum.inr WrapGate.constG) (p ⟨1 + 1, by omega⟩) = 0 := by
              rcases h2 : p ⟨1 + 1, by omega⟩ with x2 | w2
              · rfl
              · cases w2 <;> rfl
            omega
      | constG =>
          by_contra hm2
          push_neg at hm2
          have hw1 := wcircuit_step R0 j hout hj hn0 p hp 0 (by omega)
          rw [h0] at hw1
          simp only [wwire] at hw1
          omega

/-- **The wrapper circuit's size.** Exactly `R0.size + 2 + j + n`: the `2` new gates, the `j`
new wires from `R0.out` into `addG`, and the `n` new wires from `addG` into `constG`. -/
theorem wcircuit_size_eq :
    (wcircuit R0 j hout hj hn0).size = R0.size + 2 + j + n := by
  show Fintype.card (WGate R0) + ∑ g : WGate R0, ∑ h : WGate R0, wwire R0 j g h =
    R0.size + 2 + j + n
  have hcard : Fintype.card (WGate R0) = Fintype.card R0.Gate + 2 := by
    show Fintype.card (R0.Gate ⊕ WrapGate) = _
    rw [Fintype.card_sum]
    rfl
  have hsum : (∑ g : WGate R0, ∑ h : WGate R0, wwire R0 j g h) =
      (∑ x : R0.Gate, ∑ y : R0.Gate, R0.wire x y) + j + n := by
    rw [Fintype.sum_sum_type]
    have hleft : (∑ x : R0.Gate, ∑ h : WGate R0, wwire R0 j (Sum.inl x) h) =
        (∑ x : R0.Gate, ∑ y : R0.Gate, R0.wire x y) + j := by
      have hstep : ∀ x : R0.Gate, (∑ h : WGate R0, wwire R0 j (Sum.inl x) h) =
          (∑ y : R0.Gate, R0.wire x y) + (if x = R0.out then j else 0) := by
        intro x
        rw [Fintype.sum_sum_type]
        have hr : (∑ w : WrapGate, wwire R0 j (Sum.inl x) (Sum.inr w)) =
            (if x = R0.out then j else 0) := by
          rw [show (Finset.univ : Finset WrapGate) = {WrapGate.addG, WrapGate.constG} from rfl,
            Finset.sum_insert (by decide), Finset.sum_singleton]
          show (if x = R0.out then j else 0) + wwire R0 j (Sum.inl x) (Sum.inr WrapGate.constG)
            = (if x = R0.out then j else 0)
          rw [show wwire R0 j (Sum.inl x) (Sum.inr WrapGate.constG) = 0 from rfl, add_zero]
        have hl : (∑ y : R0.Gate, wwire R0 j (Sum.inl x) (Sum.inl y)) =
            ∑ y : R0.Gate, R0.wire x y := rfl
        rw [hl, hr]
      rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_ite_eq' Finset.univ R0.out (fun _ => j)]
      simp
    have hright : (∑ w : WrapGate, ∑ h : WGate R0, wwire R0 j (Sum.inr w) h) = n := by
      rw [show (Finset.univ : Finset WrapGate) = {WrapGate.addG, WrapGate.constG} from rfl,
        Finset.sum_insert (by decide), Finset.sum_singleton]
      have h1 : (∑ h : WGate R0, wwire R0 j (Sum.inr WrapGate.addG) h) = n := by
        rw [Fintype.sum_sum_type]
        have hl : (∑ x : R0.Gate, wwire R0 j (Sum.inr WrapGate.addG) (Sum.inl x)) = 0 :=
          Finset.sum_eq_zero (fun x _ => rfl)
        have hr : (∑ w : WrapGate, wwire R0 j (Sum.inr WrapGate.addG) (Sum.inr w)) = n := by
          rw [show (Finset.univ : Finset WrapGate) = {WrapGate.addG, WrapGate.constG} from rfl,
            Finset.sum_insert (by decide), Finset.sum_singleton]
          show wwire R0 j (Sum.inr WrapGate.addG) (Sum.inr WrapGate.addG) + n = n
          rw [show wwire R0 j (Sum.inr WrapGate.addG) (Sum.inr WrapGate.addG) = 0 from rfl,
            zero_add]
        rw [hl, hr]; ring
      have h2 : (∑ h : WGate R0, wwire R0 j (Sum.inr WrapGate.constG) h) = 0 := by
        rw [Fintype.sum_sum_type]
        have hl : (∑ x : R0.Gate, wwire R0 j (Sum.inr WrapGate.constG) (Sum.inl x)) = 0 :=
          Finset.sum_eq_zero (fun x _ => rfl)
        have hr : (∑ w : WrapGate, wwire R0 j (Sum.inr WrapGate.constG) (Sum.inr w)) = 0 :=
          Finset.sum_eq_zero (fun w _ => by cases w <;> rfl)
        rw [hl, hr]
      omega
    rw [hleft, hright]
  show Fintype.card (WGate R0) + ∑ g : WGate R0, ∑ h : WGate R0, wwire R0 j g h = _
  rw [hcard, hsum]
  show Fintype.card R0.Gate + 2 + ((∑ x : R0.Gate, ∑ y : R0.Gate, R0.wire x y) + j + n) =
    R0.size + 2 + j + n
  show _ = (Fintype.card R0.Gate + ∑ x, ∑ y, R0.wire x y) + 2 + j + n
  ring

/-- **The wrapper circuit's size bound.** -/
theorem wcircuit_size_le (S : ℕ) (hS : R0.size + 2 + j + n ≤ S) :
    (wcircuit R0 j hout hj hn0).size ≤ S := by
  rw [wcircuit_size_eq]; exact hS

/-- Backward step: if index `k + 1` is an old gate, so is index `k`. -/
theorem wcircuit_inl_backward {m : ℕ} (p : Fin (m + 1) → WGate R0)
    (hp : (wcircuit R0 j hout hj hn0).IsPath p) (k : ℕ) (hk : k < m) (x : R0.Gate)
    (hx : p ⟨k + 1, by omega⟩ = Sum.inl x) : ∃ y, p ⟨k, by omega⟩ = Sum.inl y := by
  have hwire := wcircuit_step R0 j hout hj hn0 p hp k hk
  rw [hx] at hwire
  rcases h : p ⟨k, by omega⟩ with y | w
  · exact ⟨y, rfl⟩
  · exfalso
    rw [h] at hwire
    cases w with
    | addG => simp only [wwire] at hwire; omega
    | constG => simp only [wwire] at hwire; omega

/-- Chained backward propagation: if index `i0` is an old gate, so is every earlier index. -/
theorem wcircuit_inl_backward_chain {m : ℕ} (p : Fin (m + 1) → WGate R0)
    (hp : (wcircuit R0 j hout hj hn0).IsPath p) :
    ∀ i0 : ℕ, ∀ hi0 : i0 ≤ m, ∀ x0 : R0.Gate, p ⟨i0, by omega⟩ = Sum.inl x0 →
      ∀ k, ∀ hk : k ≤ i0, ∃ y, p ⟨k, by omega⟩ = Sum.inl y := by
  intro i0
  induction i0 with
  | zero =>
      intro _ x0 hx0 k hk
      have hk0 : k = 0 := by omega
      subst hk0
      exact ⟨x0, hx0⟩
  | succ i0 ih =>
      intro hi0 x0 hx0 k hk
      rcases Nat.lt_or_ge k (i0 + 1) with hklt | hkge
      · obtain ⟨y, hy⟩ := wcircuit_inl_backward R0 j hout hj hn0 p hp i0 (by omega) x0 hx0
        exact ih (by omega) y hy k (by omega)
      · have hkeq : k = i0 + 1 := by omega
        subst hkeq
        exact ⟨x0, hx0⟩

/-- The explicit automorphism of the wrapper circuit extending `γ`, built from `τ γ` on the old
part and fixed on the pendant part (the same witness used in `wcircuit_isMatrixSymmetric`). -/
noncomputable def wcircuit_auto (τ : Γ n → R0.Gate ≃ R0.Gate) (γ : Γ n) : WGate R0 ≃ WGate R0 :=
  Equiv.sumCongr (τ γ) (Equiv.refl WrapGate)

theorem wcircuit_auto_extends (τ : Γ n → R0.Gate ≃ R0.Gate)
    (hτ : ∀ γ, Extends R0 (τ γ) (actVar γ)) (γ : Γ n) :
    Extends (wcircuit R0 j hout hj hn0) (wcircuit_auto R0 τ γ) (actVar γ) := by
  refine ⟨?_, ?_⟩
  · rintro (x | w)
    · show R0.label (τ γ x) = (R0.label x).map (actVar γ)
      exact (hτ γ).1 x
    · cases w <;> rfl
  · rintro (x | w) (x' | w')
    · show wwire R0 j (Sum.inl (τ γ x)) (Sum.inl (τ γ x')) = wwire R0 j (Sum.inl x) (Sum.inl x')
      show R0.wire (τ γ x) (τ γ x') = R0.wire x x'
      exact (hτ γ).2 x x'
    · show wwire R0 j (Sum.inl (τ γ x)) (Sum.inr w') = wwire R0 j (Sum.inl x) (Sum.inr w')
      cases w' with
      | addG =>
          show (if τ γ x = R0.out then j else 0) = (if x = R0.out then j else 0)
          have hfix : τ γ R0.out = R0.out := extends_fixes_out (hτ γ)
          by_cases hx : x = R0.out
          · rw [hx, hfix]
          · have hx' : τ γ x ≠ R0.out := by
              intro hc
              exact hx ((τ γ).injective (hc.trans hfix.symm))
            rw [if_neg hx, if_neg hx']
      | constG => rfl
    · show wwire R0 j (Sum.inr w) (Sum.inl (τ γ x')) = wwire R0 j (Sum.inr w) (Sum.inl x')
      cases w <;> rfl
    · show wwire R0 j (Sum.inr w) (Sum.inr w') = wwire R0 j (Sum.inr w) (Sum.inr w')
      rfl

/-- `σOf hrigD γ` agrees with `σOf hrig0 γ` on the old part. -/
theorem wcircuit_σOf_inl (τ : Γ n → R0.Gate ≃ R0.Gate) (hτ : ∀ γ, Extends R0 (τ γ) (actVar γ))
    (hrig0 : IsRigid R0) (hrigD : IsRigid (wcircuit R0 j hout hj hn0)) (γ : Γ n) (x : R0.Gate) :
    σOf hrigD γ (Sum.inl x) = Sum.inl (σOf hrig0 γ x) := by
  rw [← σOf_unique hrigD (wcircuit_auto_extends R0 j hout hj hn0 τ hτ γ)]
  show Sum.inl (τ γ x) = Sum.inl (σOf hrig0 γ x)
  rw [σOf_unique hrig0 (hτ γ)]

/-- `σOf hrigD γ` fixes every pendant gate. -/
theorem wcircuit_σOf_inr (τ : Γ n → R0.Gate ≃ R0.Gate) (hτ : ∀ γ, Extends R0 (τ γ) (actVar γ))
    (hrigD : IsRigid (wcircuit R0 j hout hj hn0)) (γ : Γ n) (w : WrapGate) :
    σOf hrigD γ (Sum.inr w) = Sum.inr w := by
  rw [← σOf_unique hrigD (wcircuit_auto_extends R0 j hout hj hn0 τ hτ γ)]
  rfl

theorem wcircuit_gateStabilizer_inl (τ : Γ n → R0.Gate ≃ R0.Gate)
    (hτ : ∀ γ, Extends R0 (τ γ) (actVar γ)) (hrig0 : IsRigid R0)
    (hrigD : IsRigid (wcircuit R0 j hout hj hn0)) (x : R0.Gate) :
    gateStabilizer hrigD (Sum.inl x) = gateStabilizer hrig0 x := by
  ext γ
  rw [mem_gateStabilizer_iff, mem_gateStabilizer_iff,
    wcircuit_σOf_inl R0 j hout hj hn0 τ hτ hrig0 hrigD γ x]
  exact ⟨fun h => Sum.inl_injective h, fun h => congrArg Sum.inl h⟩

theorem wcircuit_gateStabilizer_inr (τ : Γ n → R0.Gate ≃ R0.Gate)
    (hτ : ∀ γ, Extends R0 (τ γ) (actVar γ)) (hrigD : IsRigid (wcircuit R0 j hout hj hn0))
    (w : WrapGate) : gateStabilizer hrigD (Sum.inr w) = ⊤ := by
  ext γ
  simp only [Subgroup.mem_top, iff_true, mem_gateStabilizer_iff]
  exact wcircuit_σOf_inr R0 j hout hj hn0 τ hτ hrigD γ w

theorem wcircuit_isSupport_inl_iff (τ : Γ n → R0.Gate ≃ R0.Gate)
    (hτ : ∀ γ, Extends R0 (τ γ) (actVar γ)) (hrig0 : IsRigid R0)
    (hrigD : IsRigid (wcircuit R0 j hout hj hn0)) (x : R0.Gate) (S : Set (Fin n ⊕ Fin n)) :
    IsSupport (wcircuit R0 j hout hj hn0) (Sum.inl x) S ↔ IsSupport R0 x S := by
  rw [isSupport_iff_fixingSubgroup_le hrigD, isSupport_iff_fixingSubgroup_le hrig0,
    wcircuit_gateStabilizer_inl R0 j hout hj hn0 τ hτ hrig0 hrigD x]

theorem wcircuit_isSupport_inr (τ : Γ n → R0.Gate ≃ R0.Gate)
    (hτ : ∀ γ, Extends R0 (τ γ) (actVar γ)) (hrigD : IsRigid (wcircuit R0 j hout hj hn0))
    (w : WrapGate) (S : Set (Fin n ⊕ Fin n)) :
    IsSupport (wcircuit R0 j hout hj hn0) (Sum.inr w) S := by
  rw [isSupport_iff_fixingSubgroup_le hrigD,
    wcircuit_gateStabilizer_inr R0 j hout hj hn0 τ hτ hrigD w]
  exact le_top

/-- **`supportSize` is unaffected by the pendant extension.** -/
theorem wcircuit_supportSize_eq (τ : Γ n → R0.Gate ≃ R0.Gate)
    (hτ : ∀ γ, Extends R0 (τ γ) (actVar γ)) (hrig0 : IsRigid R0)
    (hrigD : IsRigid (wcircuit R0 j hout hj hn0)) :
    supportSize (wcircuit R0 j hout hj hn0) = supportSize R0 := by
  show sInf {k | ∀ g : WGate R0, ∃ S, IsSupport (wcircuit R0 j hout hj hn0) g S ∧ S.ncard ≤ k} =
    sInf {k | ∀ x : R0.Gate, ∃ S, IsSupport R0 x S ∧ S.ncard ≤ k}
  congr 1
  ext k
  constructor
  · intro hk x
    obtain ⟨S, hS, hSc⟩ := hk (Sum.inl x)
    exact ⟨S, (wcircuit_isSupport_inl_iff R0 j hout hj hn0 τ hτ hrig0 hrigD x S).mp hS, hSc⟩
  · intro hk g
    cases g with
    | inl x =>
        obtain ⟨S, hS, hSc⟩ := hk x
        exact ⟨S, (wcircuit_isSupport_inl_iff R0 j hout hj hn0 τ hτ hrig0 hrigD x S).mpr hS, hSc⟩
    | inr w =>
        refine ⟨∅, wcircuit_isSupport_inr R0 j hout hj hn0 τ hτ hrigD w ∅, ?_⟩
        simp

/-- **`supportSize` bound for the wrapper circuit.** -/
theorem wcircuit_supportSize_le (τ : Γ n → R0.Gate ≃ R0.Gate)
    (hτ : ∀ γ, Extends R0 (τ γ) (actVar γ)) (hrig0 : IsRigid R0)
    (hrigD : IsRigid (wcircuit R0 j hout hj hn0)) {k0 : ℕ} (hss0 : supportSize R0 ≤ k0) :
    supportSize (wcircuit R0 j hout hj hn0) ≤ k0 := by
  rw [wcircuit_supportSize_eq R0 j hout hj hn0 τ hτ hrig0 hrigD]
  exact hss0

/-- **`orbitSize` bound for the wrapper circuit.** -/
theorem wcircuit_orbitSize_le (τ : Γ n → R0.Gate ≃ R0.Gate)
    (hτ : ∀ γ, Extends R0 (τ γ) (actVar γ)) (hrig0 : IsRigid R0)
    (hrigD : IsRigid (wcircuit R0 j hout hj hn0)) {k0 : ℕ} (hss0 : supportSize R0 ≤ k0) :
    orbitSize (wcircuit R0 j hout hj hn0) ≤ n ^ k0 :=
  orbitSize_le_pow_of_supportSize_le hrigD hn0
    (wcircuit_supportSize_le R0 j hout hj hn0 τ hτ hrig0 hrigD hss0)

theorem wcircuit_minSupport_inl_eq (τ : Γ n → R0.Gate ≃ R0.Gate)
    (hτ : ∀ γ, Extends R0 (τ γ) (actVar γ)) (hrig0 : IsRigid R0)
    (hrigD : IsRigid (wcircuit R0 j hout hj hn0)) (x : R0.Gate) :
    minSupport (wcircuit R0 j hout hj hn0) (Sum.inl x) = minSupport R0 x := by
  ext p0
  show (∀ S, IsSupport (wcircuit R0 j hout hj hn0) (Sum.inl x) S →
      S.ncard ≤ supportSize (wcircuit R0 j hout hj hn0) → p0 ∈ S) ↔
    (∀ S, IsSupport R0 x S → S.ncard ≤ supportSize R0 → p0 ∈ S)
  rw [wcircuit_supportSize_eq R0 j hout hj hn0 τ hτ hrig0 hrigD]
  constructor
  · intro h S hS hSc
    exact h S ((wcircuit_isSupport_inl_iff R0 j hout hj hn0 τ hτ hrig0 hrigD x S).mpr hS) hSc
  · intro h S hS hSc
    exact h S ((wcircuit_isSupport_inl_iff R0 j hout hj hn0 τ hτ hrig0 hrigD x S).mp hS) hSc

theorem wcircuit_minSupport_inr_eq (τ : Γ n → R0.Gate ≃ R0.Gate)
    (hτ : ∀ γ, Extends R0 (τ γ) (actVar γ)) (hrigD : IsRigid (wcircuit R0 j hout hj hn0))
    (w : WrapGate) : minSupport (wcircuit R0 j hout hj hn0) (Sum.inr w) = ∅ := by
  apply Set.subset_empty_iff.mp
  intro p0 hp0
  exact hp0 ∅ (wcircuit_isSupport_inr R0 j hout hj hn0 τ hτ hrigD w ∅) (by simp)

/-- **Every gate of a `¬hall` path has empty minimal support.** -/
theorem wcircuit_minSupport_eq_empty_of_not_hall (τ : Γ n → R0.Gate ≃ R0.Gate)
    (hτ : ∀ γ, Extends R0 (τ γ) (actVar γ)) (hrig0 : IsRigid R0)
    (hrigD : IsRigid (wcircuit R0 j hout hj hn0)) {m : ℕ} (p : Fin (m + 1) → WGate R0)
    (hp : (wcircuit R0 j hout hj hn0).IsPath p) (hall : ¬ ∀ i, ∃ x, p i = Sum.inl x) :
    ∀ i : Fin (m + 1), minSupport (wcircuit R0 j hout hj hn0) (p i) = ∅ := by
  intro i
  rcases hi : p i with x | w
  · by_cases hxout : x = R0.out
    · rw [hxout, wcircuit_minSupport_inl_eq R0 j hout hj hn0 τ hτ hrig0 hrigD]
      exact minSupport_out R0
    · exfalso
      apply hall
      intro i'
      rcases Nat.lt_or_ge (i' : ℕ) (i : ℕ) with hlt | hge
      · obtain ⟨y, hy⟩ := wcircuit_inl_backward_chain R0 j hout hj hn0 p hp i (by omega) x
          (by rw [show (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = i from Fin.ext rfl]; exact hi)
          i' (by omega)
        exact ⟨y, by rwa [show (⟨(i' : ℕ), by omega⟩ : Fin (m + 1)) = i' from Fin.ext rfl] at hy⟩
      · obtain ⟨y, hy, _⟩ := wcircuit_prop_inl_ne_out R0 j hout hj hn0 p hp i (by omega) x
          (by rw [show (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = i from Fin.ext rfl]; exact hi)
          hxout i' hge (by omega)
        exact ⟨y, by rwa [show (⟨(i' : ℕ), by omega⟩ : Fin (m + 1)) = i' from Fin.ext rfl] at hy⟩
  · exact wcircuit_minSupport_inr_eq R0 j hout hj hn0 τ hτ hrigD w

/-- **The wrapper circuit's support-changing count on any path is bounded by `Δ0`**, given that
`R0`'s is. Either the path lies entirely in the old part (reducing directly to `R0`'s bound via
the `minSupport` correspondence), or every gate it visits has empty minimal support (so no step
is ever support-changing). -/
theorem wcircuit_supportChanges_le (τ : Γ n → R0.Gate ≃ R0.Gate)
    (hτ : ∀ γ, Extends R0 (τ γ) (actVar γ)) (hrig0 : IsRigid R0)
    (hrigD : IsRigid (wcircuit R0 j hout hj hn0)) {Δ0 : ℕ}
    (hΔ0 : ∀ {m : ℕ} (p' : Fin (m + 1) → R0.Gate), R0.IsPath p' → supportChanges R0 p' ≤ Δ0)
    {m : ℕ} (p : Fin (m + 1) → WGate R0) (hp : (wcircuit R0 j hout hj hn0).IsPath p) :
    supportChanges (wcircuit R0 j hout hj hn0) p ≤ Δ0 := by
  by_cases hall : ∀ i, ∃ x, p i = Sum.inl x
  · choose p' hp' using hall
    have hp'path : R0.IsPath p' := by
      intro i
      have hwi := hp i
      rw [hp' i.castSucc, hp' i.succ] at hwi
      exact hwi
    have heq : supportChanges (wcircuit R0 j hout hj hn0) p = supportChanges R0 p' := by
      show {i : Fin m | ¬ minSupport (wcircuit R0 j hout hj hn0) (p i.succ) ⊆
          minSupport (wcircuit R0 j hout hj hn0) (p i.castSucc)}.ncard =
        {i : Fin m | ¬ minSupport R0 (p' i.succ) ⊆ minSupport R0 (p' i.castSucc)}.ncard
      congr 1
      ext i
      simp only [Set.mem_setOf_eq]
      rw [hp' i.succ, hp' i.castSucc, wcircuit_minSupport_inl_eq R0 j hout hj hn0 τ hτ hrig0 hrigD,
        wcircuit_minSupport_inl_eq R0 j hout hj hn0 τ hτ hrig0 hrigD]
    rw [heq]
    exact hΔ0 p' hp'path
  · have hallempty := wcircuit_minSupport_eq_empty_of_not_hall R0 j hout hj hn0 τ hτ hrig0 hrigD
      p hp hall
    have : supportChanges (wcircuit R0 j hout hj hn0) p = 0 := by
      show {i : Fin m | ¬ minSupport (wcircuit R0 j hout hj hn0) (p i.succ) ⊆
          minSupport (wcircuit R0 j hout hj hn0) (p i.castSucc)}.ncard = 0
      rw [Set.ncard_eq_zero (by exact Set.toFinite _)]
      ext i
      simp [hallempty i.succ, hallempty i.castSucc]
    omega

/-- **`supportDepth` bound for the wrapper circuit.** -/
theorem wcircuit_supportDepth_le (τ : Γ n → R0.Gate ≃ R0.Gate)
    (hτ : ∀ γ, Extends R0 (τ γ) (actVar γ)) (hrig0 : IsRigid R0)
    (hrigD : IsRigid (wcircuit R0 j hout hj hn0)) {k0 Δ0 : ℕ} (hss0 : supportSize R0 ≤ k0)
    (hn2 : 2 * k0 < n)
    (hΔ0 : ∀ {m : ℕ} (p' : Fin (m + 1) → R0.Gate), R0.IsPath p' → supportChanges R0 p' ≤ Δ0) :
    supportDepth (wcircuit R0 j hout hj hn0) ≤ Δ0 := by
  have hssD : supportSize (wcircuit R0 j hout hj hn0) ≤ k0 :=
    wcircuit_supportSize_le R0 j hout hj hn0 τ hτ hrig0 hrigD hss0
  show (if 2 * supportSize (wcircuit R0 j hout hj hn0) < n then
      sSup {c | ∃ (m : ℕ) (p : Fin (m + 1) → WGate R0),
        (wcircuit R0 j hout hj hn0).IsPath p ∧ supportChanges (wcircuit R0 j hout hj hn0) p = c}
    else (wcircuit R0 j hout hj hn0).depth) ≤ Δ0
  rw [if_pos (by omega)]
  apply csSup_le'
  rintro c ⟨m, p, hp, hc⟩
  rw [← hc]
  exact wcircuit_supportChanges_le R0 j hout hj hn0 τ hτ hrig0 hrigD hΔ0 p hp

end Wrapper

end Lax461425Proofs
