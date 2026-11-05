import Lax461425Proofs.SymmetricABPBasic

/-!
A finite layered-program constructor for the path-decomposition ABP. All vertices must
have a predecessor/successor when their layer is not an endpoint, ensuring that the
resulting graph has exactly the stipulated source and sink.
-/

namespace Lax461425Proofs.Section6LayeredABP

open Lax461425.SymmetricABPs

structure Program (V K : Type*) where
  length : ℕ
  State : Type
  [fintypeState : Fintype State]
  [decEqState : DecidableEq State]
  valid : Fin (length + 1) → State → Prop
  [decValid : ∀ i, DecidablePred (valid i)]
  start : State
  finish : State
  valid_start : valid 0 start
  valid_finish : valid (Fin.last length) finish
  first_unique : ∀ s, valid 0 s → s = start
  last_unique : ∀ s, valid (Fin.last length) s → s = finish
  step : Fin (length + 1) → State → State → Prop
  [decStep : ∀ i, DecidableRel (step i)]
  label : Fin (length + 1) → State → State → AffineForm V K
  predecessor : ∀ (i : Fin (length + 1)) s, valid i s → 0 < i.val →
    ∃ (j : Fin (length + 1)) (t : State), j.val + 1 = i.val ∧ valid j t ∧ step j t s
  successor : ∀ (i : Fin (length + 1)) s, valid i s → i.val < length →
    ∃ (j : Fin (length + 1)) (t : State), i.val + 1 = j.val ∧ valid j t ∧ step i s t

attribute [instance] Program.fintypeState Program.decEqState Program.decValid Program.decStep

variable {V K : Type*} (P : Program V K)

abbrev Vertex := {p : Fin (P.length + 1) × P.State // P.valid p.1 p.2}

def source : Vertex P := ⟨(0, P.start), P.valid_start⟩
def sink : Vertex P := ⟨(Fin.last P.length, P.finish), P.valid_finish⟩

def edge (u v : Vertex P) : Prop :=
  u.1.1.val + 1 = v.1.1.val ∧ P.step u.1.1 u.1.2 v.1.2

theorem edge_strict {u v : Vertex P} (h : edge P u v) : u.1.1.val < v.1.1.val := by
  have := h.1
  omega

theorem transGen_strict {u v : Vertex P} (h : Relation.TransGen (edge P) u v) :
    u.1.1.val < v.1.1.val := by
  induction h with
  | single h => exact edge_strict P h
  | tail h h' ih => exact ih.trans (edge_strict P h')

theorem eq_source_of_zero (v : Vertex P) (hv : v.1.1.val = 0) : v = source P := by
  have hi : v.1.1 = 0 := Fin.ext hv
  have hs : v.1.2 = P.start := P.first_unique _ (by simpa only [← hi] using v.2)
  apply Subtype.ext
  exact Prod.ext hi hs

theorem eq_sink_of_last (v : Vertex P) (hv : v.1.1.val = P.length) : v = sink P := by
  have hi : v.1.1 = Fin.last P.length := Fin.ext hv
  have hs : v.1.2 = P.finish := P.last_unique _ (by simpa only [← hi] using v.2)
  apply Subtype.ext
  exact Prod.ext hi hs

theorem source_reaches (v : Vertex P) : Relation.ReflTransGen (edge P) (source P) v := by
  suffices h : ∀ m, ∀ v : Vertex P, v.1.1.val = m →
      Relation.ReflTransGen (edge P) (source P) v from h _ v rfl
  intro m
  induction m with
  | zero =>
    intro v hv
    rw [eq_source_of_zero P v hv]
  | succ m ih =>
    intro v hv
    obtain ⟨j, t, hj, ht, he⟩ := P.predecessor v.1.1 v.1.2 v.2 (by omega)
    let u : Vertex P := ⟨(j, t), ht⟩
    have hu : u.1.1.val = m := by change j.val = m; omega
    exact (ih u hu).tail ⟨hj, he⟩

theorem reaches_sink (v : Vertex P) : Relation.ReflTransGen (edge P) v (sink P) := by
  suffices h : ∀ m, ∀ v : Vertex P, P.length - v.1.1.val = m →
      Relation.ReflTransGen (edge P) v (sink P) from h _ v rfl
  intro m
  induction m with
  | zero =>
    intro v hv
    have hi := v.1.1.isLt
    have hlast : v.1.1.val = P.length := by omega
    rw [eq_sink_of_last P v hlast]
  | succ m ih =>
    intro v hv
    obtain ⟨j, t, hj, ht, he⟩ := P.successor v.1.1 v.1.2 v.2 (by omega)
    let u : Vertex P := ⟨(j, t), ht⟩
    have hu : P.length - u.1.1.val = m := by
      have hi := v.1.1.isLt
      change P.length - j.val = m
      omega
    exact Relation.ReflTransGen.head ⟨hj, he⟩ (ih u hu)

/-- The literal finite affine-labelled DAG associated to the layered program. -/
noncomputable abbrev abp : ABP V K where
  Vertex := Vertex P
  edge := edge P
  decEdge := fun u v => inferInstanceAs (Decidable
    (u.1.1.val + 1 = v.1.1.val ∧ P.step u.1.1 u.1.2 v.1.2))
  label u v := P.label u.1.1 u.1.2 v.1.2
  source := source P
  sink := sink P
  source_no_incoming v h := by have := h.1; change v.1.1.val + 1 = 0 at this; omega
  sink_no_outgoing v h := by
    have hi := v.1.1.isLt
    have := h.1
    change P.length + 1 = v.1.1.val at this
    omega
  acyclic v h := (lt_irrefl _) (transGen_strict P h)
  source_reaches := source_reaches P
  reaches_sink := reaches_sink P

/-- Every extending automorphism of the constructed ABP preserves its state layer. -/
theorem layer_preserved [Fintype V] [CommSemiring K]
    {σ : (abp P).Vertex ≃ (abp P).Vertex} {π : V → V}
    (hσ : (abp P).Extends σ π) (v : (abp P).Vertex) :
    (σ v).1.1 = v.1.1 := by
  apply Fin.ext
  exact SymmetricABPBasic.layer_preserved (abp P) (fun v => v.1.1.val)
    (fun u v h => h.1.symm) hσ v

theorem layer_eq_of_mem_orbit {n : ℕ} (P : Program (Fin n × Fin n) K) [CommSemiring K]
    {u v : (abp P).Vertex} (hu : u ∈ (abp P).orbit v) : u.1.1 = v.1.1 := by
  obtain ⟨γ, σ, hσ, rfl⟩ := hu
  exact layer_preserved P hσ v

/-- The orbit bound uses the number of admissible states in a layer, independently of
the total number of layers or of states in the whole ABP. -/
theorem orbitSize_le {n : ℕ} (P : Program (Fin n × Fin n) K) [CommSemiring K] (B : ℕ)
    (hB : ∀ i, Fintype.card {s // P.valid i s} ≤ B) : (abp P).orbitSize ≤ B := by
  classical
  apply Finset.sup_le
  intro v hv
  let f : (abp P).orbit v → {s // P.valid v.1.1 s} := fun u =>
    ⟨u.1.1.2, by
      have hi := layer_eq_of_mem_orbit P u.2
      simpa only [← hi] using u.1.2⟩
  have hf : Function.Injective f := by
    intro u w huw
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (layer_eq_of_mem_orbit P u.2).trans (layer_eq_of_mem_orbit P w.2).symm
    · exact congrArg Subtype.val huw
  have hcard := Fintype.card_le_of_injective f hf
  rw [Set.fintypeCard_eq_ncard] at hcard
  exact hcard.trans (hB _)

end Lax461425Proofs.Section6LayeredABP
