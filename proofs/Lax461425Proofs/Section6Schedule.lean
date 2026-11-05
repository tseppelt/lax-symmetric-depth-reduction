import Lax461425Proofs.Section6BagProgram
import Mathlib.Tactic

/-!
Insert one processing step for every edge occurrence into a path decomposition. Repeated
bags preserve its width and interval property; the extra slot in each block separates edge
processing from the transition to the next bag.
-/

namespace Lax461425Proofs.Section6Schedule

open Lax461425.SymmetricABPs Lax461425.HomomorphismPolynomials
open Section6BagProgram
open scoped Classical

variable {F : Pattern} {k : ℕ} (D : PaddedPathDecomposition F k)

/-- Parallel edges are represented by separate occurrences. -/
abbrev Occurrence (F : Pattern) := Σ p : F.A × F.B, Fin (F.mult p.1 p.2)

noncomputable def enumerate : Occurrence F ≃ Fin (Fintype.card (Occurrence F)) :=
  Fintype.equivFin _

def denominator : ℕ := Fintype.card (Occurrence F) + 1

lemma denominator_pos : 0 < denominator (F := F) := by simp [denominator]

def length : ℕ := (D.length + 1) * denominator (F := F)

noncomputable def coveringBag (e : Occurrence F) : Fin (D.length + 1) :=
  Classical.choose (D.covers_edge e.1.1 e.1.2 (by have := e.2.isLt; omega))

theorem coveringBag_spec (e : Occurrence F) :
    Sum.inl e.1.1 ∈ D.bag (coveringBag D e) ∧
      Sum.inr e.1.2 ∈ D.bag (coveringBag D e) :=
  Classical.choose_spec (D.covers_edge e.1.1 e.1.2 (by have := e.2.isLt; omega))

lemma slot_lt (j : Fin (D.length + 1)) (r : ℕ) (hr : r < denominator (F := F)) :
    j.val * denominator (F := F) + r < length D := by
  have h₁ : j.val * denominator (F := F) + r <
      (j.val + 1) * denominator (F := F) := by nlinarith
  have h₂ := Nat.mul_le_mul_right (denominator (F := F)) (Nat.le_of_lt_succ j.isLt)
  dsimp [length]
  nlinarith

noncomputable def place (e : Occurrence F) : Fin (length D + 1) :=
  ⟨(coveringBag D e).val * denominator (F := F) + (enumerate e).val,
    Nat.lt_succ_of_lt (slot_lt D _ _ (by have := (enumerate e).isLt; dsimp only [denominator]; omega))⟩

def decode (i : Fin (length D + 1)) : Fin (D.length + 1) :=
  ⟨min (i.val / denominator (F := F)) D.length, by omega⟩

theorem decode_mono {i j : Fin (length D + 1)} (hij : i ≤ j) :
    decode D i ≤ decode D j := by
  change min (i.val / denominator (F := F)) D.length ≤
    min (j.val / denominator (F := F)) D.length
  exact min_le_min_right _ (Nat.div_le_div_right hij)

lemma decode_zero : decode D 0 = 0 := by apply Fin.ext; simp [decode]

lemma decode_last : decode D (Fin.last (length D)) = Fin.last D.length := by
  apply Fin.ext
  simp [decode, length, denominator, Nat.mul_div_cancel]

lemma decode_slot (j : Fin (D.length + 1)) (r : ℕ) (hr : r < denominator (F := F))
    (i : Fin (length D + 1)) (hi : i.val = j.val * denominator (F := F) + r) :
    decode D i = j := by
  apply Fin.ext
  simp only [decode, hi]
  rw [Nat.mul_comm j.val (denominator (F := F)),
    Nat.mul_add_div (denominator_pos (F := F)), Nat.div_eq_of_lt hr, Nat.add_zero,
    Nat.min_eq_left (Nat.le_of_lt_succ j.isLt)]

lemma decode_place (e : Occurrence F) : decode D (place D e) = coveringBag D e :=
  decode_slot D _ _ (by have := (enumerate e).isLt; dsimp only [denominator]; omega) _ rfl

lemma decode_next_place (e : Occurrence F) :
    decode D (Section6BagProgram.next (place D e)) = coveringBag D e := by
  have hr : (enumerate e).val + 1 < denominator (F := F) := by
    have := (enumerate e).isLt
    dsimp only [denominator]
    omega
  apply decode_slot D (coveringBag D e) ((enumerate e).val + 1) hr
  dsimp [Section6BagProgram.next, place]
  have hlt := slot_lt D (coveringBag D e) ((enumerate e).val + 1) hr
  rw [Nat.min_eq_left (by omega)]
  omega

lemma place_lt_length (e : Occurrence F) : (place D e).val < length D :=
  slot_lt D _ _ (by have := (enumerate e).isLt; dsimp only [denominator]; omega)

theorem place_injective : Function.Injective (place D) := by
  intro e f hef
  apply enumerate.injective
  apply Fin.ext
  have hm := congrArg (fun i : Fin (length D + 1) => i.val % denominator (F := F)) hef
  have he : (enumerate e).val < denominator (F := F) := by
    have := (enumerate e).isLt; dsimp only [denominator]; omega
  have hf : (enumerate f).val < denominator (F := F) := by
    have := (enumerate f).isLt; dsimp only [denominator]; omega
  simpa [place, Nat.add_mod, Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hf] using hm

noncomputable def eventAt (i : Fin (length D + 1)) : Option (Occurrence F) :=
  if h : ∃ e, place D e = i then some (Classical.choose h) else none

theorem eventAt_some_iff (i : Fin (length D + 1)) (e : Occurrence F) :
    eventAt D i = some e ↔ place D e = i := by
  unfold eventAt
  split_ifs with h
  · have hc := Classical.choose_spec h
    constructor
    · intro he
      have he' : Classical.choose h = e := Option.some.inj he
      simpa [he'] using hc
    · intro he
      exact congrArg some (place_injective D (hc.trans he.symm))
  · constructor
    · intro he; cases he
    · intro he; exact False.elim (h ⟨e, he⟩)

noncomputable def process (i : Fin (length D + 1)) : Option (F.A × F.B) :=
  (eventAt D i).map Sigma.fst

theorem process_some_iff (i : Fin (length D + 1)) (p : F.A × F.B) :
    process D i = some p ↔ ∃ e : Occurrence F, place D e = i ∧ e.1 = p := by
  unfold process
  cases he : eventAt D i with
  | none =>
    constructor
    · simp
    · rintro ⟨e, hp, _⟩
      have h := (eventAt_some_iff D i e).2 hp
      simp [he] at h
  | some e =>
    have hp := (eventAt_some_iff D i e).1 he
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · intro hep
      exact ⟨e, hp, hep⟩
    · rintro ⟨f, hf, hfp⟩
      have hef : e = f := place_injective D (hp.trans hf.symm)
      exact hef ▸ hfp

theorem process_last : process D (Fin.last (length D)) = none := by
  cases hp : process D (Fin.last (length D)) with
  | none => rfl
  | some p =>
    obtain ⟨e, he, _⟩ := (process_some_iff D _ p).1 hp
    have hlt := place_lt_length D e
    have hv := congrArg Fin.val he
    simp at hv
    omega

theorem process_count (a : F.A) (b : F.B) :
    (Finset.univ.filter fun i => process D i = some (a, b)).card = F.mult a b := by
  symm
  calc
    F.mult a b = (Finset.univ : Finset (Fin (F.mult a b))).card := by simp
    _ = _ := by
      refine Finset.card_bij (fun j _ => place D ⟨(a, b), j⟩) ?_ ?_ ?_
      · intro j _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (process_some_iff D _ _).2 ⟨⟨(a, b), j⟩, rfl, rfl⟩
      · intro i _ j _ he
        have he' := place_injective D he
        apply Fin.ext
        exact congrArg (fun e : Occurrence F => e.2.val) he'
      · intro i hi
        have hp := (Finset.mem_filter.mp hi).2
        obtain ⟨⟨p, j⟩, he, hp⟩ := (process_some_iff D _ _).1 hp
        dsimp at hp
        subst p
        exact ⟨j, Finset.mem_univ _, he⟩

noncomputable def repeatedIndex (j : Fin (D.length + 1)) : Fin (length D + 1) :=
  ⟨j.val * denominator (F := F), Nat.lt_succ_of_lt (by
    simpa using slot_lt D j 0 (denominator_pos (F := F)))⟩

theorem decode_repeatedIndex (j : Fin (D.length + 1)) :
    decode D (repeatedIndex D j) = j :=
  decode_slot D j 0 (denominator_pos (F := F)) _ (by simp [repeatedIndex])

/-- Repeat bags, retaining the empty endpoints, the width bound and all interval axioms. -/
noncomputable def repeatedDecomposition : PaddedPathDecomposition F k where
  length := length D
  bag i := D.bag (decode D i)
  bag_first := by rw [decode_zero, D.bag_first]
  bag_last := by rw [decode_last, D.bag_last]
  card_bag_le i := D.card_bag_le _
  covers_vertex v := by
    obtain ⟨j, hj⟩ := D.covers_vertex v
    exact ⟨repeatedIndex D j, by simpa [decode_repeatedIndex] using hj⟩
  covers_edge a b hab := by
    obtain ⟨j, hj⟩ := D.covers_edge a b hab
    exact ⟨repeatedIndex D j, by simpa [decode_repeatedIndex] using hj⟩
  interval v i j l hij hjl hi hl :=
    D.interval v _ _ _ (decode_mono D hij) (decode_mono D hjl) hi hl

/-- Insert one edge-processing step for every occurrence of every parallel edge. -/
noncomputable def schedule : Schedule F k where
  toPaddedPathDecomposition := repeatedDecomposition D
  process := process D
  process_last := process_last D
  process_bag := by
    intro i a b hp
    obtain ⟨e, he, hep⟩ := (process_some_iff D i (a, b)).1 hp
    subst i
    change D.bag (decode D (place D e)) =
        D.bag (decode D (Section6BagProgram.next (place D e))) ∧
      Sum.inl a ∈ D.bag (decode D (place D e)) ∧
      Sum.inr b ∈ D.bag (decode D (place D e))
    rw [decode_place, decode_next_place]
    refine ⟨rfl, ?_⟩
    have h := coveringBag_spec D e
    simpa [hep] using h
  process_count := process_count D

end Lax461425Proofs.Section6Schedule
