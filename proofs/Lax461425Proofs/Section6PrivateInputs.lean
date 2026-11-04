import Lax461425.CircuitProperties
import Lax461425Proofs.InputConditions
import Lax461425Proofs.Section6ABPToSkew

open Lax461425.CircuitProperties Lax461425Proofs.InputConditions

/-!
The explicit ABP-to-skew conversion uses private coefficient and variable leaves. At each
product gate its coefficient and variable have different label constructors, so identifying
equally labelled inputs cannot introduce parallel input wires.
-/

namespace Lax461425Proofs.Section6ABPToSkew

open Lax461425.Circuits Lax461425.SymmetricABPs
open scoped Classical

variable {V : Type} {K : Type*} [Fintype V] [One K] (G : ABP V K)

theorem circuit_privateInputs : (PrivateInputs (circuit G)) := by
  constructor
  · change ¬ (GateLabel.add : GateLabel V K).IsInput
    simp [GateLabel.IsInput]
  · intro g hg
    cases g with
    | vertex v => exact hg.elim
    | term e x => exact hg.elim
    | coeff e x =>
      refine ⟨.term e x, by simp [circuit, wire], ?_⟩
      intro q hq
      cases q with
      | term f y =>
        have he : f = e ∧ y = x := by
          by_contra he
          simp [circuit, wire, he] at hq
        rcases he with ⟨rfl, rfl⟩
        rfl
      | vertex v => simp [circuit, wire] at hq
      | coeff f y => simp [circuit, wire] at hq
      | inputVar f y => simp [circuit, wire] at hq
      | sourceOne => simp [circuit, wire] at hq
    | inputVar e x =>
      refine ⟨.term e (some x), by simp [circuit, wire], ?_⟩
      intro q hq
      cases q with
      | term f y =>
        cases y with
        | none => simp [circuit, wire] at hq
        | some y =>
          have he : f = e ∧ y = x := by
            by_contra he
            simp [circuit, wire, he] at hq
          rcases he with ⟨rfl, rfl⟩
          rfl
      | vertex v => simp [circuit, wire] at hq
      | coeff f y => simp [circuit, wire] at hq
      | inputVar f y => simp [circuit, wire] at hq
      | sourceOne => simp [circuit, wire] at hq
    | sourceOne =>
      refine ⟨.vertex G.source, by simp [circuit, wire], ?_⟩
      intro q hq
      cases q with
      | vertex v =>
        have hv : v = G.source := by by_contra hv; simp [circuit, wire, hv] at hq
        subst v
        rfl
      | term f y => cases y <;> simp [circuit, wire] at hq
      | coeff f y => simp [circuit, wire] at hq
      | inputVar f y => simp [circuit, wire] at hq
      | sourceOne => simp [circuit, wire] at hq

theorem circuit_inputSiblingsDistinct : (InputSiblingsDistinct (circuit G)) := by
  intro p g h hg hh hpg hph hlabel
  cases p with
  | vertex v =>
    cases g <;> cases h <;> simp_all [circuit, label, GateLabel.IsInput, wire]
  | term e x =>
    cases x <;> cases g <;> cases h <;> simp_all [circuit, label, GateLabel.IsInput, wire]
    all_goals split_ifs at hpg hph <;> simp_all
  | coeff e x => cases g <;> simp [circuit, wire] at hpg
  | inputVar e x => cases g <;> simp [circuit, wire] at hpg
  | sourceOne => cases g <;> simp [circuit, wire] at hpg

end Lax461425Proofs.Section6ABPToSkew
