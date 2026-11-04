import Lean
import Lax461425Proofs.DixonMortimer
import Lax461425Proofs.ReducedRigid
import Lax461425Proofs.SkewCircuitCharacterisation
import Lax461425Proofs.Section6Characterisation
import Lax461425Proofs.HomomorphismSpanning

/-!
Executable checks for the new statement/proof split. A conclusion check compares the full
Lean types (not docstrings) and permits only standard logical axioms and independently
checked theorem interfaces. In particular, unproved target axioms and `sorryAx` cannot
discharge a proof.
-/

namespace Lax461425Proofs.ProofAudit

open Lean Meta Elab Command

private def allowedAxioms : Array Name := #[
  `propext, `Classical.choice, `Quot.sound]

/-- Resolve concept interfaces to their independently checked proofs, including Tim's
existing results and the new pathwidth refinement. This is a registry, not an axiom
allowlist: types and proof dependencies are checked recursively on every use. -/
private def existingProofs : Array (Name × Name) := #[
  (`Lax461425.BooleanSumSymmetry.matrixInvariant_of_mem,
    `Lax461425Proofs.BooleanWitnesses.matrixInvariant_of_mem),
  (`Lax461425.SymmetricFormulaWitness.formula_witness,
    `Lax461425Proofs.Section7FormulaConstruction.formula_witness),
  (`Lax461425.PermanentCompleteness.membership,
    `Lax461425Proofs.Permanent.permanent_membership),
  (`Lax461425.HomomorphismSpanning.invariant_mem_span_hom,
    `Lax461425Proofs.HomomorphismSpanning.invariant_mem_span_hom),
  (`Lax461425.DixonMortimer.exists_fixingSubgroup_inf_alternatingGroup_le,
    `Lax461425Proofs.exists_fixingSubgroup_inf_alternatingGroup_le),
  (`Lax461425.ReducedRigid.isRigid, `Lax461425Proofs.ReducedRigid.isRigid),
  (`Lax461425.SkewCircuitCharacterisation.eventually_pathwidth_span,
    `Lax461425Proofs.SkewCircuitCharacterisation.eventually_pathwidth_span),
  (`Lax461425.ABPsForPatterns.exists_abp,
    `Lax461425Proofs.Section6ABPForPatterns.exists_abp),
  (`Lax461425.SkewFromABP.family_inclusion,
    `Lax461425Proofs.Section6ABPToSkew.family_inclusion),
  (`Lax461425.ABPFromSkew.family_inclusion,
    `Lax461425Proofs.Section6Characterisation.skew_to_abp)]

private def checkTypes (targetName proofName : Name) : CommandElabM Unit := do
  liftTermElabM do
    let t ← mkConstWithFreshMVarLevels targetName
    let p ← mkConstWithFreshMVarLevels proofName
    unless ← isDefEq (← inferType t) (← inferType p) do
      throwError "Conclusion type mismatch: {targetName} and {proofName}"
    let targetInfo ← getConstInfo targetName
    let proofInfo ← getConstInfo proofName
    match Kernel.isDefEq (← getEnv) {} proofInfo.type targetInfo.type with
    | .ok true => pure ()
    | _ => throwError "Archive kernel type mismatch: {targetName} and {proofName}"

private partial def auditDependencies (proofName : Name) (active : Array Name := #[])
    (allowCited : Bool := true) : CommandElabM Unit := do
  if active.contains proofName then
    throwError "Circular proof registry at {proofName}"
  let axioms ← Lean.collectAxioms proofName
  for a in axioms do
    if let some (_, proof) := existingProofs.find? (fun pair => pair.1 == a) then
      checkTypes a proof
      auditDependencies proof (active.push proofName) allowCited
    else unless allowedAxioms.contains a &&
        (allowCited || (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains a) do
      throwError "Unapproved axiom {a} in {proofName}"
  let earlier := axioms.filter fun a =>
    allowedAxioms.contains a && !(#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains a
  logInfo m!"Axiom audit passed: {proofName}; unproved cited earlier results: {earlier.toList}"

/-- Fail the build if the proof relies on an unapproved axiom. -/
elab "audit_axioms " p:ident : command => do
  let pn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo p
  auditDependencies pn

/-- Require closure under standard logical axioms and independently checked interfaces. -/
elab "audit_closed " p:ident : command => do
  let pn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo p
  auditDependencies pn #[] false

/-- Fail the build on a type mismatch or an unapproved transitive proof dependency. -/
elab "audit_conclusion " target:ident " := " proof:ident : command => do
  let tn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  let pn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo proof
  checkTypes tn pn
  auditDependencies pn

end Lax461425Proofs.ProofAudit
