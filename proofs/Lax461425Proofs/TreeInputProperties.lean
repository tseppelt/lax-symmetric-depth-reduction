import Lax461425.CircuitProperties
import Lax461425.InputSharing
import Lax461425Proofs.ComputedFormulaOrbit

open Lax461425.CircuitProperties

/-!
Private-input and sibling-distinctness facts for finite formula trees. These are the local
conditions needed to identify equal input labels while retaining the paper's formula model.
-/

namespace Lax461425Proofs.TreeInputProperties

open Lax461425.Circuits TreeFormulaCircuit TreeFormulaOperations ComputedFormula
open scoped Classical

variable {V K : Type*} [CommSemiring K]

/-- Every input occurrence of a noninput-rooted tree has exactly one parent and one wire. -/
theorem privateInputs (T : Tree V K) (hout : ¬ (T.label T.out).IsInput) :
    (PrivateInputs (circuit T)) := by
  refine ⟨hout, ?_⟩
  intro g hg
  have hne : g ≠ T.out := fun h => hout (h ▸ hg)
  obtain ⟨p, hp⟩ := T.parent_exists g hne
  refine ⟨p, ?_, ?_⟩
  · simp [circuit, hp]
  · intro q hq
    have hpq : T.parent g = some q := by
      by_contra h
      simp [circuit, h] at hq
    exact Option.some.inj (hpq.symm.trans hp)

/-- Equal-labelled input siblings in a joined tree can only arise in one old child or
between two input child roots. The latter are explicitly required to have distinct labels. -/
theorem siblings_join {I : Type} [Fintype I] (T : I → Tree V K) (mul : Bool)
    (hchild : ∀ i, (InputSiblingsDistinct (circuit (T i))))
    (hroots : ∀ i j, ((T i).label (T i).out).IsInput →
      ((T j).label (T j).out).IsInput →
      (T i).label (T i).out = (T j).label (T j).out → i = j) :
    (InputSiblingsDistinct (circuit (join T mul))) := by
  intro p g h hg hh hpg hph heq
  cases p with
  | inl u =>
    cases u
    obtain ⟨i, rfl⟩ := ComputedFormulaOrbit.join_child_cases T mul g hpg
    obtain ⟨j, rfl⟩ := ComputedFormulaOrbit.join_child_cases T mul h hph
    have hij := hroots i j hg hh heq
    subst j
    rfl
  | inr p =>
    rcases p with ⟨i, p⟩
    obtain ⟨g', rfl⟩ := TreeFormulaOrbit.edge_to_child T mul (i := i) (r := p) hpg
    obtain ⟨h', rfl⟩ := TreeFormulaOrbit.edge_to_child T mul (i := i) (r := p) hph
    have hpg' : 0 < (circuit (T i)).wire p g' := by
      exact (TreeFormulaOrbit.embed_wire T mul i p g') ▸ hpg
    have hph' : 0 < (circuit (T i)).wire p h' := by
      exact (TreeFormulaOrbit.embed_wire T mul i p h') ▸ hph
    exact congrArg (TreeFormulaOrbit.embed T mul i)
      (hchild i p g' h' hg hh hpg' hph' heq)

theorem siblings_var (x : V) : (InputSiblingsDistinct (circuit (var (K := K) x).tree)) := by
  intro p g h hg hh hpg
  simp [circuit, var, varInput] at hpg

theorem siblings_const (c : K) : (InputSiblingsDistinct (circuit (const (V := V) c).tree)) := by
  intro p g h hg hh hpg
  simp [circuit, const, constant] at hpg

theorem root_noninput_op {I : Type} [Fintype I] (mul : Bool) (F : I → Formula V K) :
    ¬ ((op mul F).tree.label (op mul F).tree.out).IsInput := by
  cases mul <;> simp [op, join, GateLabel.IsInput]

theorem root_noninput_mul (F G : Formula V K) :
    ¬ ((ComputedFormula.mul F G).tree.label (ComputedFormula.mul F G).tree.out).IsInput :=
  root_noninput_op true _

theorem root_noninput_add (F G : Formula V K) :
    ¬ ((ComputedFormula.add F G).tree.label (ComputedFormula.add F G).tree.out).IsInput :=
  root_noninput_op false _

/-- A binary operation preserves sibling distinctness if its input child roots have
different labels whenever both child roots are inputs. -/
theorem siblings_binary (mul : Bool) (F G : Formula V K)
    (hF : (InputSiblingsDistinct (circuit F.tree))) (hG : (InputSiblingsDistinct (circuit G.tree)))
    (hcross : (F.tree.label F.tree.out).IsInput → (G.tree.label G.tree.out).IsInput →
      F.tree.label F.tree.out ≠ G.tree.label G.tree.out) :
    (InputSiblingsDistinct (circuit (op mul (fun b : Bool => if b then F else G)).tree)) := by
  apply siblings_join
  · intro b
    cases b
    · exact hG
    · exact hF
  · intro i j hi hj hij
    cases i <;> cases j
    · rfl
    · exact False.elim (hcross hj hi hij.symm)
    · exact False.elim (hcross hi hj hij)
    · rfl

theorem siblings_mul (F G : Formula V K)
    (hF : (InputSiblingsDistinct (circuit F.tree))) (hG : (InputSiblingsDistinct (circuit G.tree)))
    (hcross : (F.tree.label F.tree.out).IsInput → (G.tree.label G.tree.out).IsInput →
      F.tree.label F.tree.out ≠ G.tree.label G.tree.out) :
    (InputSiblingsDistinct (circuit (ComputedFormula.mul F G).tree)) :=
  siblings_binary true F G hF hG hcross

theorem siblings_add (F G : Formula V K)
    (hF : (InputSiblingsDistinct (circuit F.tree))) (hG : (InputSiblingsDistinct (circuit G.tree)))
    (hcross : (F.tree.label F.tree.out).IsInput → (G.tree.label G.tree.out).IsInput →
      F.tree.label F.tree.out ≠ G.tree.label G.tree.out) :
    (InputSiblingsDistinct (circuit (ComputedFormula.add F G).tree)) :=
  siblings_binary false F G hF hG hcross

theorem siblings_op_of_noninput {I : Type} [Fintype I] (mul : Bool) (F : I → Formula V K)
    (hchild : ∀ i, (InputSiblingsDistinct (circuit (F i).tree)))
    (hroot : ∀ i, ¬ ((F i).tree.label (F i).tree.out).IsInput) :
    (InputSiblingsDistinct (circuit (op mul F).tree)) := by
  apply siblings_join
  · exact hchild
  · intro i j hi
    exact False.elim (hroot i hi)

theorem siblings_mul_const (c : K) (F : Formula V K)
    (hF : (InputSiblingsDistinct (circuit F.tree)))
    (hroot : ¬ (F.tree.label F.tree.out).IsInput) :
    (InputSiblingsDistinct (circuit (ComputedFormula.mul (const c) F).tree)) := by
  apply siblings_mul _ _ (siblings_const c) hF
  intro hc hF'
  exact False.elim (hroot hF')

end Lax461425Proofs.TreeInputProperties

namespace Lax461425Proofs.TreeInputProperties

open Lax461425.Circuits TreeFormulaCircuit ComputedFormula

variable {V K : Type*} [Field K]

theorem siblings_tag (t : K) (F : Formula V K)
    (hF : (InputSiblingsDistinct (circuit F.tree)))
    (hroot : ¬ (F.tree.label F.tree.out).IsInput) :
    (InputSiblingsDistinct (circuit (tag t F).tree)) := by
  exact siblings_mul_const t⁻¹ _ (siblings_mul_const t F hF hroot) (root_noninput_mul _ _)

theorem root_noninput_tag (t : K) (F : Formula V K) :
    ¬ ((tag t F).tree.label (tag t F).tree.out).IsInput := root_noninput_mul _ _

end Lax461425Proofs.TreeInputProperties
