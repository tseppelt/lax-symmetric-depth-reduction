import Lax461425Proofs.RigidWeight
import Lax461425Proofs.RigidRep

/-!
Helper material for the rigidification proof: the reduced circuit `C'` obtained from `C` by
merging equivalent gates, restricted to the representatives from which the (representative of
the) output gate can still be reached.
-/

namespace Lax461425Proofs.RigidConstruction

open Lax461425.Circuits RigidHeight RigidEquiv RigidWeight RigidRep

open scoped Classical

variable {V K : Type*} (C : Circuit V K)

/-- `a` is a representative, `b` is a representative, and `b` is a child of `a` in the
aggregated sense: `a` sends positive total weight into the class of `b`. -/
def ParentStep (a b : C.Gate) : Prop := rep C a = a ∧ rep C b = b ∧ 0 < W C b a

/-- A representative is *live* if it can still reach the representative of the output gate via
a chain of `ParentStep`s, mirroring `Circuit.reaches_out`. -/
def IsLive (g : C.Gate) : Prop :=
  Relation.ReflTransGen (fun h g' => ParentStep C h g') g (rep C C.out)

/-- A live gate is a representative. -/
theorem isLive_rep_self {g : C.Gate} (hg : IsLive C g) : rep C g = g := by
  rcases Relation.ReflTransGen.cases_head hg with heq | ⟨c, hgc, _⟩
  · rw [heq]; exact rep_rep C C.out
  · exact hgc.1

/-- The representative of the output gate is live. -/
theorem isLive_out : IsLive C (rep C C.out) := Relation.ReflTransGen.refl

/-- The gates of the reduced circuit `C'`: representatives from which the output can still be
reached. -/
def Gate' := {g : C.Gate // IsLive C g}

noncomputable instance : Fintype (Gate' C) := by unfold Gate'; infer_instance

/-- The reduced circuit obtained from `C` by merging equivalent gates. -/
noncomputable def reduced : Circuit V K where
  Gate := Gate' C
  label a := C.label a.1
  wire a b := W C a.1 b.1
  out := ⟨rep C C.out, isLive_out C⟩
  wire_eq_zero_of_isInput a b hinput := by
    show W C a.1 b.1 = 0
    unfold W
    apply Finset.sum_eq_zero
    intro h _
    rw [C.wire_eq_zero_of_isInput a.1 h hinput]
    simp
  acyclic a ha := by
    have hr : ∀ x y : Gate' C, (fun h g => 0 < W C g.1 h.1) x y → height C x.1 < height C y.1 :=
      fun x y hxy => W_pos_height_lt C hxy
    exact absurd (transGen_strict hr ha) (lt_irrefl _)
  reaches_out g := by
    obtain ⟨g, hg⟩ := g
    unfold IsLive at hg
    induction hg using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.ReflTransGen.refl
    | head h' h ih =>
      exact Relation.ReflTransGen.head h'.2.2 ih

/-- A positive wire from `g` to a child `h` yields positive aggregated weight from `g` into the
class of `h`. -/
theorem W_pos_of_wire_pos {g h : C.Gate} (hw : 0 < C.wire g h) : 0 < W C g (rep C h) := by
  have hmem : (0 : ℕ) < (if Equiv C h (rep C h) then C.wire g h else 0) := by
    rw [if_pos (rep_equiv C h)]; exact hw
  exact lt_of_lt_of_le hmem
    (Finset.single_le_sum (f := fun x => if Equiv C x (rep C h) then C.wire g x else 0)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ h))

/-- If `h` is a child of `g` in `C`, then `rep h` is a child of `rep g` in the aggregated
sense, i.e. a `ParentStep`. -/
theorem parentStep_of_wire_pos {g h : C.Gate} (hw : 0 < C.wire g h) :
    ParentStep C (rep C h) (rep C g) := by
  have h1 : 0 < W C g (rep C h) := W_pos_of_wire_pos C hw
  have h2 : W C g (rep C h) = W C (rep C g) (rep C h) := W_eq_of_equiv C (rep_equiv C g)
  exact ⟨rep_rep C h, rep_rep C g, h2 ▸ h1⟩

/-- The representative of any gate is live: it still reaches the representative of the output
gate, by pushing the original reachability chain of `g` through `rep`. -/
theorem isLive_rep (g : C.Gate) : IsLive C (rep C g) :=
  Relation.ReflTransGen.lift (rep C) (fun _ _ hw => parentStep_of_wire_pos C hw) g C.out
    (C.reaches_out g)

/-- The gate of the reduced circuit `C'` corresponding to a gate of `C`. -/
noncomputable def toC' (g : C.Gate) : (reduced C).Gate := ⟨rep C g, isLive_rep C g⟩

/-- Unfolding lemma for the `wire` field of `reduced C`. -/
theorem reduced_wire (a b : (reduced C).Gate) : (reduced C).wire a b = W C a.1 b.1 := rfl

/-- The weight the reduced circuit assigns from `toC' g` into `b` equals the weight `g` itself
sends into the class of `b`. -/
theorem wire_toC'_eq (g : C.Gate) (b : (reduced C).Gate) :
    (reduced C).wire (toC' C g) b = W C g b.1 := by
  show W C (rep C g) b.1 = W C g b.1
  exact W_eq_of_equiv C (equiv_symm C (rep_equiv C g))

/-- `toC'` is the identity, up to the subtype wrapping, on gates that are already live. -/
theorem toC'_self (p : (reduced C).Gate) : toC' C p.1 = p := by
  apply Subtype.ext
  show rep C p.1 = p.1
  exact isLive_rep_self C p.2

/-- If `g` is equivalent to the representative `b.1` of a reduced gate `b`, then `g` itself
maps to `b`. This is the fact to reach for whenever a wire of `reduced C` (whose multiplicity
is an aggregate `W C a.1 b.1 = ∑ h, if Equiv C h b.1 then C.wire a.1 h else 0` over `b.1`'s whole
equivalence class) is known to be positive via *some specific* `C`-gate `h` with
`0 < C.wire a.1 h`: one need not identify `b.1` itself, or any other member of its class — `h`
alone already determines `b` via this lemma, so any fact already established uniformly for
`toC' C g` (for every `g`, by its own structure) transfers to `b` through `h` directly. -/
theorem toC'_eq_of_equiv {g : C.Gate} {b : (reduced C).Gate} (h : Equiv C g b.1) :
    toC' C g = b := by
  have hreq : rep C g = rep C b.1 := rep_eq_of_equiv C h
  rw [show toC' C g = ⟨rep C g, isLive_rep C g⟩ from rfl, ← toC'_self C b]
  exact Subtype.ext hreq

/-- Aggregated weight into a gate only depends on the gate's equivalence class. -/
theorem W_eq_rep_right (a b : C.Gate) : W C a b = W C a (rep C b) := by
  unfold W
  apply Finset.sum_congr rfl
  intro h _
  have hiff : Equiv C h b ↔ Equiv C h (rep C b) :=
    ⟨fun hh => equiv_trans C hh (rep_equiv C b),
      fun hh => equiv_trans C hh (equiv_symm C (rep_equiv C b))⟩
  rw [show (Equiv C h b) = (Equiv C h (rep C b)) from propext hiff]

/-- The height of a gate is the aggregated-class analogue of its defining recursion: it is one
more than the maximum height among classes it sends positive weight into, computed through the
reduced circuit. -/
theorem height_eq_toC' (a : C.Gate) : height C a =
    Finset.univ.sup
      (fun b : (reduced C).Gate => if 0 < (reduced C).wire (toC' C a) b then height C b.1 + 1
        else 0) := by
  rw [height_eq]
  apply le_antisymm
  · apply Finset.sup_le
    intro h _
    by_cases hc : Child C a h
    · rw [dif_pos hc]
      have hb : 0 < (reduced C).wire (toC' C a) (toC' C h) := by
        show 0 < W C (rep C a) (rep C h)
        rw [← W_eq_of_equiv C (rep_equiv C a)]
        exact W_pos_of_wire_pos C hc
      have hheq : height C h = height C (toC' C h).1 := equiv_height_eq C (rep_equiv C h)
      have hmem :
          (if 0 < (reduced C).wire (toC' C a) (toC' C h) then height C (toC' C h).1 + 1 else 0) ≤
            Finset.univ.sup
              (fun b : (reduced C).Gate =>
                if 0 < (reduced C).wire (toC' C a) b then height C b.1 + 1 else 0) :=
        Finset.le_sup
          (f := fun b : (reduced C).Gate =>
            if 0 < (reduced C).wire (toC' C a) b then height C b.1 + 1 else 0)
          (Finset.mem_univ (toC' C h))
      rw [if_pos hb] at hmem
      omega
    · rw [dif_neg hc]; exact Nat.zero_le _
  · apply Finset.sup_le
    intro b _
    split_ifs with hwb
    · have hwb' : 0 < W C a b.1 := wire_toC'_eq C a b ▸ hwb
      obtain ⟨h0, heq0, hw0⟩ := exists_of_W_pos C hwb'
      have hheq : height C h0 = height C b.1 := equiv_height_eq C heq0
      have hmem :
          (if hc : Child C a h0 then height C h0 + 1 else 0) ≤
            Finset.univ.sup (fun h => if hc : Child C a h then height C h + 1 else 0) :=
        Finset.le_sup (f := fun h => if hc : Child C a h then height C h + 1 else 0)
          (Finset.mem_univ h0)
      rw [dif_pos (show Child C a h0 from hw0)] at hmem
      omega
    · exact Nat.zero_le _

/-- If `a` is live and sends positive weight into the class of a representative `b`, then `b`
is itself live. -/
theorem isLive_of_wire_pos {a b : C.Gate} (ha : IsLive C a) (hb : rep C b = b)
    (hw : 0 < W C a b) : IsLive C b :=
  Relation.ReflTransGen.head ⟨hb, isLive_rep_self C ha, hw⟩ ha

/-- If `a` is live, it sends no weight into any non-live representative class. -/
theorem W_eq_zero_of_not_live {a b : C.Gate} (ha : IsLive C a) (hb : ¬ IsLive C (rep C b)) :
    W C a b = 0 := by
  rw [W_eq_rep_right]
  by_contra hne
  exact hb (isLive_of_wire_pos C ha (rep_rep C b) (Nat.pos_of_ne_zero hne))

/-- If `a` and `a'` are both live and send the same aggregated weight into every live class,
they send the same aggregated weight into *every* class. -/
theorem W_match_all_of_live {a a' : C.Gate} (ha : IsLive C a) (ha' : IsLive C a')
    (hmatch : ∀ b : (reduced C).Gate, W C a b.1 = W C a' b.1) (c : C.Gate) :
    W C a c = W C a' c := by
  by_cases hlive : IsLive C (rep C c)
  · rw [W_eq_rep_right C a c, W_eq_rep_right C a' c]
    exact hmatch ⟨rep C c, hlive⟩
  · rw [W_eq_zero_of_not_live C ha hlive, W_eq_zero_of_not_live C ha' hlive]

end Lax461425Proofs.RigidConstruction
