import Lax461425.DixonMortimer
import Lax461425Proofs.ConverseOrbitSupport
import Lax461425Proofs.STNumerics
import Lax461425Proofs.STUpgrade

/-!
The inductive construction of supports with both sides of size `≤ κ - 1` in the proof of the
support theorem.
-/

namespace Lax461425Proofs.STSupports

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports Equiv
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open Lax461425Proofs.STUpgrade

variable {K : Type*} {n : ℕ} {C : Circuit (Fin n × Fin n) K}

/-- The direct child relation. -/
private def Child (g h : C.Gate) : Prop := 0 < C.wire g h

private instance : Std.Irrefl (Relation.TransGen fun (h g : C.Gate) => Child g h) :=
  ⟨C.acyclic⟩

private theorem wellFounded_child : WellFounded fun (h g : C.Gate) => Child g h := by
  have hsub : Subrelation (fun (h g : C.Gate) => Child g h)
      (Relation.TransGen fun (h g : C.Gate) => Child g h) :=
    fun hc => Relation.TransGen.single hc
  exact Subrelation.wf hsub (Finite.wellFounded_of_trans_of_irrefl _)

/-- The index of a pullback subgroup is at most the index. -/
theorem index_comap_le {H : Subgroup (Γ n)} (f : Perm (Fin n) →* Γ n) :
    (H.comap f).index ≤ H.index := by
  rw [Subgroup.index_comap]
  have h0 : H.relIndex ⊤ ≠ 0 := by
    rw [Subgroup.relIndex_top_right _]; exact Subgroup.FiniteIndex.index_ne_zero
  calc H.relIndex f.range ≤ H.relIndex ⊤ := Subgroup.relIndex_le_of_le_right le_top h0
    _ = H.index := Subgroup.relIndex_top_right _

theorem leftPart_inl_union_inr (A B : Set (Fin n)) :
    leftPart ((Sum.inl '' A ∪ Sum.inr '' B : Set (Fin n ⊕ Fin n))) = A := by
  ext i; simp [leftPart]

theorem rightPart_inl_union_inr (A B : Set (Fin n)) :
    rightPart ((Sum.inl '' A ∪ Sum.inr '' B : Set (Fin n ⊕ Fin n))) = B := by
  ext i; simp [rightPart]

/-- Assembling a support from the two sides. -/
theorem isSupport_of_sides (hrig : IsRigid C) {g : C.Gate} {TL TR : Set (Fin n)}
    (hL : ∀ σ ∈ fixingSubgroup (Perm (Fin n)) TL, (MonoidHom.inl _ _ σ : Γ n) ∈ gateStabilizer hrig g)
    (hR : ∀ σ ∈ fixingSubgroup (Perm (Fin n)) TR, (MonoidHom.inr _ _ σ : Γ n) ∈ gateStabilizer hrig g) :
    IsSupport C g (Sum.inl '' TL ∪ Sum.inr '' TR) := by
  rw [isSupport_iff_fixingSubgroup_le hrig, fixingSubgroupΓ_eq_prod, leftPart_inl_union_inr,
    rightPart_inl_union_inr]
  intro γ hγ
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.mp hγ
  have : γ = (MonoidHom.inl _ _ γ.1 : Γ n) * (MonoidHom.inr _ _ γ.2 : Γ n) := by
    ext <;> simp
  rw [this]
  exact mul_mem (hL _ h1) (hR _ h2)

theorem inl_mem_fixing (S : Set (Fin n ⊕ Fin n)) (τ : Perm (Fin n))
    (h : ∀ i ∈ leftPart S, τ i = i) :
    (MonoidHom.inl _ _ τ : Γ n) ∈ fixingSubgroup (Γ n) S := by
  rw [fixingSubgroupΓ_eq_prod]
  refine Subgroup.mem_prod.mpr ⟨?_, one_mem _⟩
  exact (mem_fixingSubgroup_iff (Perm (Fin n))).mpr h

theorem inr_mem_fixing (S : Set (Fin n ⊕ Fin n)) (τ : Perm (Fin n))
    (h : ∀ i ∈ rightPart S, τ i = i) :
    (MonoidHom.inr _ _ τ : Γ n) ∈ fixingSubgroup (Γ n) S := by
  rw [fixingSubgroupΓ_eq_prod]
  refine Subgroup.mem_prod.mpr ⟨one_mem _, ?_⟩
  exact (mem_fixingSubgroup_iff (Perm (Fin n))).mpr h

/-- A variable gate has an orbit of size at least `n`. -/
theorem le_index_of_var (hrig : IsRigid C) {g : C.Gate} {x : Fin n × Fin n}
    (hx : C.label g = .var x) : n ≤ (gateStabilizer hrig g).index := by
  classical
  rw [← orbit_ncard_eq_index_gateStabilizer hrig g]
  let f : Fin n → C.Gate := fun i => σOf hrig (swap x.1 i, 1) g
  have hlab : ∀ i, C.label (f i) = .var (i, x.2) := by
    intro i
    show C.label (σOf hrig (swap x.1 i, 1) g) = _
    rw [(σOf_extends hrig _).1 g, hx]
    simp [GateLabel.map, actVar]
  have hinj : Set.InjOn f (Set.univ : Set (Fin n)) := by
    intro i _ j _ hij
    have := hlab i
    rw [hij, hlab j] at this
    simpa using this.symm
  have := Set.ncard_le_ncard_of_injOn (s := (Set.univ : Set (Fin n))) (t := orbit C g) f
    (fun i _ => ⟨(swap x.1 i, 1), σOf hrig _, σOf_extends hrig _, rfl⟩) hinj (Set.toFinite _)
  simpa using this

variable {κ : ℕ}

/-- **Small supports.** Every gate has a support with both sides of size at most `κ - 1`. -/
theorem exists_small_support (hn : 20 ≤ n) (hκ : 3 * κ ≤ n + 2) (hκ1 : 1 ≤ κ)
    (hrig : IsRigid C) (hred : C.IsReduced)
    (hidx : ∀ g, (gateStabilizer hrig g).index < n.choose κ) (g : C.Gate) :
    ∃ S, IsSupport C g S ∧ (leftPart S).ncard + 1 ≤ κ ∧ (rightPart S).ncard + 1 ≤ κ := by
  classical
  induction g using wellFounded_child.induction with
  | _ g ih =>
    by_cases hinput : (C.label g).IsInput
    · cases hl : C.label g with
      | var x =>
        have hκ2 : 2 ≤ κ := by
          by_contra hlt
          have hκ' : κ = 1 := by omega
          have h1 := le_index_of_var hrig hl
          have h2 := hidx g
          rw [hκ'] at h2
          simp at h2
          omega
        refine ⟨{Sum.inl x.1, Sum.inr x.2}, ?_, ?_, ?_⟩
        · intro γ σ hfix hext
          have h1 := hfix (Sum.inl x.1) (by simp)
          have h2 := hfix (Sum.inr x.2) (by simp)
          simp only [actPoint, Sum.map_inl, Sum.map_inr, Sum.inl.injEq, Sum.inr.injEq] at h1 h2
          refine hred.1 (σ g) g ?_ ?_
          · rw [hext.1 g, hl]; trivial
          · rw [hext.1 g, hl]; simp [GateLabel.map, actVar, h1, h2]
        · have : leftPart ({Sum.inl x.1, Sum.inr x.2} : Set (Fin n ⊕ Fin n)) = {x.1} := by
            ext i; simp [leftPart]
          rw [this]; simpa using hκ2
        · have : rightPart ({Sum.inl x.1, Sum.inr x.2} : Set (Fin n ⊕ Fin n)) = {x.2} := by
            ext i; simp [rightPart]
          rw [this]; simpa using hκ2
      | const c =>
        refine ⟨∅, ?_, ?_, ?_⟩
        · intro γ σ _ hext
          refine hred.1 (σ g) g ?_ ?_
          · rw [hext.1 g, hl]; trivial
          · rw [hext.1 g, hl]; rfl
        · simpa [leftPart] using hκ1
        · simpa [rightPart] using hκ1
      | add => rw [hl] at hinput; exact absurd hinput (by simp [GateLabel.IsInput])
      | mul => rw [hl] at hinput; exact absurd hinput (by simp [GateLabel.IsInput])
    · have hκ2 : 2 * κ ≤ n := by omega
      have hhalf : 2 * (n.choose κ) ≤ n.choose (n / 2) := STNumerics.two_mul_choose_le hn hκ
      -- left side
      obtain ⟨TL, hTLc, hTL⟩ := Lax461425.DixonMortimer.exists_fixingSubgroup_inf_alternatingGroup_le
        hn hκ1 hκ2 ((gateStabilizer hrig g).comap (MonoidHom.inl (Perm (Fin n)) (Perm (Fin n))))
        (by have := index_comap_le (H := gateStabilizer hrig g) (MonoidHom.inl (Perm (Fin n)) (Perm (Fin n)))
            have := hidx g
            omega)
        ((index_comap_le (MonoidHom.inl (Perm (Fin n)) (Perm (Fin n)))).trans_lt (hidx g))
      obtain ⟨TR, hTRc, hTR⟩ := Lax461425.DixonMortimer.exists_fixingSubgroup_inf_alternatingGroup_le
        hn hκ1 hκ2 ((gateStabilizer hrig g).comap (MonoidHom.inr (Perm (Fin n)) (Perm (Fin n))))
        (by have := index_comap_le (H := gateStabilizer hrig g) (MonoidHom.inr (Perm (Fin n)) (Perm (Fin n)))
            have := hidx g
            omega)
        ((index_comap_le (MonoidHom.inr (Perm (Fin n)) (Perm (Fin n)))).trans_lt (hidx g))
      have hL := upgrade hrig hred (MonoidHom.inl (Perm (Fin n)) (Perm (Fin n))) leftPart
        (fun τ S h => inl_mem_fixing S τ h) hκ2 hinput (T := TL) (by omega)
        (fun α hα => hTL hα)
        (fun h hh => by
          obtain ⟨S, hS, hS1, -⟩ := ih h hh
          exact ⟨S, hS, hS1⟩)
      have hR := upgrade hrig hred (MonoidHom.inr (Perm (Fin n)) (Perm (Fin n))) rightPart
        (fun τ S h => inr_mem_fixing S τ h) hκ2 hinput (T := TR) (by omega)
        (fun α hα => hTR hα)
        (fun h hh => by
          obtain ⟨S, hS, -, hS1⟩ := ih h hh
          exact ⟨S, hS, hS1⟩)
      refine ⟨_, isSupport_of_sides hrig hL hR, ?_, ?_⟩
      · rw [leftPart_inl_union_inr]; omega
      · rw [rightPart_inl_union_inr]; omega

end Lax461425Proofs.STSupports
