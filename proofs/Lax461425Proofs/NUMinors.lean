import Lax461425Proofs.NUDefs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
Minor facts: `IsMinor` is monotone, transitive, and holds for connected-part quotients and for
removing isolated vertices.
-/

namespace Lax461425Proofs.NU

open Lax461425.HomomorphismPolynomials Lax461425.NonUniformClosure
open Lax68.GraphMinors

open scoped Classical

/-- Induced graph on a singleton is connected. -/
theorem minor_connected_singleton {V : Type} (G : SimpleGraph V) (x : V) :
    (G.induce {x}).Connected := by
  have : Subsingleton ({x} : Set V) := by infer_instance
  have : Nonempty ({x} : Set V) := ⟨⟨x, rfl⟩⟩
  exact (SimpleGraph.connected_iff _).mpr ⟨fun a b => by rw [Subsingleton.elim a b], inferInstance⟩

/-- An injective homomorphism gives a minor. -/
theorem minor_of_injective_hom {U V : Type} {A : SimpleGraph U} {B : SimpleGraph V}
    (f : U → V) (hf : Function.Injective f) (hadj : ∀ u v, A.Adj u v → B.Adj (f u) (f v)) :
    IsMinor A B :=
  ⟨{ branchSet := fun u => {f u}
     connected := fun u => minor_connected_singleton B (f u)
     disjoint := fun {u v} h => by
       simp only [Set.disjoint_singleton]
       exact fun e => h (hf e)
     adjacent := fun {u v} h => ⟨f u, rfl, f v, rfl, hadj u v h⟩ }⟩

theorem isMinor_of_le {V : Type} {F' F : SimpleGraph V} (h : F' ≤ F) : IsMinor F' F :=
  minor_of_injective_hom id Function.injective_id fun _ _ e => h e

/-- Connectivity of a union of connected sets joined along a connected index set. -/
theorem minor_union_connected {V W : Type} (B : SimpleGraph V) (C : SimpleGraph W)
    (S : Set V) (f : V → Set W) (hS : (B.induce S).Connected)
    (hf : ∀ v ∈ S, (C.induce (f v)).Connected)
    (hadj : ∀ x ∈ S, ∀ y ∈ S, B.Adj x y → ∃ p ∈ f x, ∃ q ∈ f y, C.Adj p q) :
    (C.induce (⋃ v ∈ S, f v)).Connected := by
  have key : ∀ (a b : S) (w : (B.induce S).Walk a b) (p q : W) (hp : p ∈ f a) (hq : q ∈ f b),
      (C.induce (⋃ v ∈ S, f v)).Reachable ⟨p, Set.mem_biUnion a.2 hp⟩
        ⟨q, Set.mem_biUnion b.2 hq⟩ := by
    intro a b w
    induction w with
    | nil =>
      rename_i a
      intro p q hp hq
      obtain ⟨r⟩ := (hf a a.2).preconnected ⟨p, hp⟩ ⟨q, hq⟩
      exact ⟨r.map (C.induceHomOfLE (Set.subset_biUnion_of_mem a.2)).toHom⟩
    | cons h w ih =>
      rename_i a c b
      intro p q hp hq
      obtain ⟨p', hp', q', hq', hpq⟩ := hadj a a.2 c c.2 h
      have h1 : (C.induce (⋃ v ∈ S, f v)).Reachable ⟨p, Set.mem_biUnion a.2 hp⟩
          ⟨p', Set.mem_biUnion a.2 hp'⟩ := by
        obtain ⟨r⟩ := (hf a a.2).preconnected ⟨p, hp⟩ ⟨p', hp'⟩
        exact ⟨r.map (C.induceHomOfLE (Set.subset_biUnion_of_mem a.2)).toHom⟩
      have h2 : (C.induce (⋃ v ∈ S, f v)).Adj ⟨p', Set.mem_biUnion a.2 hp'⟩
          ⟨q', Set.mem_biUnion c.2 hq'⟩ := hpq
      exact h1.trans ((SimpleGraph.Adj.reachable h2).trans (ih q' q hq' hq))
  obtain ⟨⟨v0, hv0⟩⟩ := hS.nonempty
  obtain ⟨⟨p0, hp0⟩⟩ := (hf v0 hv0).nonempty
  have : Nonempty (⋃ v ∈ S, f v) := ⟨⟨p0, Set.mem_biUnion hv0 hp0⟩⟩
  refine (SimpleGraph.connected_iff _).mpr ⟨?_, this⟩
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  obtain ⟨a, ha, hpa⟩ := Set.mem_iUnion₂.mp hp
  obtain ⟨b, hb, hqb⟩ := Set.mem_iUnion₂.mp hq
  obtain ⟨w⟩ := hS.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  exact key ⟨a, ha⟩ ⟨b, hb⟩ w p q hpa hqb

theorem isMinor_trans {U V W : Type} {A : SimpleGraph U} {B : SimpleGraph V}
    {C : SimpleGraph W} (hAB : IsMinor A B) (hBC : IsMinor B C) : IsMinor A C := by
  obtain ⟨M1⟩ := hAB
  obtain ⟨M2⟩ := hBC
  refine ⟨{ branchSet := fun u => ⋃ v ∈ M1.branchSet u, M2.branchSet v
            connected := fun u => ?_
            disjoint := fun {u u'} h => ?_
            adjacent := fun {u u'} h => ?_ }⟩
  · exact minor_union_connected B C _ _ (M1.connected u) (fun v _ => M2.connected v)
      (fun x _ y _ hxy => M2.adjacent hxy)
  · rw [Set.disjoint_left]
    intro p hp hq
    obtain ⟨v, hv, hpv⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨v', hv', hpv'⟩ := Set.mem_iUnion₂.mp hq
    have hne : v ≠ v' := fun e => by
      subst e
      exact Set.disjoint_left.mp (M1.disjoint h) hv hv'
    exact Set.disjoint_left.mp (M2.disjoint hne) hpv hpv'
  · obtain ⟨x, hx, y, hy, hxy⟩ := M1.adjacent h
    obtain ⟨p, hp, q, hq, hpq⟩ := M2.adjacent hxy
    exact ⟨p, Set.mem_biUnion hx hp, q, Set.mem_biUnion hy hq, hpq⟩

theorem isMinor_quotientGraph {V : Type} (F : SimpleGraph V) (𝓡 : ConnPart F) :
    IsMinor 𝓡.quotientGraph F :=
  ⟨{ branchSet := fun a => {v | Quotient.mk 𝓡.setoid v = a}
     connected := 𝓡.connected
     disjoint := fun {a b} h => by
       rw [Set.disjoint_left]
       intro v hv hv'
       exact h (hv.symm.trans hv')
     adjacent := fun {a b} h => by
       obtain ⟨_, x, y, hxy, hx, hy⟩ := h
       exact ⟨x, hx, y, hy, hxy⟩ }⟩

/-- The embedding of the pattern without isolated vertices. -/
def minor_nzMap (F : Pattern) : (nzPat F).A ⊕ (nzPat F).B → F.A ⊕ F.B
  | Sum.inl a => Sum.inl a.1
  | Sum.inr b => Sum.inr b.1

theorem minor_nzMap_injective (F : Pattern) : Function.Injective (minor_nzMap F) := by
  rintro (a | a) (b | b) h <;> simp [minor_nzMap] at h <;> simp [Subtype.ext h]

theorem minor_underlying_adj_inl_inr (F : Pattern) (a : F.A) (b : F.B) :
    (underlying F).Adj (Sum.inl a) (Sum.inr b) ↔ F.mult a b ≠ 0 := by
  simp [underlying, SimpleGraph.fromRel_adj]

theorem minor_underlying_adj_inr_inl (F : Pattern) (a : F.A) (b : F.B) :
    (underlying F).Adj (Sum.inr b) (Sum.inl a) ↔ F.mult a b ≠ 0 := by
  rw [SimpleGraph.adj_comm]; exact minor_underlying_adj_inl_inr F a b

theorem minor_underlying_adj_inl_inl (F : Pattern) (a a' : F.A) :
    ¬ (underlying F).Adj (Sum.inl a) (Sum.inl a') := by
  simp [underlying, SimpleGraph.fromRel_adj]

theorem minor_underlying_adj_inr_inr (F : Pattern) (b b' : F.B) :
    ¬ (underlying F).Adj (Sum.inr b) (Sum.inr b') := by
  simp [underlying, SimpleGraph.fromRel_adj]

theorem minor_nzMap_adj_iff (F : Pattern) (u v : (nzPat F).A ⊕ (nzPat F).B) :
    (underlying F).Adj (minor_nzMap F u) (minor_nzMap F v) ↔ (underlying (nzPat F)).Adj u v := by
  rcases u with a | a <;> rcases v with b | b <;>
    simp only [minor_nzMap, minor_underlying_adj_inl_inr, minor_underlying_adj_inr_inl,
      minor_underlying_adj_inl_inl, minor_underlying_adj_inr_inr]
  · rfl
  · rfl

theorem isMinor_nz (F : Pattern) : IsMinor (underlying (nzPat F)) (underlying F) :=
  minor_of_injective_hom (minor_nzMap F) (minor_nzMap_injective F)
    fun u v h => (minor_nzMap_adj_iff F u v).2 h

/-- Neighbour from non-trivial reachability. -/
theorem minor_exists_adj {V : Type} {G : SimpleGraph V} {a b : V} (h : G.Reachable a b)
    (hne : a ≠ b) : ∃ c, G.Adj a c := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl hne
  | cons h _ => exact ⟨_, h⟩

/-- Every non-isolated vertex lies in the range of `minor_nzMap`. -/
theorem minor_mem_range_nzMap (F : Pattern) (x : F.A ⊕ F.B) :
    (∃ y, (underlying F).Adj x y) → x ∈ Set.range (minor_nzMap F) := by
  rintro ⟨y, hy⟩
  rcases x with a | b
  · rcases y with a' | b'
    · exact absurd hy (minor_underlying_adj_inl_inl F a a')
    · rw [minor_underlying_adj_inl_inr] at hy
      exact ⟨Sum.inl ⟨a, b', hy⟩, rfl⟩
  · rcases y with a' | b'
    · rw [minor_underlying_adj_inr_inl] at hy
      exact ⟨Sum.inr ⟨b, a', hy⟩, rfl⟩
    · exact absurd hy (minor_underlying_adj_inr_inr F b b')

/-- The preimage of a connected set contained in the range of `minor_nzMap` is connected. -/
theorem minor_preimage_connected (F : Pattern) (X : Set (F.A ⊕ F.B))
    (hX : X ⊆ Set.range (minor_nzMap F)) (hc : ((underlying F).induce X).Connected) :
    ((underlying (nzPat F)).induce (minor_nzMap F ⁻¹' X)).Connected := by
  have hbij : Function.Bijective
      (fun x : (minor_nzMap F ⁻¹' X : Set _) => (⟨minor_nzMap F x.1, x.2⟩ : X)) := by
    constructor
    · intro x y h
      exact Subtype.ext (minor_nzMap_injective F (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hX hy
      exact ⟨⟨x, hy⟩, rfl⟩
  let e : ((underlying (nzPat F)).induce (minor_nzMap F ⁻¹' X)) ≃g ((underlying F).induce X) :=
    { toEquiv := Equiv.ofBijective _ hbij
      map_rel_iff' := fun {a b} => by
        show (underlying F).Adj (minor_nzMap F a.1) (minor_nzMap F b.1) ↔
          (underlying (nzPat F)).Adj a.1 b.1
        exact minor_nzMap_adj_iff F a.1 b.1 }
  exact e.connected_iff.mpr hc

theorem isMinor_nz_of_isMinor {V : Type} [Nontrivial V] {G : SimpleGraph V} (hG : G.Connected)
    (F : Pattern) (h : IsMinor G (underlying F)) : IsMinor G (underlying (nzPat F)) := by
  obtain ⟨M⟩ := h
  have hnb : ∀ v, ∃ w, G.Adj v w := by
    intro v
    obtain ⟨w, hw⟩ := exists_ne v
    exact minor_exists_adj (hG.preconnected v w) hw.symm
  have hmem : ∀ v, M.branchSet v ⊆ Set.range (minor_nzMap F) := by
    intro v x hx
    apply minor_mem_range_nzMap
    by_cases hall : ∀ x' ∈ M.branchSet v, x' = x
    · obtain ⟨w, hw⟩ := hnb v
      obtain ⟨x', hx', y, _, hxy⟩ := M.adjacent hw
      rw [hall x' hx'] at hxy
      exact ⟨y, hxy⟩
    · push Not at hall
      obtain ⟨x', hx', hne⟩ := hall
      obtain ⟨c, hc⟩ := minor_exists_adj
        ((M.connected v).preconnected ⟨x, hx⟩ ⟨x', hx'⟩) (fun e => hne (congrArg Subtype.val e).symm)
      exact ⟨c.1, hc⟩
  exact ⟨{ branchSet := fun v => minor_nzMap F ⁻¹' M.branchSet v
           connected := fun v => minor_preimage_connected F _ (hmem v) (M.connected v)
           disjoint := fun {u v} huv => by
             rw [Set.disjoint_left]
             intro x hx hx'
             exact Set.disjoint_left.mp (M.disjoint huv) hx hx'
           adjacent := fun {u v} huv => by
             obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent huv
             obtain ⟨x', rfl⟩ := hmem u hx
             obtain ⟨y', rfl⟩ := hmem v hy
             exact ⟨x', hx, y', hy, (minor_nzMap_adj_iff F x' y').mp hxy⟩ }⟩

end Lax461425Proofs.NU
