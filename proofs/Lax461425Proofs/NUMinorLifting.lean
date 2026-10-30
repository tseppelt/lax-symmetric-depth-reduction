import Lax461425Proofs.NUFilled
import Lax461425Proofs.NUBipContract
import Lax461425Proofs.NUMinors
import Lax461425Proofs.NUMinorModel
import Lax461425Proofs.NUEval

/-!
Minor lifting (`lem:minor-lifting`): `minorLifting_eq` and `minorLifting_lt`.
-/

namespace Lax461425Proofs.NU

open Lax461425.HomomorphismPolynomials Lax461425.NonUniformClosure Lax461425.Oddomorphisms
open Lax871432.ConnectedPartitions Lax871432.HomomorphismCounts Lax871432.GraphClasses
open Lax871432.ClosureProperties Lax68.GraphMinors

open scoped Classical

/-- Termwise equality when the contracted pattern lies in the class. -/
theorem mlift_term_eq (𝓕 : GraphClass) (hminor : IsMinorClosed 𝓕)
    (hodd : IsWeakOddomorphismClosed 𝓕) {V : Type} [Fintype V] [Nontrivial V]
    {G : SimpleGraph V} (hG : G.Connected) (hGF : ¬ 𝓕.Mem G) (v₀ : V)
    {X : Type} [Finite X] (Q : SimpleGraph X) (hQ : 𝓕.Mem Q) :
    homCount Q (cfiHat G (Pi.single v₀ 1)) = homCount Q (cfiHat G 0) := by
  have : Fintype X := Fintype.ofFinite X
  refine le_antisymm (filled_le Q hG v₀) ?_
  by_contra hlt
  have hlt' := lt_of_not_ge hlt
  obtain ⟨ψ, -, hψ⟩ := (filled_lt_iff Q hG v₀).1 hlt'
  have h1 : 𝓕.Mem (Fpsi Q G ψ) :=
    hminor _ (isMinor_of_le (inf_le_left : Fpsi Q G ψ ≤ Q)) hQ
  exact hGF (hodd (psiHom Q G ψ) hψ h1)

/-- Strict inequality for a contracted pattern containing `G` in the strong sense. -/
theorem mlift_term_lt {V : Type} [Fintype V] [Nontrivial V]
    {G : SimpleGraph V} (hG : G.Connected) (v₀ : V)
    {X : Type} [Finite X] (Q : SimpleGraph X) (ι : V → X) (hinj : Function.Injective ι)
    (hadj : ∀ u v, G.Adj u v → Q.Adj (ι u) (ι v))
    (hiso : ∀ q, q ∉ Set.range ι → ∀ q', ¬ Q.Adj q q') :
    homCount Q (cfiHat G (Pi.single v₀ 1)) < homCount Q (cfiHat G 0) := by
  have : Fintype X := Fintype.ofFinite X
  rw [filled_lt_iff Q hG v₀]
  let ψ : X → V := fun q => if h : ∃ u, ι u = q then h.choose else v₀
  have hψι : ∀ u, ψ (ι u) = u := by
    intro u
    have h : ∃ u', ι u' = ι u := ⟨u, rfl⟩
    simp only [ψ, dif_pos h]
    exact hinj h.choose_spec
  have hrange : ∀ a b, Q.Adj a b → (a ∈ Set.range ι ∧ b ∈ Set.range ι) := by
    intro a b hab
    refine ⟨?_, ?_⟩
    · by_contra h; exact hiso a h b hab
    · by_contra h; exact hiso b h a hab.symm
  refine ⟨ψ, ?_, ?_⟩
  · intro a b hab
    obtain ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ := hrange a b hab
    rw [hψι, hψι]
    intro h; subst h; exact Q.loopless.irrefl _ hab
  · -- the subgraph
    let F'' : (Fpsi Q G ψ).Subgraph :=
      { verts := Set.univ
        Adj := fun a b => ∃ u v, G.Adj u v ∧ a = ι u ∧ b = ι v
        adj_sub := by
          rintro a b ⟨u, v, huv, rfl, rfl⟩
          exact ⟨hadj u v huv, by simpa [hψι] using huv⟩
        edge_vert := fun _ => Set.mem_univ _
        symm := ⟨by
          rintro a b ⟨u, v, huv, rfl, rfl⟩
          exact ⟨v, u, huv.symm, rfl, rfl⟩⟩ }
    refine ⟨F'', ?_⟩
    -- neighbours description
    have hnb : ∀ (a : F''.verts) (x : V),
        neighborsOver ((psiHom Q G ψ).comp F''.hom) a x =
          {b : F''.verts | (∃ u v, G.Adj u v ∧ a.1 = ι u ∧ b.1 = ι v) ∧ ψ b.1 = x} := by
      intro a x
      ext b
      exact Iff.rfl
    have hodd_ι : ∀ (a : F''.verts) (u : V), a.1 = ι u →
        IsOdd ((psiHom Q G ψ).comp F''.hom) a := by
      intro a u hau x hx
      have hx' : G.Adj u x := by
        have : ((psiHom Q G ψ).comp F''.hom) a = u := by
          show ψ a.1 = u
          rw [hau, hψι]
        rwa [this] at hx
      have : neighborsOver ((psiHom Q G ψ).comp F''.hom) a x = {⟨ι x, Set.mem_univ _⟩} := by
        rw [hnb]
        ext b
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨⟨u', v, huv, h1, h2⟩, h3⟩
          have : u' = u := hinj (h1.symm.trans hau)
          subst this
          rw [h2, hψι] at h3
          subst h3
          exact Subtype.ext h2
        · rintro rfl
          exact ⟨⟨u, x, hx', hau, rfl⟩, hψι x⟩
      rw [this, Set.ncard_singleton]
      exact odd_one
    have heven_not : ∀ (a : F''.verts), a.1 ∉ Set.range ι →
        IsEven ((psiHom Q G ψ).comp F''.hom) a := by
      intro a ha x hx
      have : neighborsOver ((psiHom Q G ψ).comp F''.hom) a x = ∅ := by
        rw [hnb]
        ext b
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨u, v, huv, h1, h2⟩, h3⟩
        exact ha ⟨u, h1.symm⟩
      rw [this, Set.ncard_empty]
      exact ⟨0, rfl⟩
    refine ⟨?_, ?_⟩
    · intro a
      by_cases ha : a.1 ∈ Set.range ι
      · obtain ⟨u, hu⟩ := ha
        exact Or.inr (hodd_ι a u hu.symm)
      · exact Or.inl (heven_not a ha)
    · intro x
      have hset : {a : F''.verts | ((psiHom Q G ψ).comp F''.hom) a = x ∧
          IsOdd ((psiHom Q G ψ).comp F''.hom) a} = {⟨ι x, Set.mem_univ _⟩} := by
        ext a
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases ha : a.1 ∈ Set.range ι
          · obtain ⟨u, hu⟩ := ha
            have : ψ a.1 = x := h1
            rw [← hu, hψι] at this
            subst this
            exact Subtype.ext hu.symm
          · exfalso
            obtain ⟨y, hy⟩ := hG.preconnected.exists_adj_of_nontrivial x
            have hy' : G.Adj (((psiHom Q G ψ).comp F''.hom) a) y := by rw [h1]; exact hy
            have h3 := h2 y hy'
            have : neighborsOver ((psiHom Q G ψ).comp F''.hom) a y = ∅ := by
              rw [hnb]
              ext b
              simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
              rintro ⟨⟨u, v, huv, h1, h2⟩, h3⟩
              exact ha ⟨u, h1.symm⟩
            rw [this, Set.ncard_empty] at h3
            exact absurd h3 (by decide)
        · rintro rfl
          exact ⟨hψι x, hodd_ι _ x rfl⟩
      rw [hset, Set.ncard_singleton]
      exact odd_one

/-- Pattern in the class: the two filled bipartite CFI graphs agree. -/
theorem minorLifting_eq (𝓕 : GraphClass) (hminor : IsMinorClosed 𝓕)
    (hodd : IsWeakOddomorphismClosed 𝓕) {V : Type} [Fintype V] [Nontrivial V]
    {G : SimpleGraph V} (hG : G.Connected) (hGF : ¬ 𝓕.Mem G) (v₀ : V) (F : Pattern)
    (hF : 𝓕.Mem (underlying F)) :
    homBip F (BRel (cfiHat G (Pi.single v₀ 1))) = homBip F (BRel (cfiHat G 0)) := by
  rw [homBip_BRel, homBip_BRel]
  refine finsum_congr fun 𝓡 => ?_
  exact mlift_term_eq 𝓕 hminor hodd hG hGF v₀ _
    (hminor _ (isMinor_quotientGraph _ 𝓡) hF)

/-- Pattern containing `G` as a minor: strictly more homomorphisms into `B(Ĝ_0)` than `B(Ĝ_1)`. -/
theorem minorLifting_lt {V : Type} [Fintype V] [Nontrivial V] {G : SimpleGraph V}
    (hG : G.Connected) (v₀ : V) (F : Pattern) (hF : IsMinor G (underlying F)) :
    homBip F (BRel (cfiHat G (Pi.single v₀ 1))) < homBip F (BRel (cfiHat G 0)) := by
  rw [homBip_BRel, homBip_BRel]
  obtain ⟨𝓡₀, ι, hinj, hadj, hiso⟩ := exists_connPart_of_isMinor hG hF
  have : Fintype (ConnPart (underlying F)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  refine Finset.sum_lt_sum (fun 𝓡 _ => filled_le _ hG v₀) ⟨𝓡₀, Finset.mem_univ _, ?_⟩
  exact mlift_term_lt hG v₀ _ ι hinj hadj hiso

end Lax461425Proofs.NU
