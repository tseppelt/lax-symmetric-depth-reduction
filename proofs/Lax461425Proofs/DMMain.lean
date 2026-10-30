import Lax461425Proofs.DMRestrict

/-!
Main argument of the Dixon–Mortimer small-index theorem for `Perm (Fin n)`.
-/

namespace Lax461425Proofs.DM

open Nat Equiv MulAction
open scoped Classical

theorem dm_main {n r : ℕ} (hn : 20 ≤ n) (hr : 1 ≤ r) (hrn : 2 * r ≤ n)
    (H : Subgroup (Perm (Fin n)))
    (hhalf : 2 * H.index < n.choose (n / 2)) (hr' : H.index < n.choose r) :
    ∃ T : Set (Fin n), T.ncard < r ∧
      fixingSubgroup (Perm (Fin n)) T ⊓ alternatingGroup (Fin n) ≤ H := by
  have hcard : Nat.card H * H.index = n ! := by
    rw [Subgroup.card_mul_index, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  generalize H.index = I at hcard hhalf hr'
  by_cases hbig : ∃ x : Fin n, n - n / 2 < (orbit H x).ncard
  · obtain ⟨x, hx⟩ := hbig
    let p : Fin n → Prop := fun y => y ∈ orbit H x
    have hinv : ∀ h ∈ H, ∀ y, p (h y) ↔ p y := by
      intro h hh y
      have hmem : ∀ (h : Perm (Fin n)), h ∈ H → ∀ y, y ∈ orbit H x → h y ∈ orbit H x := by
        intro h hh y ⟨a, ha⟩
        have ha' : a • x = y := ha
        exact ⟨⟨h, hh⟩ * a, by
          show ((⟨h, hh⟩ : H) * a) • x = h y
          rw [mul_smul, ha']; rfl⟩
      constructor
      · intro hy
        have := hmem h⁻¹ (H.inv_mem hh) _ hy
        simpa using this
      · exact hmem h hh y
    have hg : Fintype.card (Subtype p) = (orbit H x).ncard := by
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    have hδ : Fintype.card {y // ¬ p y} + Fintype.card (Subtype p) = n := by
      have h1 : Fintype.card {y // ¬ p y} = Fintype.card (Fin n) - Fintype.card (Subtype p) :=
        Fintype.card_subtype_compl p
      have h2 : Fintype.card (Subtype p) ≤ Fintype.card (Fin n) := Fintype.card_subtype_le p
      rw [Fintype.card_fin] at h1 h2
      omega
    have hres := card_le_restrict (H := H) hinv
    have hK'g : Nat.card (restrictSub p H) ≤ (Fintype.card (Subtype p))! := by
      have h1 : Nat.card (restrictSub p H) ≤ Nat.card (Perm (Subtype p)) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
      have h2 : Nat.card (Perm (Subtype p)) = (Fintype.card (Subtype p))! := by
        rw [Nat.card_perm, Nat.card_eq_fintype_card]
      exact h1.trans h2.le
    have hh : Nat.card H ≤ (Fintype.card (Subtype p))! * (Fintype.card {y // ¬ p y})! :=
      hres.trans (Nat.mul_le_mul_right _ hK'g)
    have hδlt : Fintype.card {y // ¬ p y} < r := by
      by_contra hcon
      have hrδ : r ≤ Fintype.card {y // ¬ p y} := not_lt.mp hcon
      have hδle : Fintype.card {y // ¬ p y} ≤ n / 2 := by omega
      have h1 := contra_set hcard hh hδ
      have h2 := choose_ge (n := n) hrδ hδle
      omega
    have hK : ∀ u v : Subtype p, ∃ ψ : Perm (Subtype p), ψ u = v ∧
        ∀ k ∈ restrictSub p H, ψ * k * ψ⁻¹ ∈ restrictSub p H := by
      intro u v
      obtain ⟨a, ha⟩ := u.2
      obtain ⟨b, hb⟩ := v.2
      have hh : ((b * a⁻¹ : H) : Perm (Fin n)) ∈ H := (b * a⁻¹ : H).2
      have hu : ((b * a⁻¹ : H) : Perm (Fin n)) (u : Fin n) = (v : Fin n) := by
        have : (b * a⁻¹ : H) • (u : Fin n) = (v : Fin n) := by
          rw [← ha, ← hb, ← mul_smul]; simp
        exact this
      refine ⟨Equiv.Perm.subtypePerm _ (hinv _ hh), Subtype.ext hu, ?_⟩
      intro k hk
      exact restrict_conj hh (hinv _ hh) hk
    have hcore := core_dichotomy (Γ := Subtype p) (by omega) (restrictSub p H) hK
    rcases hcore with hA | hsmall
    · refine ⟨{y | ¬ p y}, ?_, fixing_le hA⟩
      have : ({y | ¬ p y} : Set (Fin n)).ncard = Fintype.card {y // ¬ p y} := by
        rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
        try rfl
      rw [this]
      exact hδlt
    · exfalso
      have h3 := three_parts (n := n) (δ := Fintype.card {y // ¬ p y})
        (g := Fintype.card (Subtype p)) hδ (by omega)
      have hb : Nat.card H ≤ 2 * (n / 2)! * (n - n / 2)! := by
        calc Nat.card H ≤ Nat.card (restrictSub p H) * (Fintype.card {y // ¬ p y})! := hres
          _ ≤ (2 * (Fintype.card (Subtype p) / 2)! *
              (Fintype.card (Subtype p) - Fintype.card (Subtype p) / 2)!) *
              (Fintype.card {y // ¬ p y})! := Nat.mul_le_mul_right _ hsmall
          _ = 2 * ((Fintype.card {y // ¬ p y})! * ((Fintype.card (Subtype p) / 2)! *
              (Fintype.card (Subtype p) - Fintype.card (Subtype p) / 2)!)) := by ring
          _ ≤ 2 * ((n / 2)! * (n - n / 2)!) := Nat.mul_le_mul_left _ h3
          _ = _ := by ring
      have := contra_half hcard hb
      omega
  · exfalso
    push Not at hbig
    have h1 := card_le_of_orbits_le H (n - n / 2) (by rw [Fintype.card_fin]; omega) hbig
    rw [Fintype.card_fin, show n - (n - n / 2) = n / 2 by omega] at h1
    have hb : Nat.card H ≤ 2 * (n / 2)! * (n - n / 2)! := by
      calc Nat.card H ≤ (n - n / 2)! * (n / 2)! := h1
        _ ≤ 2 * (n / 2)! * (n - n / 2)! := by
          nlinarith [Nat.factorial_pos (n / 2), Nat.factorial_pos (n - n / 2)]
    have := contra_half hcard hb
    omega

end Lax461425Proofs.DM
