import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Numerical facts about binomial coefficients used in the support theorem.
-/

namespace Lax461425Proofs.STNumerics

/-- `choose n` is monotone on `[0, n / 2]`. -/
theorem choose_mono_half {n a b : ℕ} (hab : a ≤ b) (hb : b ≤ n / 2) :
    n.choose a ≤ n.choose b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- For `κ ≤ r ≤ n - κ`, `choose n κ ≤ choose n r`. -/
theorem choose_le_of_between {n κ r : ℕ} (hκ : κ ≤ r) (hr : r + κ ≤ n) :
    n.choose κ ≤ n.choose r := by
  by_cases h : r ≤ n / 2
  · exact choose_mono_half hκ h
  · rw [← Nat.choose_symm (by omega : r ≤ n)]
    exact choose_mono_half (by omega) (by omega)

/-- `choose n (a + b) ≤ choose n a * choose n b`. -/
theorem choose_add_le {n a b : ℕ} : n.choose (a + b) ≤ n.choose a * n.choose b := by
  by_cases h : a + b ≤ n
  · have h1 := Nat.choose_mul (n := n) (k := a + b) (s := a) (Nat.le_add_right a b)
    rw [Nat.add_sub_cancel_left] at h1
    have h2 : 0 < (a + b).choose a := Nat.choose_pos (Nat.le_add_right a b)
    have h3 : (n - a).choose b ≤ n.choose b := Nat.choose_le_choose b (Nat.sub_le n a)
    calc n.choose (a + b) ≤ n.choose (a + b) * (a + b).choose a := Nat.le_mul_of_pos_right _ h2
      _ = n.choose a * (n - a).choose b := h1
      _ ≤ n.choose a * n.choose b := Nat.mul_le_mul_left _ h3
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.zero_le _

theorem two_mul_choose_aux {m a : ℕ} (hm8 : 8 ≤ m) (ha : 2 * m ≤ a + 2) :
    2 * (m + a).choose m ≤ (m + a).choose (m + 2) := by
  have e1 := Nat.choose_succ_right_eq (m + a) m
  have e2 := Nat.choose_succ_right_eq (m + a) (m + 1)
  have hs1 : m + a - m = a := by omega
  have hs2 : m + a - (m + 1) = a - 1 := by omega
  rw [hs1] at e1
  rw [hs2] at e2
  have hge : 2 * (m + 1) * (m + 2) ≤ a * (a - 1) := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : 2 * m ≤ b + 3 := by omega
    nlinarith [Nat.mul_le_mul this this, hm8]
  have key : (m + 2) * (m + 1) * (m + a).choose (m + 2) =
      (m + a).choose m * (a * (a - 1)) := by
    calc (m + 2) * (m + 1) * (m + a).choose (m + 2)
        = ((m + a).choose (m + 1 + 1) * (m + 1 + 1)) * (m + 1) := by ring
      _ = (m + a).choose (m + 1) * (a - 1) * (m + 1) := by rw [e2]
      _ = ((m + a).choose (m + 1) * (m + 1)) * (a - 1) := by ring
      _ = (m + a).choose m * (a * (a - 1)) := by rw [e1]; ring
  have hpos : 0 < (m + 2) * (m + 1) := Nat.mul_pos (by omega) (by omega)
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc (m + 2) * (m + 1) * (2 * (m + a).choose m)
      = (m + a).choose m * (2 * (m + 1) * (m + 2)) := by ring
    _ ≤ (m + a).choose m * (a * (a - 1)) := Nat.mul_le_mul_left _ hge
    _ = _ := key.symm

/-- For `n ≥ 20` and `3 κ ≤ n + 2`, `2 * choose n κ ≤ choose n (n / 2)`. -/
theorem two_mul_choose_le {n κ : ℕ} (hn : 20 ≤ n) (hκ : 3 * κ ≤ n + 2) :
    2 * n.choose κ ≤ n.choose (n / 2) := by
  have hκm : κ ≤ (n + 2) / 3 := by omega
  have hmh : (n + 2) / 3 ≤ n / 2 := by omega
  refine le_trans (Nat.mul_le_mul_left 2 (choose_mono_half hκm hmh)) ?_
  by_cases h22 : n ≤ 21
  · have : n = 20 ∨ n = 21 := by omega
    rcases this with rfl | rfl <;> decide +kernel
  · obtain ⟨a, ha⟩ : ∃ a, n = (n + 2) / 3 + a := ⟨n - (n + 2) / 3, by omega⟩
    have h := two_mul_choose_aux (m := (n + 2) / 3) (a := a) (by omega) (by omega)
    rw [← ha] at h
    exact h.trans (Nat.choose_le_middle _ _)

end Lax461425Proofs.STNumerics
