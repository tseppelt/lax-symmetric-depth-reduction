import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Basic

namespace Lax461425Proofs.DepthHierarchy

theorem choose_lb_aux (m n : ℕ) (hm : m ≤ n) : n ^ m ≤ m ^ m * n.choose m := by
  have h1 : n ^ m * m.descFactorial m ≤ m ^ m * n.descFactorial m := by
    rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
    have : n ^ m * ∏ i ∈ Finset.range m, (m - i) = ∏ i ∈ Finset.range m, (n * (m - i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [this]
    have : m ^ m * ∏ i ∈ Finset.range m, (n - i) = ∏ i ∈ Finset.range m, (m * (n - i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [this]
    apply Finset.prod_le_prod' 
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have him : i ≤ m := by omega
    have hin : i ≤ n := by omega
    have : m * i ≤ n * i := Nat.mul_le_mul_right _ hm
    zify [him, hin] at this ⊢
    nlinarith
  rw [Nat.descFactorial_self, Nat.descFactorial_eq_factorial_mul_choose] at h1
  have hp : 0 < (Nat.factorial m) := Nat.factorial_pos m
  have : n ^ m * (Nat.factorial m) ≤ m ^ m * n.choose m * (Nat.factorial m) := by
    calc n ^ m * (Nat.factorial m) ≤ m ^ m * ((Nat.factorial m) * n.choose m) := h1
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right this hp

/-- The final numerical estimate: if an orbit size `O` is at least `C(n, k+1)` for every `k ≥ 2`
with `4(k+1) ≤ n` and `2^(k+3) (k+1)^(Δ-1) ≤ n`, then `O ≥ n^(log₂ n - Δ log₂ log₂ n - 3)`. -/
theorem arith {Δ n O : ℕ} (hΔ : 1 ≤ Δ) (hn : 20 ≤ n) (hO : 1 ≤ O)
    (h : ∀ k, 2 ≤ k → 4 * (k + 1) ≤ n → 2 ^ (k + 3) * (k + 1) ^ (Δ - 1) ≤ n →
      n.choose (k + 1) ≤ O) :
    (n : ℝ) ^ (Real.logb 2 n - Δ * Real.logb 2 (Real.logb 2 n) - 3) ≤ O := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hn20 : (20 : ℝ) ≤ n := by exact_mod_cast hn
  set L := Real.logb 2 n with hL
  set ℓ := Real.logb 2 L with hℓ
  have h2L : (2 : ℝ) ^ L = n := Real.rpow_logb (by norm_num) (by norm_num) hn0
  have hL4 : 4 ≤ L := by
    rw [hL, Real.le_logb_iff_rpow_le (by norm_num) hn0]
    norm_num; linarith
  have hL0 : 0 < L := by linarith
  have h2l : (2 : ℝ) ^ ℓ = L := Real.rpow_logb (by norm_num) (by norm_num) hL0
  have hl2 : 2 ≤ ℓ := by
    rw [hℓ, Real.le_logb_iff_rpow_le (by norm_num) hL0]
    norm_num; linarith
  have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hO' : (1 : ℝ) ≤ O := by exact_mod_cast hO
  set e := L - Δ * ℓ - 3 with he
  by_cases hle : e ≤ 0
  · calc (n : ℝ) ^ e ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hle
      _ ≤ O := hO'
  push Not at hle
  -- k
  set a := L - ((Δ - 1 : ℕ) : ℝ) * ℓ - 3 with ha
  have hcast : ((Δ - 1 : ℕ) : ℝ) = (Δ : ℝ) - 1 := by
    rw [Nat.cast_sub hΔ]; simp
  have ha_eq : a = e + ℓ := by rw [ha, he, hcast]; ring
  have ha0 : 0 ≤ a := by rw [ha_eq]; linarith
  set k := ⌊a⌋₊ with hk
  have hk1 : (k : ℝ) ≤ a := Nat.floor_le ha0
  have hk2 : a < k + 1 := Nat.lt_floor_add_one a
  have hk2' : 2 ≤ k := Nat.le_floor (by push_cast; rw [ha_eq]; linarith)
  have hΔ1 : (0 : ℝ) ≤ ((Δ - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hkL : (k : ℝ) + 1 ≤ L := by nlinarith [mul_nonneg hΔ1 (by linarith : (0:ℝ) ≤ ℓ)]
  have hpow : ((k + 1 : ℕ) : ℝ) ^ (Δ - 1) ≤ (2 : ℝ) ^ (ℓ * ((Δ - 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_mul (by norm_num), h2l, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) (by push_cast; exact hkL) _
  have h2k : (2 : ℝ) ^ (k + 3) ≤ (2 : ℝ) ^ (L - ((Δ - 1 : ℕ) : ℝ) * ℓ) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast; linarith
  have hcond2 : 2 ^ (k + 3) * (k + 1) ^ (Δ - 1) ≤ n := by
    have : ((2 ^ (k + 3) * (k + 1) ^ (Δ - 1) : ℕ) : ℝ) ≤ n := by
      push_cast
      calc (2 : ℝ) ^ (k + 3) * ((k : ℝ) + 1) ^ (Δ - 1)
          ≤ (2 : ℝ) ^ (L - ((Δ - 1 : ℕ) : ℝ) * ℓ) * (2 : ℝ) ^ (ℓ * ((Δ - 1 : ℕ) : ℝ)) := by
            apply mul_le_mul h2k (by exact_mod_cast hpow) (by positivity) (by positivity)
        _ = n := by
            rw [← Real.rpow_add (by norm_num), ← h2L]; congr 1; ring
    exact_mod_cast this
  have hcond1 : 4 * (k + 1) ≤ n := by
    have h1 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    have h3 : 1 ≤ (k + 1) ^ (Δ - 1) := Nat.one_le_pow _ _ (by omega)
    calc 4 * (k + 1) ≤ 2 ^ (k + 3) * 1 := by rw [pow_add]; omega
      _ ≤ 2 ^ (k + 3) * (k + 1) ^ (Δ - 1) := Nat.mul_le_mul_left _ h3
      _ ≤ n := hcond2
  have hC := h k hk2' hcond1 hcond2
  have hmn : k + 1 ≤ n := by omega
  have hlb := choose_lb_aux (k + 1) n hmn
  have hlbR : (n : ℝ) ^ (k + 1) ≤ ((k : ℝ) + 1) ^ (k + 1) * (n.choose (k + 1) : ℝ) := by
    exact_mod_cast hlb
  have hm0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hnge : (2 : ℝ) ^ (L - ℓ) * ((k : ℝ) + 1) ≤ n := by
    calc (2 : ℝ) ^ (L - ℓ) * ((k : ℝ) + 1) ≤ (2 : ℝ) ^ (L - ℓ) * (2 : ℝ) ^ ℓ := by
          rw [h2l]; exact mul_le_mul_of_nonneg_left hkL (by positivity)
      _ = n := by rw [← Real.rpow_add (by norm_num), ← h2L]; congr 1; ring
  have hpowle : ((2 : ℝ) ^ (L - ℓ) * ((k : ℝ) + 1)) ^ (k + 1) ≤ (n : ℝ) ^ (k + 1) :=
    pow_le_pow_left₀ (by positivity) hnge _
  rw [mul_pow] at hpowle
  have hmp : (0 : ℝ) < ((k : ℝ) + 1) ^ (k + 1) := by positivity
  have hch : ((2 : ℝ) ^ (L - ℓ)) ^ (k + 1) ≤ (n.choose (k + 1) : ℝ) := by
    have := hpowle.trans hlbR
    rw [mul_comm] at this
    exact le_of_mul_le_mul_left this hmp
  have hCR : (n.choose (k + 1) : ℝ) ≤ O := by exact_mod_cast hC
  have hnE : (n : ℝ) ^ e = (2 : ℝ) ^ (L * e) := by
    rw [Real.rpow_mul (by norm_num), h2L]
  have hexp : L * e ≤ (L - ℓ) * ((k : ℝ) + 1) := by
    have h1 : L ≤ (2:ℝ) ^ L := by
      have h0 : 0 ≤ L := hL0.le
      have := Nat.lt_two_pow_self (n := ⌊L⌋₊)
      have h5 : (⌊L⌋₊ : ℝ) + 1 ≤ (2:ℝ) ^ ⌊L⌋₊ := by exact_mod_cast this
      have h6 : (2:ℝ) ^ ⌊L⌋₊ ≤ (2:ℝ) ^ L := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le h0)
      linarith [Nat.lt_floor_add_one L]
    have hLl : 0 ≤ L - ℓ := by
      have : ℓ ≤ L := by
        rw [hℓ, Real.logb_le_iff_le_rpow (by norm_num) hL0]; exact h1
      linarith
    have hk' : e + ℓ ≤ (k : ℝ) + 1 := by rw [← ha_eq]; exact hk2.le
    nlinarith [mul_nonneg hLl (by linarith : (0:ℝ) ≤ (k:ℝ) + 1 - (e + ℓ)),
      mul_nonneg (by linarith : (0:ℝ) ≤ ℓ) (by nlinarith [mul_nonneg hΔ1 (by linarith : (0:ℝ) ≤ ℓ)] : (0:ℝ) ≤ L - ℓ - e)]
  rw [hnE]
  calc (2 : ℝ) ^ (L * e) ≤ (2 : ℝ) ^ ((L - ℓ) * ((k : ℝ) + 1)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = ((2 : ℝ) ^ (L - ℓ)) ^ (k + 1) := by
        rw [Real.rpow_mul (by norm_num)]; norm_cast
    _ ≤ _ := hch.trans hCR

end Lax461425Proofs.DepthHierarchy
