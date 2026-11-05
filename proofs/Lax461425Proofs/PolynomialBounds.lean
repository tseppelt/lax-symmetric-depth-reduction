import Lax461425.SymmetricFamilies
import Lax461425.SymmetricClasses
import Lax461425.SymmetricVNP
import Mathlib.Tactic

/-! Closure properties of the polynomial bounds used for orbit and auxiliary-variable counts. -/

namespace Lax461425Proofs.PolynomialBounds

open Lax461425.SymmetricFamilies Lax461425.SymmetricClasses Lax461425.SymmetricVNP

theorem constant (c : ℕ) : PolynomiallyBounded (fun _ => c) :=
  ⟨c, 0, by simp⟩

theorem index : PolynomiallyBounded (fun n => n) :=
  ⟨1, 1, fun n => by simp⟩

theorem add {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n + g n) := by
  obtain ⟨c, d, hc⟩ := hf
  obtain ⟨e, k, he⟩ := hg
  refine ⟨c + e, d + k, ?_⟩
  intro n
  have hd : (n + 1) ^ d ≤ (n + 1) ^ (d + k) :=
    pow_le_pow_right₀ (by omega) (by omega)
  have hk : (n + 1) ^ k ≤ (n + 1) ^ (d + k) :=
    pow_le_pow_right₀ (by omega) (by omega)
  calc
    f n + g n ≤ c * (n + 1) ^ d + e * (n + 1) ^ k := Nat.add_le_add (hc n) (he n)
    _ ≤ c * (n + 1) ^ (d + k) + e * (n + 1) ^ (d + k) :=
      Nat.add_le_add (Nat.mul_le_mul_left c hd) (Nat.mul_le_mul_left e hk)
    _ = (c + e) * (n + 1) ^ (d + k) := by ring

theorem mul {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n * g n) := by
  obtain ⟨c, d, hc⟩ := hf
  obtain ⟨e, k, he⟩ := hg
  refine ⟨c * e, d + k, ?_⟩
  intro n
  calc
    f n * g n ≤ (c * (n + 1) ^ d) * (e * (n + 1) ^ k) := Nat.mul_le_mul (hc n) (he n)
    _ = (c * e) * (n + 1) ^ (d + k) := by rw [pow_add]; ring

theorem square {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun n => f n ^ 2) := by
  simpa only [pow_two] using mul hf hf

/-- The orbit bound arising from the ABP-to-skew translation remains polynomial. -/
theorem skew_bound {b : ℕ → ℕ} (hb : PolynomiallyBounded b) :
    PolynomiallyBounded (fun n => b n + b n ^ 2 * (n ^ 2 + 1) + 1) :=
  add (add hb (mul (square hb) (add (square index) (constant 1)))) (constant 1)

end Lax461425Proofs.PolynomialBounds
