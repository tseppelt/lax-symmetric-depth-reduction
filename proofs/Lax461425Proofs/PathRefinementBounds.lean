import Lax461425Proofs.DepthHierarchyArith

/-! An explicit eventual binomial lower bound, using Tim's existing estimate. -/
namespace Lax461425Proofs.PathRefinementBounds

theorem polynomial_lt_choose (c d n : ℕ)
    (hn : max (d + 3) (c * 2 ^ d * (d + 3) ^ (d + 3) + 1) ≤ n) :
    c * (n + 1) ^ d < n.choose (d + 3) := by
  have hm : d + 3 ≤ n := (Nat.le_max_left _ _).trans hn
  have hc : c * 2 ^ d * (d + 3) ^ (d + 3) < n := by
    have := (Nat.le_max_right (d + 3) _).trans hn
    omega
  have hn1 : 1 ≤ n := by omega
  have hd : c * (n + 1) ^ d ≤ c * 2 ^ d * n ^ d := by
    calc
      _ ≤ c * (2 * n) ^ d := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d)
      _ = _ := by rw [mul_pow]; ring
  have hp : 0 < n ^ d := pow_pos (by omega) _
  have hstrict : (d + 3) ^ (d + 3) * (c * (n + 1) ^ d) < n ^ (d + 3) := by
    calc
      _ ≤ (c * 2 ^ d * (d + 3) ^ (d + 3)) * n ^ d := by
        exact (Nat.mul_le_mul_left ((d + 3) ^ (d + 3)) hd).trans_eq (by ring)
      _ < n * n ^ d := Nat.mul_lt_mul_of_pos_right hc hp
      _ = n ^ (d + 1) := by rw [pow_succ]; ring
      _ ≤ n ^ (d + 3) := pow_le_pow_right₀ hn1 (by omega)
  have hlb := DepthHierarchy.choose_lb_aux (d + 3) n hm
  by_contra hh
  have hmul := Nat.mul_le_mul_left ((d + 3) ^ (d + 3)) (Nat.le_of_not_gt hh)
  omega

end Lax461425Proofs.PathRefinementBounds
