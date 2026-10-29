import Lax461425Proofs.ConverseGates

/-!
The depth bound for the circuit built in `ConverseGates.lean`: `C.depth ≤ 2Δ + 1`. This follows
directly from the strictly decreasing measure `mu` used there for acyclicity: every gate has
`mu g ≤ 2Δ + 1`, and `mu` strictly decreases by at least `1` along every wire, so no path can
have length more than `2Δ + 1`.
-/

namespace Lax461425Proofs

open Classical Lax461425.Circuits Lax461425.HomomorphismPolynomials Lax461425.Forestwidth

variable {F : Pattern} {Δ k : ℕ} (N : NormDecomp F Δ k) (n : ℕ)

/-- A purely combinatorial fact: if `f : Fin (m + 1) → ℕ` strictly decreases along consecutive
indices, then `m ≤ f 0`. -/
theorem fin_strict_decr_bound {m : ℕ} (f : Fin (m + 1) → ℕ)
    (hf : ∀ i : Fin m, f i.succ < f i.castSucc) : m ≤ f 0 := by
  induction m with
  | zero => exact Nat.zero_le _
  | succ m' ih =>
      have hrec : m' ≤ f (0 : Fin (m' + 1)).succ := by
        apply ih (fun i => f i.succ)
        intro j
        exact hf j.succ
      have hbase : f (0 : Fin (m' + 1)).succ < f 0 := hf 0
      omega

/-- **Item 3 (depth bound).** The constructed circuit has depth at most `2Δ + 1`. -/
theorem circuit_depth_le (K : Type*) (hn0 : 0 < n) (hE : ∃ a b, F.mult a b ≠ 0) :
    (circuit N n K hn0 hE).depth ≤ 2 * Δ + 1 := by
  show sSup {m | ∃ p : Fin (m + 1) → CGate N n,
      ∀ i : Fin m, 0 < wire N n (p i.castSucc) (p i.succ)} ≤ 2 * Δ + 1
  apply csSup_le'
  intro m hm
  obtain ⟨p, hp⟩ := hm
  have hdecr : ∀ i : Fin m, mu N n (p i.succ) < mu N n (p i.castSucc) :=
    fun i => wire_pos_lt N n (hp i)
  have hb := fin_strict_decr_bound (fun i => mu N n (p i)) hdecr
  have hc := mu_le N n (p 0)
  omega

end Lax461425Proofs
