import Mathlib

/-!
Numerical lemmas (factorials and binomial coefficients) for the Dixon–Mortimer small-index
theorem.
-/

namespace Lax461425Proofs.DM

open Nat Finset

/-- Exchange inequality for factorials. -/
theorem fact_exchange {x y B : ℕ} (hx : x ≤ B) (hy : y ≤ B) (hB : B ≤ x + y) :
    x ! * y ! ≤ B ! * (x + y - B)! := by
  have aux : ∀ p c q : ℕ, (c + p)! * (c + q)! ≤ (c + p + q)! * c ! := by
    intro p c q
    induction p with
    | zero => simp [mul_comm]
    | succ p ih =>
      calc (c + (p + 1))! * (c + q)!
          = (c + p + 1) * ((c + p)! * (c + q)!) := by
            rw [← add_assoc, Nat.factorial_succ]; ring
        _ ≤ (c + p + 1) * ((c + p + q)! * c !) := Nat.mul_le_mul_left _ ih
        _ ≤ (c + p + q + 1) * ((c + p + q)! * c !) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = (c + (p + 1) + q)! * c ! := by
            rw [show c + (p + 1) + q = (c + p + q) + 1 by omega, Nat.factorial_succ]; ring
  have h := aux (B - y) (x + y - B) (B - x)
  have e1 : x + y - B + (B - y) = x := by omega
  have e2 : x + y - B + (B - x) = y := by omega
  have e3 : x + y - B + (B - y) + (B - x) = B := by omega
  rw [e3, e1, e2] at h
  exact h

/-- Product of factorials of parts, each at most `B`, is at most `B ! * (N - B)!`. -/
theorem prod_factorial_le {ι : Type*} (s : ι → ℕ) (B : ℕ) (S : Finset ι)
    (hS : ∀ i ∈ S, s i ≤ B) (hB : B ≤ ∑ i ∈ S, s i) :
    ∏ i ∈ S, (s i)! ≤ B ! * (∑ i ∈ S, s i - B)! := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty] at hB ⊢
    have : B = 0 := by omega
    subst this
    simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha] at *
    have hsa : s a ≤ B := hS a (Finset.mem_insert_self _ _)
    have hS' : ∀ i ∈ S, s i ≤ B := fun i hi => hS i (Finset.mem_insert_of_mem hi)
    by_cases hN : B ≤ ∑ i ∈ S, s i
    · have ih' := ih hS' hN
      calc (s a)! * ∏ i ∈ S, (s i)! ≤ (s a)! * (B ! * (∑ i ∈ S, s i - B)!) :=
            Nat.mul_le_mul_left _ ih'
        _ = B ! * ((s a)! * (∑ i ∈ S, s i - B)!) := by ring
        _ ≤ B ! * (s a + ∑ i ∈ S, s i - B)! := by
            apply Nat.mul_le_mul_left
            have := Nat.le_of_dvd (Nat.factorial_pos _)
              (Nat.factorial_mul_factorial_dvd_factorial_add (s a) (∑ i ∈ S, s i - B))
            rwa [show s a + (∑ i ∈ S, s i - B) = s a + ∑ i ∈ S, s i - B by omega] at this
    · have hN := not_le.mp hN
      have hle : ∏ i ∈ S, (s i)! ≤ (∑ i ∈ S, s i)! :=
        Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum S s)
      calc (s a)! * ∏ i ∈ S, (s i)! ≤ (s a)! * (∑ i ∈ S, s i)! := Nat.mul_le_mul_left _ hle
        _ ≤ B ! * (s a + ∑ i ∈ S, s i - B)! :=
            fact_exchange hsa hN.le hB

/-- `choose g (g/2) ≤ 2 * ⌈g/2⌉!` for `g ≥ 11`. -/
theorem choose_half_le (g : ℕ) (hg : 11 ≤ g) : g.choose (g / 2) ≤ 2 * (g - g / 2)! := by
  by_cases h : g ≤ 14
  · interval_cases g <;> decide
  · have h := not_le.mp h
    have h4 : ∀ m : ℕ, 8 ≤ m → 4 ^ m ≤ 2 * m ! := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => decide
      | succ m hm ih =>
        rw [Nat.factorial_succ, pow_succ]
        nlinarith
    calc g.choose (g / 2) ≤ 2 ^ g := Nat.choose_le_two_pow _ _
      _ ≤ 2 ^ (2 * (g - g / 2)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 ^ (g - g / 2) := by rw [pow_mul]; norm_num
      _ ≤ 2 * (g - g / 2)! := h4 _ (by omega)

/-- Bound of the order of a group from a base of size at most `g/2`. -/
theorem bound_of_desc {g k s : ℕ} (hg : 11 ≤ g) (hs : 2 * s ≤ g)
    (h : k * (g - s)! ≤ g !) : k ≤ 2 * (g / 2)! * (g - g / 2)! := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.div_le_self g 2)
  have h2 := choose_half_le g hg
  have h3 : (g - g / 2)! ≤ (g - s)! := Nat.factorial_le (by omega)
  have h4 : k * (g - g / 2)! ≤ (2 * (g / 2)! * (g - g / 2)!) * (g - g / 2)! := by
    calc k * (g - g / 2)! ≤ k * (g - s)! := Nat.mul_le_mul_left _ h3
      _ ≤ g ! := h
      _ = g.choose (g / 2) * (g / 2)! * (g - g / 2)! := h1.symm
      _ ≤ (2 * (g - g / 2)!) * (g / 2)! * (g - g / 2)! := by gcongr
      _ = (2 * (g / 2)! * (g - g / 2)!) * (g - g / 2)! := by ring
  exact Nat.le_of_mul_le_mul_right h4 (Nat.factorial_pos _)

theorem choose_succ_half (M : ℕ) : (M + 1).choose ((M + 1) / 2) ≤ 2 * M.choose (M / 2) := by
  rcases Nat.eq_zero_or_pos ((M + 1) / 2) with h | h
  · have : M = 0 := by omega
    subst this; simp
  · obtain ⟨k, hk⟩ : ∃ k, (M + 1) / 2 = k + 1 := ⟨(M + 1) / 2 - 1, by omega⟩
    rw [hk, Nat.choose_succ_succ']
    have a := Nat.choose_le_middle k M
    have b := Nat.choose_le_middle (k + 1) M
    omega

theorem choose_add_half (N m : ℕ) :
    (N + m).choose ((N + m) / 2) ≤ 2 ^ m * N.choose (N / 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc (N + (m + 1)).choose ((N + (m + 1)) / 2)
        = (N + m + 1).choose ((N + m + 1) / 2) := by rw [add_assoc]
      _ ≤ 2 * (N + m).choose ((N + m) / 2) := choose_succ_half _
      _ ≤ 2 * (2 ^ m * N.choose (N / 2)) := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (m + 1) * N.choose (N / 2) := by ring

theorem choose_mul_ge (c m : ℕ) (hc : 3 ≤ c) (hm : 2 ≤ m) :
    c * 2 ^ m ≤ (c * m).choose m := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [Nat.choose_two_right]
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 3 := ⟨c - 3, by omega⟩
    have e : (d + 3) * 2 * ((d + 3) * 2 - 1) = 2 * ((d + 3) * (2 * d + 5)) := by
      rw [show (d + 3) * 2 - 1 = 2 * d + 5 by omega]; ring
    rw [e, Nat.mul_div_cancel_left _ (by norm_num)]
    nlinarith
  | succ m hm ih =>
    have hv := Nat.add_choose_eq (c * m) c (m + 1)
    have hmem : (m, 1) ∈ Finset.HasAntidiagonal.antidiagonal (m + 1) := by simp
    have hle : (c * m).choose m * c.choose 1 ≤ (c * m + c).choose (m + 1) := by
      rw [hv]
      exact Finset.single_le_sum (f := fun ij : ℕ × ℕ => (c * m).choose ij.1 * c.choose ij.2)
        (fun _ _ => Nat.zero_le _) hmem
    rw [Nat.choose_one_right] at hle
    rw [show c * (m + 1) = c * m + c by ring]
    calc c * 2 ^ (m + 1) = 2 * (c * 2 ^ m) := by ring
      _ ≤ c * (c * 2 ^ m) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ c * (c * m).choose m := Nat.mul_le_mul_left _ ih
      _ = (c * m).choose m * c := by ring
      _ ≤ _ := hle

theorem imprim_aux (m : ℕ) (hm : 2 ≤ m) (b : ℕ) (hb : 2 ≤ b) :
    (b * m).choose (b * m / 2) * (b ! * (m !) ^ b) ≤ 2 * (b * m)! := by
  induction b, hb using Nat.le_induction with
  | base =>
    have e : 2 * m / 2 = m := by omega
    rw [e]
    have h1 := Nat.choose_mul_factorial_mul_factorial (n := 2 * m) (k := m) (by omega)
    rw [show 2 * m - m = m by omega] at h1
    refine le_of_eq ?_
    calc (2 * m).choose m * (2 ! * (m !) ^ 2) = 2 * ((2 * m).choose m * m ! * m !) := by
          simp [Nat.factorial_two]; ring
      _ = 2 * (2 * m)! := by rw [h1]
  | succ b hb ih =>
    set N := b * m with hN
    have e : (b + 1) * m = N + m := by rw [hN]; ring
    rw [e]
    have hA := choose_add_half N m
    have hB := choose_mul_ge (b + 1) m (by omega) hm
    rw [e] at hB
    have hC := Nat.add_choose_mul_factorial_mul_factorial N m
    -- hC : (N+m).choose m * N ! * m ! = (N+m)!
    have hB' : (b + 1) * 2 ^ m ≤ (N + m).choose m := hB
    calc (N + m).choose ((N + m) / 2) * ((b + 1)! * (m !) ^ (b + 1))
        ≤ (2 ^ m * N.choose (N / 2)) * ((b + 1)! * (m !) ^ (b + 1)) :=
          Nat.mul_le_mul_right _ hA
      _ = (2 ^ m * ((b + 1) * m !)) * (N.choose (N / 2) * (b ! * (m !) ^ b)) := by
          rw [Nat.factorial_succ]; ring
      _ ≤ (2 ^ m * ((b + 1) * m !)) * (2 * N !) := Nat.mul_le_mul_left _ ih
      _ = 2 * (((b + 1) * 2 ^ m) * N ! * m !) := by ring
      _ ≤ 2 * ((N + m).choose m * N ! * m !) := by gcongr
      _ = 2 * (N + m)! := by rw [hC]

theorem imprim_bound {b m : ℕ} (hb : 2 ≤ b) (hm : 2 ≤ m) :
    b ! * (m !) ^ b ≤ 2 * (b * m / 2)! * (b * m - b * m / 2)! := by
  have h := imprim_aux m hm b hb
  have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.div_le_self (b * m) 2)
  have hpos : 0 < (b * m).choose (b * m / 2) :=
    Nat.choose_pos (Nat.div_le_self _ _)
  have : (b * m).choose (b * m / 2) * (b ! * (m !) ^ b) ≤
      (b * m).choose (b * m / 2) * (2 * (b * m / 2)! * (b * m - b * m / 2)!) := by
    calc _ ≤ 2 * (b * m)! := h
      _ = 2 * ((b * m).choose (b * m / 2) * (b * m / 2)! * (b * m - b * m / 2)!) := by rw [h1]
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left this hpos

/-- Three parts. -/
theorem three_parts {n δ g : ℕ} (hn : δ + g = n) (hδ : δ ≤ n - n / 2) :
    δ ! * ((g / 2)! * (g - g / 2)!) ≤ (n / 2)! * (n - n / 2)! := by
  have h := prod_factorial_le (ι := Fin 3) ![δ, g / 2, g - g / 2] (n - n / 2) Finset.univ
    (by intro i _; fin_cases i <;> simp <;> omega)
    (by simp [Fin.sum_univ_three]; omega)
  simp only [Fin.prod_univ_three, Fin.sum_univ_three] at h
  simp at h
  have e : δ + g / 2 + (g - g / 2) - (n - n / 2) = n / 2 := by omega
  rw [e] at h
  calc δ ! * ((g / 2)! * (g - g / 2)!) ≤ (n - n / 2)! * (n / 2)! := by
        simpa [mul_assoc] using h
    _ = _ := mul_comm _ _

theorem contra_half {n h I : ℕ} (hh : h * I = n !) (hb : h ≤ 2 * (n / 2)! * (n - n / 2)!) :
    n.choose (n / 2) ≤ 2 * I := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.div_le_self n 2)
  have : n.choose (n / 2) * ((n / 2)! * (n - n / 2)!) ≤ (2 * I) * ((n / 2)! * (n - n / 2)!) := by
    calc n.choose (n / 2) * ((n / 2)! * (n - n / 2)!) = n ! := by rw [← h1]; ring
      _ = h * I := hh.symm
      _ ≤ (2 * (n / 2)! * (n - n / 2)!) * I := Nat.mul_le_mul_right _ hb
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right this (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))

theorem contra_set {n δ g h I : ℕ} (hh : h * I = n !) (hb : h ≤ g ! * δ !) (hn : δ + g = n) :
    n.choose δ ≤ I := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (n := n) (k := δ) (by omega)
  rw [show n - δ = g by omega] at h1
  have : n.choose δ * (δ ! * g !) ≤ I * (δ ! * g !) := by
    calc n.choose δ * (δ ! * g !) = n ! := by rw [← h1]; ring
      _ = h * I := hh.symm
      _ ≤ (g ! * δ !) * I := Nat.mul_le_mul_right _ hb
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right this (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))

theorem choose_ge {n r δ : ℕ} (hr : r ≤ δ) (hδ : δ ≤ n / 2) :
    n.choose r ≤ n.choose δ := by
  induction δ, hr using Nat.le_induction with
  | base => exact le_rfl
  | succ δ hδ' ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

end Lax461425Proofs.DM
