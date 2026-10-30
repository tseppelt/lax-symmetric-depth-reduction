import Lax461425Proofs.DepthHierarchyRichDefs

/-!
The full tree graph `treeG`: connectedness, richness, minor embedding into the full tree pattern,
and the CFI size bound.
-/

namespace Lax461425Proofs.DepthHierarchy

open Lax461425 Lax461425.Forestwidth Lax461425.NonUniformClosure Lax461425.Oddomorphisms
  Lax461425.HomomorphismPolynomials Lax68.GraphMinors

theorem treeG_connected (Δ m : ℕ) : (treeG Δ m).Connected := by
  have key : ∀ (l : List (Fin m)) (h : l.length ≤ Δ),
      (treeG Δ m).Reachable ⟨l, h⟩ ⟨[], Nat.zero_le _⟩ := by
    intro l
    induction l using List.reverseRecOn with
    | nil => intro h; exact SimpleGraph.Reachable.refl _
    | append_singleton l a ih =>
      intro h
      have h' : l.length ≤ Δ := by simp at h; omega
      refine SimpleGraph.Adj.reachable (G := treeG Δ m) (u := ⟨l ++ [a], h⟩) (v := ⟨l, h'⟩) ?_ |>.trans (ih h')
      exact Or.inr ⟨a, rfl⟩
  have : Nonempty {w : List (Fin m) // w.length ≤ Δ} := ⟨⟨[], Nat.zero_le _⟩⟩
  refine ⟨fun x y => ?_⟩
  exact (key x.1 x.2).trans (key y.1 y.2).symm

/-- Subtree of words extending `u`. -/
def subtreeSet (Δ m : ℕ) (u : List (Fin m)) : Set {w : List (Fin m) // w.length ≤ Δ} :=
  {w | u <+: w.1}

theorem subtreeSet_connected (Δ m : ℕ) (u : List (Fin m)) (hu : u.length ≤ Δ) :
    ((treeG Δ m).induce (subtreeSet Δ m u)).Connected := by
  have key : ∀ (s : List (Fin m)) (h : (u ++ s).length ≤ Δ),
      ((treeG Δ m).induce (subtreeSet Δ m u)).Reachable
        ⟨⟨u ++ s, h⟩, List.prefix_append _ _⟩ ⟨⟨u, hu⟩, List.prefix_refl _⟩ := by
    intro s
    induction s using List.reverseRecOn with
    | nil => intro h; simp
    | append_singleton s a ih =>
      intro h
      have h' : (u ++ s).length ≤ Δ := by simp at h ⊢; omega
      have hadj : ((treeG Δ m).induce (subtreeSet Δ m u)).Adj
          ⟨⟨u ++ (s ++ [a]), h⟩, List.prefix_append _ _⟩ ⟨⟨u ++ s, h'⟩, List.prefix_append _ _⟩ := by
        show (treeG Δ m).Adj _ _
        exact Or.inr ⟨a, by simp⟩
      exact hadj.reachable.trans (ih h')
  have : Nonempty (subtreeSet Δ m u) := ⟨⟨⟨u, hu⟩, List.prefix_refl _⟩⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨⟨x, hx⟩, hxp⟩ := x
  obtain ⟨⟨y, hy⟩, hyp⟩ := y
  obtain ⟨sx, hsx⟩ := hxp
  obtain ⟨sy, hsy⟩ := hyp
  simp only at hsx hsy
  subst hsx hsy
  exact (key sx hx).trans (key sy hy).symm

theorem subtreeSet_rich (Δ k : ℕ) : ∀ (j : ℕ) (u : List (Fin (k + 1))), u.length + j + 1 ≤ Δ →
    RichSet (treeG Δ (k + 1)) k j (subtreeSet Δ (k + 1) u) := by
  intro j
  induction j with
  | zero =>
    intro u hu
    refine ⟨subtreeSet_connected Δ _ u (by omega), ?_⟩
    have hlen : ∀ i : Fin (k + 1), (u ++ [i]).length ≤ Δ := fun i => by simp; omega
    let f : Fin (k + 1) → {w : List (Fin (k + 1)) // w.length ≤ Δ} := fun i => ⟨u ++ [i], hlen i⟩
    have hf : Function.Injective f := by
      intro i i' h
      have := congrArg Subtype.val h
      simpa [f] using this
    have hsub : Set.range f ⊆ subtreeSet Δ (k + 1) u := by
      rintro _ ⟨i, rfl⟩
      exact List.prefix_append _ _
    have h1 : (Set.range f).ncard = k + 1 := by
      rw [Set.ncard_range_of_injective hf]; simp
    calc k + 1 = (Set.range f).ncard := h1.symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  | succ j ih =>
    intro u hu
    refine ⟨subtreeSet_connected Δ _ u (by omega), fun i => subtreeSet Δ (k + 1) (u ++ [i]),
      fun i => ⟨?_, ih _ (by simp; omega)⟩, ?_⟩
    · intro w hw
      exact (List.prefix_append u [i]).trans hw
    · intro i i' hne
      rw [Function.onFun, Set.disjoint_left]
      intro w hw hw'
      apply hne
      obtain ⟨s, hs⟩ := hw
      obtain ⟨s', hs'⟩ := hw'
      rw [← hs] at hs'
      simp only [List.append_assoc] at hs'
      have := List.append_cancel_left hs'
      simp only [List.singleton_append] at this
      exact (List.cons.inj this).1.symm

theorem treeG_richSet (Δ k : ℕ) : RichSet (treeG (Δ + 1) (k + 1)) k Δ Set.univ := by
  have := subtreeSet_rich (Δ + 1) k Δ [] (by simp)
  have e : subtreeSet (Δ + 1) (k + 1) [] = Set.univ := by
    ext w; simp [subtreeSet]
  rwa [e] at this

/-- Embedding of the tree words into the two sides of the full tree pattern. -/
noncomputable def treeEmb (Δ k n : ℕ) (h : k + 1 ≤ n) :
    {w : List (Fin (k + 1)) // w.length ≤ Δ} →
      (DepthHierarchy.fullTree Δ n).A ⊕ (DepthHierarchy.fullTree Δ n).B :=
  fun w =>
    if hp : Even w.1.length then
      Sum.inl ⟨w.1.map (Fin.castLE h), by simpa using And.intro w.2 hp⟩
    else Sum.inr ⟨w.1.map (Fin.castLE h), by
      simpa using And.intro w.2 (Nat.not_even_iff_odd.mp hp)⟩

theorem treeEmb_injective (Δ k n : ℕ) (h : k + 1 ≤ n) : Function.Injective (treeEmb Δ k n h) := by
  have hinj : Function.Injective (List.map (Fin.castLE h)) :=
    List.map_injective_iff.mpr (Fin.castLE_injective h)
  intro w w' e
  unfold treeEmb at e
  apply Subtype.ext
  apply hinj
  split_ifs at e with h1 h2 h2
  · exact congrArg Subtype.val (Sum.inl.inj e)
  · exact congrArg Subtype.val (Sum.inr.inj e)

theorem underlying_adj_inl_inr (P : Pattern) (a : P.A) (b : P.B) :
    (underlying P).Adj (Sum.inl a) (Sum.inr b) ↔ P.mult a b ≠ 0 := by
  simp [underlying, SimpleGraph.fromRel_adj]

theorem fullTree_adj (Δ n : ℕ) (a : (DepthHierarchy.fullTree Δ n).A)
    (b : (DepthHierarchy.fullTree Δ n).B)
    (hab : (∃ i, b.1 = a.1 ++ [i]) ∨ ∃ i, a.1 = b.1 ++ [i]) :
    (underlying (DepthHierarchy.fullTree Δ n)).Adj (Sum.inl a) (Sum.inr b) := by
  rw [underlying_adj_inl_inr]
  simp only [DepthHierarchy.fullTree]
  rw [if_pos hab]
  exact one_ne_zero

theorem treeEmb_adj (Δ k n : ℕ) (h : k + 1 ≤ n) {u v : {w : List (Fin (k + 1)) // w.length ≤ Δ}}
    (huv : (treeG Δ (k + 1)).Adj u v) :
    (underlying (DepthHierarchy.fullTree Δ n)).Adj (treeEmb Δ k n h u) (treeEmb Δ k n h v) := by
  have key : ∀ u v : {w : List (Fin (k + 1)) // w.length ≤ Δ}, (∃ i, v.1 = u.1 ++ [i]) →
      (underlying (DepthHierarchy.fullTree Δ n)).Adj (treeEmb Δ k n h u) (treeEmb Δ k n h v) ∨
      (underlying (DepthHierarchy.fullTree Δ n)).Adj (treeEmb Δ k n h v) (treeEmb Δ k n h u) := by
    rintro u v ⟨i, hi⟩
    have hl : v.1.length = u.1.length + 1 := by simp [hi]
    by_cases hp : Even u.1.length
    · have hq : ¬ Even v.1.length := by rw [hl]; simpa [Nat.even_add_one] using hp
      left
      rw [treeEmb, treeEmb, dif_pos hp, dif_neg hq]
      exact fullTree_adj _ _ _ _ (Or.inl ⟨Fin.castLE h i, by simp [hi]⟩)
    · have hq : Even v.1.length := by rw [hl]; simpa [Nat.even_add_one] using hp
      right
      rw [treeEmb, treeEmb, dif_pos hq, dif_neg hp]
      exact fullTree_adj _ _ _ _ (Or.inr ⟨Fin.castLE h i, by simp [hi]⟩)
  rcases huv with hv | hv
  · rcases key u v hv with h1 | h1
    · exact h1
    · exact h1.symm
  · rcases key v u hv with h1 | h1
    · exact h1.symm
    · exact h1

theorem treeG_isMinor {Δ k n : ℕ} (h : k + 1 ≤ n) :
    IsMinor (treeG Δ (k + 1)) (underlying (DepthHierarchy.fullTree Δ n)) := by
  refine ⟨⟨fun w => {treeEmb Δ k n h w}, fun w => ?_, fun {u v} huv => ?_, fun {u v} huv => ?_⟩⟩
  · have : Subsingleton ({treeEmb Δ k n h w} : Set _) := (Set.subsingleton_singleton (a := treeEmb Δ k n h w)).coe_sort
    exact ⟨fun x y => by rw [Subsingleton.elim x y]⟩
  · simp only [Set.disjoint_singleton]
    exact fun e => huv (treeEmb_injective Δ k n h e)
  · exact ⟨_, rfl, _, rfl, treeEmb_adj Δ k n h huv⟩

theorem treeG_ncard_neighbor_le (Δ k : ℕ) (w : {w : List (Fin (k + 1)) // w.length ≤ Δ}) :
    ((treeG Δ (k + 1)).neighborSet w).ncard ≤ k + 2 ∧
      (w.1.length = Δ → ((treeG Δ (k + 1)).neighborSet w).ncard ≤ 1) := by
  let A : Set {w : List (Fin (k + 1)) // w.length ≤ Δ} := {x | ∃ i, x.1 = w.1 ++ [i]}
  let B : Set {w : List (Fin (k + 1)) // w.length ≤ Δ} := {x | x.1 = w.1.dropLast}
  have hB : B.ncard ≤ 1 := by
    rw [Set.ncard_le_one_iff_subsingleton]
    intro x hx y hy
    exact Subtype.ext (hx.trans hy.symm)
  have hA : A.ncard ≤ k + 1 := by
    have : A.ncard ≤ (Set.univ : Set (Fin (k + 1))).ncard := by
      refine Set.ncard_le_ncard_of_injOn (fun x => x.1.getLast?.getD 0) (fun _ _ => trivial) ?_
        (Set.toFinite _)
      rintro x ⟨i, hi⟩ y ⟨j, hj⟩ hxy
      apply Subtype.ext
      simp [hi, hj] at hxy
      rw [hi, hj, hxy]
    simpa using this
  have hsub : (treeG Δ (k + 1)).neighborSet w ⊆ A ∪ B := by
    intro x hx
    rcases hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact Or.inl ⟨i, hi⟩
    · right
      show x.1 = w.1.dropLast
      rw [hi]; simp
  have hsub2 : w.1.length = Δ → (treeG Δ (k + 1)).neighborSet w ⊆ B := by
    intro hw x hx
    rcases hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · have := x.2; rw [hi] at this; simp at this; omega
    · show x.1 = w.1.dropLast
      rw [hi]; simp
  refine ⟨?_, fun hw => ?_⟩
  · calc _ ≤ (A ∪ B).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ A.ncard + B.ncard := Set.ncard_union_le _ _
      _ ≤ k + 2 := by omega
  · exact (Set.ncard_le_ncard (hsub2 hw) (Set.toFinite _)).trans hB

theorem card_words_len (Δ m j : ℕ) (hj : j ≤ Δ) :
    Fintype.card {v : {w : List (Fin m) // w.length ≤ Δ} // v.1.length = j} = m ^ j := by
  have e : {v : {w : List (Fin m) // w.length ≤ Δ} // v.1.length = j} ≃ List.Vector (Fin m) j :=
    { toFun := fun v => ⟨v.1.1, v.2⟩
      invFun := fun l => ⟨⟨l.1, by rw [l.2]; exact hj⟩, l.2⟩
      left_inv := fun v => rfl
      right_inv := fun l => rfl }
  rw [Fintype.card_congr e]
  simp

theorem geom_le (m : ℕ) (hm : 2 ≤ m) (d : ℕ) : ∑ j ∈ Finset.range (d + 1), m ^ j ≤ 2 * m ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ]
    have : 2 * m ^ d ≤ m ^ (d + 1) := by rw [pow_succ]; nlinarith [Nat.zero_le (m ^ d)]
    omega

theorem cfiSize_treeG_le {Δ k : ℕ} (hΔ : 1 ≤ Δ) (hk : 1 ≤ k) :
    cfiSize (treeG Δ (k + 1)) ≤ 2 ^ (k + 3) * (k + 1) ^ (Δ - 1) := by
  classical
  let g : {w : List (Fin (k + 1)) // w.length ≤ Δ} → ℕ :=
    fun v => if v.1.length < Δ then 2 ^ (k + 1) else 1
  have h1 : cfiSize (treeG Δ (k + 1)) ≤ ∑ v, g v := by
    unfold cfiSize
    apply Finset.sum_le_sum
    intro v _
    obtain ⟨h2, h3⟩ := treeG_ncard_neighbor_le Δ k v
    by_cases hv : v.1.length < Δ
    · simp only [g, if_pos hv]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · have : v.1.length = Δ := by have := v.2; omega
      simp only [g, if_neg hv]
      have := h3 this
      calc 2 ^ (((treeG Δ (k + 1)).neighborSet v).ncard - 1) ≤ 2 ^ 0 :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 1 := rfl
  have h2 : ∑ v, g v = ∑ j ∈ Finset.range (Δ + 1), (k + 1) ^ j * (if j < Δ then 2 ^ (k + 1) else 1) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun v => v.1.length) (t := Finset.range (Δ + 1))
      (fun v _ => by simpa [Nat.lt_succ_iff] using v.2)]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ Δ := by simpa [Nat.lt_succ_iff] using hj
    rw [Finset.sum_congr rfl (g := fun _ => if j < Δ then 2 ^ (k + 1) else 1)
      (fun v hv => by simp only [g]; rw [(Finset.mem_filter.mp hv).2])]
    rw [Finset.sum_const, smul_eq_mul]
    congr 1
    rw [← card_words_len Δ (k + 1) j hj', Fintype.card_subtype]
  obtain ⟨d, rfl⟩ : ∃ d, Δ = d + 1 := ⟨Δ - 1, by omega⟩
  rw [h2, Finset.sum_range_succ] at h1
  have h3 : ∑ j ∈ Finset.range (d + 1), (k + 1) ^ j * (if j < d + 1 then 2 ^ (k + 1) else 1)
      = (∑ j ∈ Finset.range (d + 1), (k + 1) ^ j) * 2 ^ (k + 1) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos (Finset.mem_range.mp hj)]
  rw [h3] at h1
  have h4 := geom_le (k + 1) (by omega) d
  have h5 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  simp only [lt_irrefl, if_false, mul_one] at h1
  simp only [Nat.add_sub_cancel]
  calc cfiSize (treeG (d + 1) (k + 1))
      ≤ _ := h1
    _ ≤ (2 * (k + 1) ^ d) * 2 ^ (k + 1) + (k + 1) ^ (d + 1) :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ h4) _
    _ = (k + 1) ^ d * (2 ^ (k + 2) + (k + 1)) := by ring
    _ ≤ (k + 1) ^ d * (2 ^ (k + 2) + 2 ^ k) := by gcongr
    _ ≤ (k + 1) ^ d * 2 ^ (k + 3) := by
        gcongr
        have : 2 ^ (k + 3) = 2 ^ (k + 2) + 2 ^ (k + 2) := by ring
        have : 2 ^ k ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    _ = _ := by ring

end Lax461425Proofs.DepthHierarchy
