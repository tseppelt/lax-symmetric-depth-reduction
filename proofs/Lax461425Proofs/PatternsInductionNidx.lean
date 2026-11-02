import Lax461425Proofs.PatternsInductionChild

/-!
Single-side groundwork for `lem:induction`'s internal-gate case: given injective `v : Fin ℓg →
Fin n` (the enumeration of one side of `sup(g)`) and injective `vh : Fin ℓh → Fin n` (the
enumeration of the same side of `sup(h)` for a child `h`), we build:

* `Nidx v vh`, the (as a `Set`) subset of positions of `vh` whose value avoids `range v`;
* `ℓN v vh`, its cardinality, and `yReal v vh : Fin (ℓN v vh) → Fin n`, the induced enumeration of
  `range vh \ range v` (the paper's "`N`", enumerated as a sub-enumeration of `vh`);
* an embedding `ιPad v vh : Fin ℓh ↪ Fin (ℓg + ℓN v vh)`, built by an explicit case split
  (`Fin.castAdd`/`Fin.natAdd`) on whether a position of `vh` lies in `range v` or not, together
  with the **key identity** `append_comp_ιPad`: for *any* permutation `γ1` of `Fin n` fixing
  `range v` pointwise, `(Fin.append v (γ1 ∘ yReal v vh)) ∘ ιPad v vh = γ1 ∘ vh`.

This identity is the algebraic heart of `ψ_h`'s construction: taking `γ1 = 1` recovers
`(Fin.append v (yReal v vh)) ∘ ιPad v vh = vh` (so padding `φ_h` along `ιPad v vh` and evaluating
at the *real* `N`-tuple `yReal v vh` recovers `φ_h` evaluated at `vh` exactly), while taking `γ1`
to be an element moving `yReal v vh` to an arbitrary `y` (via the transitivity lemma of
`PatternsInductionTransitive`) shows that the *same* padded function, evaluated at the
*arbitrary* tuple `y`, equals `φ_h` evaluated at `γ1 ∘ vh` — which is where the sibling gate
`σOf hrig γ1 h` enters, via the equivariance lemmas of `PatternsInductionEquivariant`/
`PatternsInductionHomRename`.
-/

namespace Lax461425Proofs.PatternsInductionNidx

open Lax461425Proofs.PatternsInductionSetup
open scoped Classical

variable {n ℓg ℓh : ℕ}

/-- The positions of `vh` whose value avoids `range v`: the paper's "`N`", on one side. -/
def Nidx (v : Fin ℓg → Fin n) (vh : Fin ℓh → Fin n) : Set (Fin ℓh) :=
  {i | vh i ∉ Set.range v}

/-- The size of `N` on this side. -/
noncomputable def ℓN (v : Fin ℓg → Fin n) (vh : Fin ℓh → Fin n) : ℕ := (Nidx v vh).ncard

/-- The canonical enumeration of `N` on this side, induced by `vh`. -/
noncomputable def Nenum (v : Fin ℓg → Fin n) (vh : Fin ℓh → Fin n) :
    Fin (ℓN v vh) ↪o Fin ℓh := enumOf (Nidx v vh)

/-- **`yReal`**: the induced enumeration of `range vh \ range v`, the paper's real `N`-tuple. -/
noncomputable def yReal (v : Fin ℓg → Fin n) (vh : Fin ℓh → Fin n) : Fin (ℓN v vh) → Fin n :=
  vh ∘ Nenum v vh

variable {v : Fin ℓg → Fin n} {vh : Fin ℓh → Fin n}

/-- `Nenum v vh`'s range is exactly `Nidx v vh`, unfolding `Nenum`'s definition as `enumOf`. -/
theorem range_Nenum : Set.range (Nenum v vh) = Nidx v vh := range_enumOf (Nidx v vh)

theorem yReal_injective (hvh : Function.Injective vh) : Function.Injective (yReal v vh) :=
  hvh.comp (Nenum v vh).injective

theorem range_yReal : Set.range (yReal v vh) = Set.range vh \ Set.range v := by
  ext x
  simp only [yReal, Function.comp_apply, Set.mem_range, Set.mem_sdiff]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨⟨Nenum v vh k, rfl⟩, ?_⟩
    have : (Nenum v vh k : Fin ℓh) ∈ Nidx v vh := by
      rw [← range_Nenum]; exact Set.mem_range_self k
    exact this
  · rintro ⟨⟨i, hi⟩, hnotin⟩
    have hiN : i ∈ Nidx v vh := by rw [← hi] at hnotin; exact hnotin
    have hiN' : i ∈ Set.range (Nenum v vh) := by rw [range_Nenum]; exact hiN
    obtain ⟨k, hk⟩ := hiN'
    exact ⟨k, by rw [hk, hi]⟩

theorem yReal_disjoint_v : ∀ k, yReal v vh k ∉ Set.range v := by
  intro k hmem
  have heq := range_yReal (v := v) (vh := vh)
  have hmemrange : yReal v vh k ∈ Set.range (yReal v vh) := Set.mem_range_self k
  rw [heq] at hmemrange
  exact hmemrange.2 hmem

/-! ### Named inverse-image witnesses -/

variable (hv : Function.Injective v)

/-- The position `j : Fin ℓg` with `v j = vh i`, when `vh i ∈ range v`. -/
noncomputable def jOf {i : Fin ℓh} (hmem : vh i ∈ Set.range v) : Fin ℓg :=
  (Equiv.ofInjective v hv).symm ⟨vh i, hmem⟩

theorem v_jOf {i : Fin ℓh} (hmem : vh i ∈ Set.range v) : v (jOf hv hmem) = vh i :=
  Equiv.apply_ofInjective_symm hv ⟨vh i, hmem⟩

/-- The `N`-index `k : Fin (ℓN v vh)` with `Nenum v vh k = i`, when `vh i ∉ range v`. -/
noncomputable def kOf {i : Fin ℓh} (hmem : vh i ∉ Set.range v) : Fin (ℓN v vh) :=
  (Equiv.ofInjective (Nenum v vh) (Nenum v vh).injective).symm ⟨i, by rw [range_Nenum]; exact hmem⟩

theorem Nenum_kOf {i : Fin ℓh} (hmem : vh i ∉ Set.range v) : Nenum v vh (kOf hmem) = i :=
  Equiv.apply_ofInjective_symm (Nenum v vh).injective ⟨i, by rw [range_Nenum]; exact hmem⟩

theorem yReal_kOf {i : Fin ℓh} (hmem : vh i ∉ Set.range v) : yReal v vh (kOf hmem) = vh i := by
  show vh (Nenum v vh (kOf hmem)) = vh i
  rw [Nenum_kOf hmem]

/-! ### The padding embedding -/

/-- **`ιPad`**: the embedding `Fin ℓh ↪ Fin (ℓg + ℓN v vh)` routing each position of `vh` to the
matching position of `v` (if its value lies in `range v`) or to its `N`-index (otherwise). -/
noncomputable def ιPad (vh : Fin ℓh → Fin n) : Fin ℓh → Fin (ℓg + ℓN v vh) := fun i =>
  if hmem : vh i ∈ Set.range v then
    Fin.castAdd (ℓN v vh) (jOf hv hmem)
  else
    Fin.natAdd ℓg (kOf hmem)

theorem ιPad_apply_of_mem {i : Fin ℓh} (hmem : vh i ∈ Set.range v) :
    ιPad hv vh i = Fin.castAdd (ℓN v vh) (jOf hv hmem) := by
  unfold ιPad; rw [dif_pos hmem]

theorem ιPad_apply_of_notMem {i : Fin ℓh} (hmem : vh i ∉ Set.range v) :
    ιPad hv vh i = Fin.natAdd ℓg (kOf hmem) := by
  unfold ιPad; rw [dif_neg hmem]

/-- `Fin.castAdd`'s and `Fin.natAdd`'s images into `Fin (m + n)` are always disjoint. -/
theorem castAdd_ne_natAdd' {m n : ℕ} (i : Fin m) (j : Fin n) :
    Fin.castAdd n i ≠ Fin.natAdd m j := by
  intro h
  have hval := congrArg Fin.val h
  rw [Fin.val_castAdd, Fin.val_natAdd] at hval
  have := i.isLt
  omega

theorem ιPad_injective (hvh : Function.Injective vh) :
    Function.Injective (ιPad (v := v) hv vh) := by
  intro i j hij
  by_cases hi : vh i ∈ Set.range v
  · by_cases hj : vh j ∈ Set.range v
    · rw [ιPad_apply_of_mem hv hi, ιPad_apply_of_mem hv hj, Fin.castAdd_inj] at hij
      have hveq : v (jOf hv hi) = v (jOf hv hj) := by rw [hij]
      rw [v_jOf hv hi, v_jOf hv hj] at hveq
      exact hvh hveq
    · rw [ιPad_apply_of_mem hv hi, ιPad_apply_of_notMem hv hj] at hij
      exact absurd hij (castAdd_ne_natAdd' _ _)
  · by_cases hj : vh j ∈ Set.range v
    · rw [ιPad_apply_of_notMem hv hi, ιPad_apply_of_mem hv hj] at hij
      exact absurd hij.symm (castAdd_ne_natAdd' _ _)
    · rw [ιPad_apply_of_notMem hv hi, ιPad_apply_of_notMem hv hj, Fin.natAdd_inj] at hij
      have hveq : Nenum v vh (kOf hi) = Nenum v vh (kOf hj) := by rw [hij]
      rwa [Nenum_kOf hi, Nenum_kOf hj] at hveq

/-- `ιPad`, packaged as a bundled `Function.Embedding`. -/
noncomputable def ιPadEmb (hvh : Function.Injective vh) : Fin ℓh ↪ Fin (ℓg + ℓN v vh) :=
  ⟨ιPad hv vh, ιPad_injective hv hvh⟩

/-- **The key identity.** For any permutation `γ1` of `Fin n` fixing `range v` pointwise,
padding `v` with `γ1 ∘ yReal v vh` and composing with `ιPad` recovers `γ1 ∘ vh` exactly. In
particular (`γ1 = 1`), padding `v` with the *real* `N`-tuple `yReal v vh` recovers `vh` exactly. -/
theorem append_comp_ιPad {γ1 : Equiv.Perm (Fin n)}
    (hγ1 : ∀ x ∈ Set.range v, γ1 x = x) :
    (Fin.append v (γ1 ∘ yReal v vh)) ∘ (ιPad hv vh) = γ1 ∘ vh := by
  funext i
  show Fin.append v (γ1 ∘ yReal v vh) (ιPad hv vh i) = γ1 (vh i)
  by_cases hmem : vh i ∈ Set.range v
  · rw [ιPad_apply_of_mem hv hmem, Fin.append_left, v_jOf hv hmem]
    exact (hγ1 (vh i) hmem).symm
  · rw [ιPad_apply_of_notMem hv hmem, Fin.append_right]
    show γ1 (yReal v vh (kOf hmem)) = γ1 (vh i)
    rw [yReal_kOf hmem]

end Lax461425Proofs.PatternsInductionNidx
