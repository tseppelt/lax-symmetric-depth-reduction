import Lax461425Proofs.DMMain
import Lax461425.DixonMortimer

/-!
Discharges the concept axiom `Lax461425.DixonMortimer.exists_fixingSubgroup_inf_alternatingGroup_le`
(Dixon–Mortimer, Theorem 5.2B for `n ≥ 20`).

Proof outline (see `DMMain.lean`): let `Γ` be an orbit of `H` of size `> ⌈n/2⌉`, if there is
one; the pointwise stabiliser `K` of the complement in `H` is normalised by a transitive
family of permutations of `Γ`, so by `DMCore.lean` (Bochert's base bound, Jordan's theorem, and
block-system and orbit counting) it either contains `Alt Γ` or is so small that `H` would have
index `≥ ½ C(n, ⌊n/2⌋)`. If `H` has no large orbit, the same orbit counting applies to `H`
itself. The complement of `Γ` has fewer than `r` points since otherwise the stabiliser of `Γ`
alone would give index `≥ C(n, r)`.
-/

namespace Lax461425Proofs

open Equiv

/--
---
conclusion: Lax461425.DixonMortimer.exists_fixingSubgroup_inf_alternatingGroup_le
---
-/
theorem exists_fixingSubgroup_inf_alternatingGroup_le {n r : ℕ} (hn : 20 ≤ n) (hr : 1 ≤ r)
    (hrn : 2 * r ≤ n) (H : Subgroup (Perm (Fin n)))
    (hhalf : 2 * H.index < n.choose (n / 2)) (hr' : H.index < n.choose r) :
    ∃ T : Set (Fin n), T.ncard < r ∧
      fixingSubgroup (Perm (Fin n)) T ⊓ alternatingGroup (Fin n) ≤ H :=
  DM.dm_main hn hr hrn H hhalf hr'

end Lax461425Proofs
