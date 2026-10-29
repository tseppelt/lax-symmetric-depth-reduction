import Mathlib.Data.Fintype.Pigeonhole
import Lax461425Proofs.PatternsSupportBasic

/-!
A per-gate handle on `supportChanges`/`supportDepth`: `sc C g` is the maximum number of
support-changing wires on a path of `C` *starting at* `g` (matching the paper's `sc(g)`), as
opposed to `Supports.supportDepth`, which is `sSup`'d over *all* paths of the whole circuit with
no fixed starting point.

We show:

* paths cannot be longer than `Fintype.card C.Gate` (acyclicity), so the various `sSup`s below
  are genuine maxima, not the junk `0` value of an unbounded set (`isPath_card_le`,
  `sc_set_bddAbove`);
* `sc C g ≤ supportDepth C` for every gate `g` (`sc_le_supportDepth`), since a path starting at
  `g` is in particular a path of the whole circuit;
* a recursive bound: if `h` is a child of `g`, the support-changing count on any path starting
  at `h`, plus one more if the wire `g → h` is itself support-changing, is still realised by a
  path starting at `g`, hence bounded by `sc C g` (`sc_recursive_le`).
-/

namespace Lax461425Proofs.PatternsSupportDepth

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportBasic

variable {V K : Type*} {C : Circuit V K}

/-- Building a `TransGen` chain from a sequence of consecutive wire steps. -/
theorem transGen_of_chain {q : ℕ → C.Gate} {m : ℕ}
    (hq : ∀ k, k < m → 0 < C.wire (q k) (q (k + 1))) (a : ℕ) :
    ∀ b, a < b → b ≤ m → Relation.TransGen (fun h g => 0 < C.wire g h) (q b) (q a) := by
  intro b
  induction b with
  | zero => intro h; omega
  | succ b ih =>
    intro hab hbm
    rcases Nat.lt_or_ge a b with h | h
    · exact Relation.TransGen.head (hq b (by omega)) (ih h (by omega))
    · have heq : a = b := by omega
      rw [heq]
      exact Relation.TransGen.single (hq b (by omega))

/-- A path cannot be longer than the number of gates: acyclicity forces its gates to be
pairwise distinct. -/
theorem isPath_card_le {m : ℕ} {p : Fin (m + 1) → C.Gate} (hp : C.IsPath p) :
    m + 1 ≤ Fintype.card C.Gate := by
  by_contra hcon
  push Not at hcon
  set q : ℕ → C.Gate := fun k => if h : k < m + 1 then p ⟨k, h⟩ else p ⟨0, by omega⟩ with hqdef
  have hqeq : ∀ i : Fin (m + 1), q i.val = p i := by
    intro i
    simp only [hqdef, i.isLt, dif_pos]
  have hq : ∀ k, k < m → 0 < C.wire (q k) (q (k + 1)) := by
    intro k hkm
    have hk1 : (⟨k, by omega⟩ : Fin (m + 1)) = (⟨k, by omega⟩ : Fin m).castSucc := rfl
    have hk2 : (⟨k + 1, by omega⟩ : Fin (m + 1)) = (⟨k, by omega⟩ : Fin m).succ := rfl
    rw [show q k = p ⟨k, by omega⟩ from hqeq ⟨k, by omega⟩,
      show q (k + 1) = p ⟨k + 1, by omega⟩ from hqeq ⟨k + 1, by omega⟩, hk1, hk2]
    exact hp ⟨k, hkm⟩
  obtain ⟨i, j, hij, hpij⟩ := Fintype.exists_ne_map_eq_of_card_lt p
    (by rw [Fintype.card_fin]; omega)
  have aux : ∀ i j : Fin (m + 1), i.val < j.val → p i = p j → False := by
    intro i j hlt heq
    have hT := transGen_of_chain hq i.val j.val hlt (by omega)
    rw [hqeq j, hqeq i, ← heq] at hT
    exact C.acyclic (p i) hT
  rcases lt_or_lt_iff_ne.mpr hij with hlt | hlt
  · exact aux i j hlt hpij
  · exact aux j i hlt hpij.symm

variable {n : ℕ}

/-- The number of support-changing wires on a path of length `m` is at most `m`. -/
theorem supportChanges_le {C : Circuit (Fin n × Fin n) K} {m : ℕ} (p : Fin (m + 1) → C.Gate) :
    supportChanges C p ≤ m := by
  have h1 : (supportChanges C p) ≤ (Set.univ : Set (Fin m)).ncard :=
    Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h1

variable {C : Circuit (Fin n × Fin n) K}

/-- The candidate set defining `C.depth` is bounded above by `Fintype.card C.Gate`. -/
theorem depth_set_bddAbove : BddAbove {m : ℕ | ∃ p : Fin (m + 1) → C.Gate, C.IsPath p} := by
  refine ⟨Fintype.card C.Gate, ?_⟩
  rintro m ⟨p, hp⟩
  have := isPath_card_le hp
  omega

/-- The candidate set defining `supportDepth` (in its "small support size" branch) is bounded
above by `Fintype.card C.Gate`. -/
theorem supportDepth_set_bddAbove :
    BddAbove {c | ∃ (m : ℕ) (p : Fin (m + 1) → C.Gate), C.IsPath p ∧ supportChanges C p = c} := by
  refine ⟨Fintype.card C.Gate, ?_⟩
  rintro c ⟨m, p, hp, rfl⟩
  have h1 := supportChanges_le p
  have h2 := isPath_card_le hp
  omega

/-- `sc C g`: the maximum number of support-changing wires on a path of `C` *starting at* `g`. -/
noncomputable def sc (C : Circuit (Fin n × Fin n) K) (g : C.Gate) : ℕ :=
  sSup {c | ∃ (m : ℕ) (p : Fin (m + 1) → C.Gate), p 0 = g ∧ C.IsPath p ∧ supportChanges C p = c}

/-- The trivial, length-`0` path witnesses that `sc`'s candidate set is nonempty. -/
theorem sc_set_nonempty (g : C.Gate) :
    {c | ∃ (m : ℕ) (p : Fin (m + 1) → C.Gate), p 0 = g ∧ C.IsPath p ∧
      supportChanges C p = c}.Nonempty := by
  refine ⟨0, 0, fun _ => g, rfl, fun i => i.elim0, ?_⟩
  have : ({i : Fin 0 | ¬ minSupport C ((fun _ : Fin 1 => g) i.succ) ⊆
      minSupport C ((fun _ : Fin 1 => g) i.castSucc)} : Set (Fin 0)) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr (fun i _ => i.elim0)
  show ({i : Fin 0 | ¬ minSupport C ((fun _ : Fin 1 => g) i.succ) ⊆
      minSupport C ((fun _ : Fin 1 => g) i.castSucc)} : Set (Fin 0)).ncard = 0
  rw [this, Set.ncard_empty]

/-- `sc`'s candidate set is bounded above by `Fintype.card C.Gate`. -/
theorem sc_set_bddAbove (g : C.Gate) :
    BddAbove {c | ∃ (m : ℕ) (p : Fin (m + 1) → C.Gate), p 0 = g ∧ C.IsPath p ∧
      supportChanges C p = c} := by
  refine ⟨Fintype.card C.Gate, ?_⟩
  rintro c ⟨m, p, -, hp, rfl⟩
  have h1 := supportChanges_le p
  have h2 := isPath_card_le hp
  omega

/-- `sc C g` is realised by an actual path starting at `g`. -/
theorem sc_spec (g : C.Gate) :
    ∃ (m : ℕ) (p : Fin (m + 1) → C.Gate), p 0 = g ∧ C.IsPath p ∧ supportChanges C p = sc C g :=
  Nat.sSup_mem (sc_set_nonempty g) (sc_set_bddAbove g)

/-- Any path starting at `g` has at most `sc C g` support-changing wires. -/
theorem supportChanges_le_sc {g : C.Gate} {m : ℕ} {p : Fin (m + 1) → C.Gate}
    (hp0 : p 0 = g) (hp : C.IsPath p) : supportChanges C p ≤ sc C g :=
  le_csSup (sc_set_bddAbove g) ⟨m, p, hp0, hp, rfl⟩

/-- `sc C g ≤ supportDepth C`. A path starting at `g` is in particular a path of the whole
circuit (in the "small support size" branch), or its length already bounds it by `C.depth`
(the other branch), and `supportDepth C ≤ C.depth` in general. -/
theorem sc_le_supportDepth (g : C.Gate) : sc C g ≤ supportDepth C := by
  unfold Lax461425.Supports.supportDepth
  split
  · refine csSup_le (sc_set_nonempty g) ?_
    rintro c ⟨m, p, -, hp, rfl⟩
    exact le_csSup supportDepth_set_bddAbove ⟨m, p, hp, rfl⟩
  · refine csSup_le (sc_set_nonempty g) ?_
    rintro c ⟨m, p, -, hp, rfl⟩
    have h1 := supportChanges_le p
    have h2 : m ≤ C.depth := le_csSup depth_set_bddAbove ⟨p, hp⟩
    omega

/-- If `h` is a child of `g` (`0 < C.wire g h`), then `sc C h ≤ sc C g`: prepending the wire
`g → h` to a witnessing path for `h` gives a path for `g` with at least as many
support-changing wires.

(We were only able to establish this weaker monotonicity statement, not the sharper recursive
bound `sc C h + (1 if g → h is support-changing else 0) ≤ sc C g` suggested in the task
description: the sharper version needs an exact count of the index set of the extended path,
which requires more `Fin`-indexing bookkeeping than we could cleanly push through. The
monotonicity statement here is still directly usable for bounding `sc` along any path towards
the root.) -/
theorem sc_mono {g h : C.Gate} (hwire : 0 < C.wire g h) : sc C h ≤ sc C g := by
  obtain ⟨m, p, hp0, hpath, hpc⟩ := sc_spec h
  set p' : Fin (m + 2) → C.Gate := Fin.cons g p with hp'def
  have hp'0 : p' 0 = g := by simp [hp'def]
  have hp'1 : p' (1 : Fin (m + 2)) = h := by
    have e : (1 : Fin (m + 2)) = (0 : Fin (m + 1)).succ := rfl
    rw [e, hp'def, Fin.cons_succ, hp0]
  have hp'path : C.IsPath p' := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · have e1 : (0 : Fin (m + 1)).castSucc = (0 : Fin (m + 2)) := rfl
      have e2 : (0 : Fin (m + 1)).succ = (1 : Fin (m + 2)) := rfl
      show 0 < C.wire (p' (0 : Fin (m + 1)).castSucc) (p' (0 : Fin (m + 1)).succ)
      rw [e1, e2, hp'0, hp'1]
      exact hwire
    · have e1 : (j.succ).castSucc = (j.castSucc).succ := by
        apply Fin.ext
        simp
      show 0 < C.wire (p' (j.succ).castSucc) (p' (j.succ).succ)
      rw [e1, hp'def, Fin.cons_succ, Fin.cons_succ]
      exact hpath j
  have hsub : (Fin.succ '' {j : Fin m | ¬ minSupport C (p j.succ) ⊆ minSupport C (p j.castSucc)})
      ⊆ {i : Fin (m + 1) | ¬ minSupport C (p' i.succ) ⊆ minSupport C (p' i.castSucc)} := by
    rintro _ ⟨j, hj, rfl⟩
    have e1 : (j.succ).castSucc = (j.castSucc).succ := by
      apply Fin.ext
      simp
    show ¬ minSupport C (p' (j.succ).succ) ⊆ minSupport C (p' (j.succ).castSucc)
    rw [e1, hp'def, Fin.cons_succ, Fin.cons_succ]
    exact hj
  have hle : supportChanges C p ≤ supportChanges C p' := by
    show ({j : Fin m | ¬ minSupport C (p j.succ) ⊆ minSupport C (p j.castSucc)} : Set (Fin m)).ncard
        ≤ ({i : Fin (m + 1) | ¬ minSupport C (p' i.succ) ⊆
          minSupport C (p' i.castSucc)} : Set (Fin (m + 1))).ncard
    calc ({j : Fin m | ¬ minSupport C (p j.succ) ⊆ minSupport C (p j.castSucc)} : Set (Fin m)).ncard
        = (Fin.succ '' {j : Fin m | ¬ minSupport C (p j.succ) ⊆
            minSupport C (p j.castSucc)}).ncard :=
          (Set.ncard_image_of_injective _ (Fin.succ_injective m)).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  calc sc C h = supportChanges C p := hpc.symm
    _ ≤ supportChanges C p' := hle
    _ ≤ sc C g := supportChanges_le_sc hp'0 hp'path

/-- The sharper recursive bound: if `h` is a child of `g` (`0 < C.wire g h`) via a
support-changing wire (`¬ minSupport C h ⊆ minSupport C g`), then `sc C h + 1 ≤ sc C g`. Unlike
`sc_mono`, this tracks that the prepended wire `g → h` itself contributes a *new*
support-changing index (index `0`) to the extended path, disjoint from the indices inherited
(via `Fin.succ`) from the witnessing path for `h`, since `0` is never in the range of
`Fin.succ`. -/
theorem sc_succ_le_of_changing {g h : C.Gate} (hwire : 0 < C.wire g h)
    (hchg : ¬ minSupport C h ⊆ minSupport C g) : sc C h + 1 ≤ sc C g := by
  obtain ⟨m, p, hp0, hpath, hpc⟩ := sc_spec h
  set p' : Fin (m + 2) → C.Gate := Fin.cons g p with hp'def
  have hp'0 : p' 0 = g := by simp [hp'def]
  have hp'1 : p' (1 : Fin (m + 2)) = h := by
    have e : (1 : Fin (m + 2)) = (0 : Fin (m + 1)).succ := rfl
    rw [e, hp'def, Fin.cons_succ, hp0]
  have hp'path : C.IsPath p' := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · have e1 : (0 : Fin (m + 1)).castSucc = (0 : Fin (m + 2)) := rfl
      have e2 : (0 : Fin (m + 1)).succ = (1 : Fin (m + 2)) := rfl
      show 0 < C.wire (p' (0 : Fin (m + 1)).castSucc) (p' (0 : Fin (m + 1)).succ)
      rw [e1, e2, hp'0, hp'1]
      exact hwire
    · have e1 : (j.succ).castSucc = (j.castSucc).succ := by
        apply Fin.ext
        simp
      show 0 < C.wire (p' (j.succ).castSucc) (p' (j.succ).succ)
      rw [e1, hp'def, Fin.cons_succ, Fin.cons_succ]
      exact hpath j
  have hsub : (Fin.succ '' {j : Fin m | ¬ minSupport C (p j.succ) ⊆ minSupport C (p j.castSucc)})
      ⊆ {i : Fin (m + 1) | ¬ minSupport C (p' i.succ) ⊆ minSupport C (p' i.castSucc)} := by
    rintro _ ⟨j, hj, rfl⟩
    have e1 : (j.succ).castSucc = (j.castSucc).succ := by
      apply Fin.ext
      simp
    show ¬ minSupport C (p' (j.succ).succ) ⊆ minSupport C (p' (j.succ).castSucc)
    rw [e1, hp'def, Fin.cons_succ, Fin.cons_succ]
    exact hj
  have h0mem : (0 : Fin (m + 1)) ∈
      {i : Fin (m + 1) | ¬ minSupport C (p' i.succ) ⊆ minSupport C (p' i.castSucc)} := by
    have e1 : (0 : Fin (m + 1)).castSucc = (0 : Fin (m + 2)) := rfl
    have e2 : (0 : Fin (m + 1)).succ = (1 : Fin (m + 2)) := rfl
    show ¬ minSupport C (p' (0 : Fin (m + 1)).succ) ⊆ minSupport C (p' (0 : Fin (m + 1)).castSucc)
    rw [e1, e2, hp'0, hp'1]
    exact hchg
  have h0notmem : (0 : Fin (m + 1)) ∉
      (Fin.succ '' {j : Fin m | ¬ minSupport C (p j.succ) ⊆ minSupport C (p j.castSucc)}) := by
    rintro ⟨j, -, hj⟩
    exact Fin.succ_ne_zero j hj
  have hinsub : insert (0 : Fin (m + 1))
      (Fin.succ '' {j : Fin m | ¬ minSupport C (p j.succ) ⊆ minSupport C (p j.castSucc)})
      ⊆ {i : Fin (m + 1) | ¬ minSupport C (p' i.succ) ⊆ minSupport C (p' i.castSucc)} := by
    intro x hx
    rcases hx with rfl | hx
    · exact h0mem
    · exact hsub hx
  have hcard : (insert (0 : Fin (m + 1))
      (Fin.succ '' {j : Fin m | ¬ minSupport C (p j.succ) ⊆ minSupport C (p j.castSucc)})).ncard
      ≤ ({i : Fin (m + 1) | ¬ minSupport C (p' i.succ) ⊆ minSupport C (p' i.castSucc)} :
        Set (Fin (m + 1))).ncard :=
    Set.ncard_le_ncard hinsub (Set.toFinite _)
  have hinsertcard : (insert (0 : Fin (m + 1))
      (Fin.succ '' {j : Fin m | ¬ minSupport C (p j.succ) ⊆ minSupport C (p j.castSucc)})).ncard
      = (Fin.succ '' {j : Fin m | ¬ minSupport C (p j.succ) ⊆
          minSupport C (p j.castSucc)}).ncard + 1 :=
    Set.ncard_insert_of_notMem h0notmem (Set.toFinite _)
  have himgcard : (Fin.succ '' {j : Fin m | ¬ minSupport C (p j.succ) ⊆
      minSupport C (p j.castSucc)}).ncard
      = ({j : Fin m | ¬ minSupport C (p j.succ) ⊆ minSupport C (p j.castSucc)} :
        Set (Fin m)).ncard :=
    Set.ncard_image_of_injective _ (Fin.succ_injective m)
  have hfinal : ({j : Fin m | ¬ minSupport C (p j.succ) ⊆ minSupport C (p j.castSucc)} :
      Set (Fin m)).ncard + 1
      ≤ ({i : Fin (m + 1) | ¬ minSupport C (p' i.succ) ⊆ minSupport C (p' i.castSucc)} :
        Set (Fin (m + 1))).ncard := by omega
  calc sc C h + 1 = supportChanges C p + 1 := by rw [hpc]
    _ ≤ supportChanges C p' := hfinal
    _ ≤ sc C g := supportChanges_le_sc hp'0 hp'path
