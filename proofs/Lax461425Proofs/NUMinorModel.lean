import Lax461425Proofs.NUDefs
import Mathlib

namespace Lax461425Proofs.NU

open Lax461425.HomomorphismPolynomials Lax461425.NonUniformClosure
open Lax871432.ConnectedPartitions Lax871432.HomomorphismCounts
open Lax68.GraphMinors

open scoped Classical

section MM

variable {V W : Type} {G : SimpleGraph V} {U : SimpleGraph W} (M : MinorModel G U)

/-- Union of all branch sets. -/
def mmodel_S : Set W := {w | ∃ v, w ∈ M.branchSet v}

/-- `w` lies in a component of `U` meeting a branch set. -/
def mmodel_R (w : W) : Prop := ∃ s ∈ mmodel_S M, U.Reachable w s

/-- Distance (in walk length) to the union of branch sets. -/
noncomputable def mmodel_lvl (w : W) : ℕ :=
  sInf {n | ∃ s ∈ mmodel_S M, ∃ p : U.Walk w s, p.length = n}

lemma mmodel_step (w : W) (hR : mmodel_R M w) (hS : w ∉ mmodel_S M) :
    ∃ q, U.Adj w q ∧ mmodel_R M q ∧ mmodel_lvl M q < mmodel_lvl M w := by
  obtain ⟨s0, hs0, ⟨p0⟩⟩ := hR
  have hne : {n | ∃ s ∈ mmodel_S M, ∃ p : U.Walk w s, p.length = n}.Nonempty :=
    ⟨_, s0, hs0, p0, rfl⟩
  obtain ⟨s, hs, p, hp⟩ := Nat.sInf_mem hne
  cases p with
  | nil => exact absurd hs hS
  | cons h p' =>
    refine ⟨_, h, ⟨s, hs, ⟨p'⟩⟩, ?_⟩
    have : mmodel_lvl M _ ≤ p'.length := Nat.sInf_le ⟨s, hs, p', rfl⟩
    unfold mmodel_lvl at *
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega

noncomputable def mmodel_par (w : W) : W :=
  if h : mmodel_R M w ∧ w ∉ mmodel_S M then Classical.choose (mmodel_step M w h.1 h.2) else w

lemma mmodel_par_spec {w : W} (hR : mmodel_R M w) (hS : w ∉ mmodel_S M) :
    U.Adj w (mmodel_par M w) ∧ mmodel_R M (mmodel_par M w) ∧
      mmodel_lvl M (mmodel_par M w) < mmodel_lvl M w := by
  unfold mmodel_par
  rw [dif_pos ⟨hR, hS⟩]
  exact Classical.choose_spec (mmodel_step M w hR hS)

lemma mmodel_par_of_mem {w : W} (hS : w ∈ mmodel_S M) : mmodel_par M w = w := by
  unfold mmodel_par
  rw [dif_neg (fun h => h.2 hS)]

lemma mmodel_par_cases (w : W) : mmodel_par M w = w ∨ U.Adj w (mmodel_par M w) := by
  by_cases h : mmodel_R M w ∧ w ∉ mmodel_S M
  · exact Or.inr (mmodel_par_spec M h.1 h.2).1
  · left; unfold mmodel_par; rw [dif_neg h]

lemma mmodel_exists_iter : ∀ k, ∀ w : W, mmodel_lvl M w = k → mmodel_R M w →
    ∃ n, (mmodel_par M)^[n] w ∈ mmodel_S M := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro w hk hR
    by_cases hS : w ∈ mmodel_S M
    · exact ⟨0, hS⟩
    · obtain ⟨_, hRq, hlt⟩ := mmodel_par_spec M hR hS
      obtain ⟨n, hn⟩ := ih _ (hk ▸ hlt) _ rfl hRq
      exact ⟨n + 1, by rwa [Function.iterate_succ_apply]⟩

lemma mmodel_iter_reach (n : ℕ) : ∀ w : W, U.Reachable w ((mmodel_par M)^[n] w) := by
  induction n with
  | zero => intro w; exact SimpleGraph.Reachable.refl w
  | succ n ih =>
    intro w
    rw [Function.iterate_succ_apply]
    have h1 : U.Reachable w (mmodel_par M w) := by
      rcases mmodel_par_cases M w with h | h
      · rw [h]
      · exact h.reachable
    exact h1.trans (ih _)

/-- The extended branch set. -/
def mmodel_Y (v : V) : Set W := {w | ∃ n, (mmodel_par M)^[n] w ∈ M.branchSet v}

lemma mmodel_iter_mem {w : W} {n : ℕ} {v : V} (h : (mmodel_par M)^[n] w ∈ M.branchSet v) (m : ℕ) :
    (mmodel_par M)^[m + n] w = (mmodel_par M)^[n] w := by
  rw [Function.iterate_add_apply]
  exact Function.iterate_fixed (mmodel_par_of_mem M ⟨v, h⟩) m

lemma mmodel_Y_unique {w : W} {u v : V} (hu : w ∈ mmodel_Y M u) (hv : w ∈ mmodel_Y M v) :
    u = v := by
  obtain ⟨n, hn⟩ := hu
  obtain ⟨m, hm⟩ := hv
  by_contra huv
  have h1 := mmodel_iter_mem M hn m
  have h2 := mmodel_iter_mem M hm n
  rw [add_comm] at h2
  rw [h2] at h1
  rw [h1] at hm
  exact Set.disjoint_left.mp (M.disjoint huv) hn hm

lemma mmodel_Y_par {w : W} {v : V} (h : w ∈ mmodel_Y M v) : mmodel_par M w ∈ mmodel_Y M v := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  rw [mmodel_par_of_mem M ⟨v, hn⟩]
  exact hn

lemma mmodel_R_of_Y {w : W} {v : V} (h : w ∈ mmodel_Y M v) : mmodel_R M w := by
  obtain ⟨n, hn⟩ := h
  exact ⟨_, ⟨v, hn⟩, mmodel_iter_reach M n w⟩

lemma mmodel_X_sub_Y (v : V) : M.branchSet v ⊆ mmodel_Y M v := fun _ hx => ⟨0, hx⟩

lemma mmodel_Y_connected (v : V) : (U.induce (mmodel_Y M v)).Connected := by
  obtain ⟨⟨x0, hx0⟩⟩ := (M.connected v).nonempty
  have hsub : M.branchSet v ≤ mmodel_Y M v := mmodel_X_sub_Y M v
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).2 ⟨⟨x0, hsub hx0⟩, ?_⟩
  rintro ⟨w, n, hn⟩
  induction n generalizing w with
  | zero =>
    have hw : w ∈ M.branchSet v := hn
    have hr := (M.connected v).preconnected ⟨x0, hx0⟩ ⟨w, hw⟩
    exact hr.map (SimpleGraph.induceHomOfLE U hsub).toHom
  | succ n ih =>
    have hY : w ∈ mmodel_Y M v := ⟨n + 1, hn⟩
    have hp : mmodel_par M w ∈ mmodel_Y M v := mmodel_Y_par M hY
    have hn' : (mmodel_par M)^[n] (mmodel_par M w) ∈ M.branchSet v := by
      rw [← Function.iterate_succ_apply]; exact hn
    have ih' := ih (mmodel_par M w) hn'
    rcases mmodel_par_cases M w with h | h
    · have : (⟨mmodel_par M w, hp⟩ : mmodel_Y M v) = ⟨w, hY⟩ := Subtype.ext h
      rw [this] at ih'
      exact ih'
    · exact ih'.trans (SimpleGraph.Adj.reachable (show (U.induce (mmodel_Y M v)).Adj
        ⟨mmodel_par M w, hp⟩ ⟨w, hY⟩ from h.symm))

lemma mmodel_ex_owner {w : W} (h : mmodel_R M w) : ∃ v, w ∈ mmodel_Y M v := by
  obtain ⟨s, _, _⟩ := h
  obtain ⟨n, v, hv⟩ := mmodel_exists_iter M _ w rfl ⟨s, ‹_›, ‹_›⟩
  exact ⟨v, n, hv⟩

noncomputable def mmodel_lab (w : W) : V ⊕ U.ConnectedComponent :=
  if h : mmodel_R M w then Sum.inl (Classical.choose (mmodel_ex_owner M h))
  else Sum.inr (U.connectedComponentMk w)

lemma mmodel_lab_inl_iff (w : W) (v : V) : mmodel_lab M w = Sum.inl v ↔ w ∈ mmodel_Y M v := by
  constructor
  · intro h
    unfold mmodel_lab at h
    by_cases hR : mmodel_R M w
    · rw [dif_pos hR] at h
      have := Classical.choose_spec (mmodel_ex_owner M hR)
      rw [Sum.inl.injEq] at h
      rwa [h] at this
    · rw [dif_neg hR] at h; exact absurd h (by simp)
  · intro h
    have hR := mmodel_R_of_Y M h
    unfold mmodel_lab
    rw [dif_pos hR]
    congr 1
    exact mmodel_Y_unique M (Classical.choose_spec (mmodel_ex_owner M hR)) h

lemma mmodel_lab_inr {w : W} (h : ¬ mmodel_R M w) :
    mmodel_lab M w = Sum.inr (U.connectedComponentMk w) := by
  unfold mmodel_lab; rw [dif_neg h]

lemma mmodel_R_reach {a b : W} (h : U.Reachable a b) : mmodel_R M a ↔ mmodel_R M b := by
  constructor
  · rintro ⟨s, hs, hr⟩; exact ⟨s, hs, h.symm.trans hr⟩
  · rintro ⟨s, hs, hr⟩; exact ⟨s, hs, h.trans hr⟩

/-- The setoid with the extended branch sets and the components not meeting any branch set. -/
noncomputable def mmodel_setoid : Setoid W := Setoid.ker (mmodel_lab M)

lemma mmodel_mk_eq (a b : W) :
    (Quotient.mk (mmodel_setoid M) a = Quotient.mk (mmodel_setoid M) b) ↔
      mmodel_lab M a = mmodel_lab M b := by
  rw [Quotient.eq]; exact Iff.rfl

noncomputable def mmodel_connPart : ConnPart U where
  setoid := mmodel_setoid M
  connected := by
    intro a
    induction a using Quotient.inductionOn with
    | _ w =>
      by_cases hR : mmodel_R M w
      · obtain ⟨v, hv⟩ := mmodel_ex_owner M hR
        have : {x | Quotient.mk (mmodel_setoid M) x = Quotient.mk (mmodel_setoid M) w} =
            mmodel_Y M v := by
          ext x
          simp only [Set.mem_ofPred_eq]
          rw [mmodel_mk_eq, (mmodel_lab_inl_iff M w v).2 hv, mmodel_lab_inl_iff]
        rw [this]
        exact mmodel_Y_connected M v
      · have : {x | Quotient.mk (mmodel_setoid M) x = Quotient.mk (mmodel_setoid M) w} =
            (U.connectedComponentMk w).supp := by
          ext x
          simp only [Set.mem_ofPred_eq, SimpleGraph.ConnectedComponent.mem_supp_iff]
          rw [mmodel_mk_eq, mmodel_lab_inr M hR]
          constructor
          · intro h
            by_cases hx : mmodel_R M x
            · unfold mmodel_lab at h
              rw [dif_pos hx] at h
              exact absurd h (by simp)
            · rw [mmodel_lab_inr M hx] at h
              exact (Sum.inr.inj h)
          · intro h
            have hxw : U.Reachable x w := SimpleGraph.ConnectedComponent.eq.1 h
            have hx : ¬ mmodel_R M x := fun hx => hR ((mmodel_R_reach M hxw).1 hx)
            rw [mmodel_lab_inr M hx, h]
        rw [this]
        exact (U.connectedComponentMk w).connected_toSimpleGraph

end MM

/-- A connected minor model, completed to a partition into connected parts: if a connected `G`
is a minor of `U`, there are a partition `𝓡` into connected parts and an injection `ι` of `V(G)`
into the classes such that `G`-edges become edges of `U/𝓡` and all classes outside the range of
`ι` are isolated in `U/𝓡`. -/
theorem exists_connPart_of_isMinor {V W : Type} {G : SimpleGraph V} (hG : G.Connected)
    {U : SimpleGraph W} (h : IsMinor G U) :
    ∃ (𝓡 : ConnPart U) (ι : V → Quotient 𝓡.setoid), Function.Injective ι ∧
      (∀ u v, G.Adj u v → 𝓡.quotientGraph.Adj (ι u) (ι v)) ∧
      ∀ q, q ∉ Set.range ι → ∀ q', ¬ 𝓡.quotientGraph.Adj q q' := by
  obtain ⟨M⟩ := h
  have hne : ∀ v, ∃ x, x ∈ M.branchSet v := fun v => by
    obtain ⟨⟨x, hx⟩⟩ := (M.connected v).nonempty
    exact ⟨x, hx⟩
  choose x hx using hne
  have hlab : ∀ v w, w ∈ M.branchSet v → mmodel_lab M w = Sum.inl v := fun v w hw =>
    (mmodel_lab_inl_iff M w v).2 (mmodel_X_sub_Y M v hw)
  refine ⟨mmodel_connPart M, fun v => Quotient.mk (mmodel_setoid M) (x v), ?_, ?_, ?_⟩
  · intro u v huv
    have := (mmodel_mk_eq M _ _).1 huv
    rw [hlab u _ (hx u), hlab v _ (hx v)] at this
    exact Sum.inl.inj this
  · intro u v huv
    refine ⟨?_, ?_⟩
    · intro heq
      have := (mmodel_mk_eq M _ _).1 heq
      rw [hlab u _ (hx u), hlab v _ (hx v)] at this
      exact G.ne_of_adj huv (Sum.inl.inj this)
    · obtain ⟨a, ha, b, hb, hab⟩ := M.adjacent huv
      refine ⟨a, b, hab, ?_, ?_⟩
      · exact (mmodel_mk_eq M _ _).2 (by rw [hlab u _ ha, hlab u _ (hx u)])
      · exact (mmodel_mk_eq M _ _).2 (by rw [hlab v _ hb, hlab v _ (hx v)])
  · intro q hq q' hadj
    obtain ⟨hne, a, b, hab, ha, hb⟩ := hadj
    have ha' : Quotient.mk (mmodel_setoid M) a = q := ha
    have hb' : Quotient.mk (mmodel_setoid M) b = q' := hb
    by_cases hR : mmodel_R M a
    · obtain ⟨v, hv⟩ := mmodel_ex_owner M hR
      apply hq
      refine ⟨v, ?_⟩
      rw [← ha']
      exact (mmodel_mk_eq M _ _).2 (by
        rw [(mmodel_lab_inl_iff M a v).2 hv, hlab v _ (hx v)])
    · have hR' : ¬ mmodel_R M b := fun hb => hR ((mmodel_R_reach M hab.reachable).2 hb)
      apply hne
      rw [← ha', ← hb']
      exact (mmodel_mk_eq M _ _).2 (by
        rw [mmodel_lab_inr M hR, mmodel_lab_inr M hR']
        congr 1
        exact SimpleGraph.ConnectedComponent.eq.2 hab.reachable)

end Lax461425Proofs.NU
