import Lax461425Proofs.DepthHierarchyRichDefs

/-!
Basic facts about richness: invariance under isomorphism, passing from a minor to the graph,
`K₁` is not rich, and a rich underlying graph excludes a depth-`Δ` decomposition with small bags.
-/

namespace Lax461425Proofs.DepthHierarchy

open Lax461425 Lax461425.Forestwidth Lax461425.NonUniformClosure Lax461425.Oddomorphisms
  Lax461425.HomomorphismPolynomials Lax68.GraphMinors

namespace RichBasic

/-! ### Connectivity of vertex sets via reflexive-transitive closure -/

/-- Any two vertices of `S` are joined by a path inside `S`. -/
def ConnSet {V : Type*} (F : SimpleGraph V) (S : Set V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ F.Adj x y) a b

lemma connSet_of_connected {V : Type*} {F : SimpleGraph V} {S : Set V}
    (h : (F.induce S).Connected) : S.Nonempty ∧ ConnSet F S := by
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨v, hv⟩⟩ := h.nonempty
    exact ⟨v, hv⟩
  · intro a ha b hb
    obtain ⟨w⟩ := h.preconnected ⟨a, ha⟩ ⟨b, hb⟩
    suffices H : ∀ (x y : S) (_ : (F.induce S).Walk x y),
        Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ F.Adj x y) x.1 y.1 from H _ _ w
    intro x y w
    induction w with
    | nil => exact Relation.ReflTransGen.refl
    | @cons x z y hadj _ ih => exact Relation.ReflTransGen.head ⟨x.2, z.2, hadj⟩ ih

lemma connected_of_connSet {V : Type*} {F : SimpleGraph V} {S : Set V}
    (hne : S.Nonempty) (h : ConnSet F S) : (F.induce S).Connected := by
  haveI : Nonempty S := hne.to_subtype
  rw [SimpleGraph.connected_iff]
  refine ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => ?_, this⟩
  have key : ∀ c, Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ F.Adj x y) a c →
      ∃ hc : c ∈ S, (F.induce S).Reachable ⟨a, ha⟩ ⟨c, hc⟩ := by
    intro c hc
    induction hc with
    | refl => exact ⟨ha, SimpleGraph.Reachable.refl _⟩
    | @tail b' c' _ hbc ih =>
      obtain ⟨hb', hr⟩ := ih
      exact ⟨hbc.2.1, hr.trans (SimpleGraph.Adj.reachable (show (F.induce S).Adj ⟨b', hb'⟩ ⟨c', hbc.2.1⟩ from hbc.2.2))⟩
  obtain ⟨_, hr⟩ := key b (h a ha b hb)
  exact hr

/-! ### Nonemptiness, isomorphism -/

lemma RichSet.nonempty {V : Type*} {F : SimpleGraph V} {k : ℕ} :
    ∀ {j S}, RichSet F k j S → S.Nonempty
  | 0, S, h => (connSet_of_connected h.1).1
  | j + 1, S, h => (connSet_of_connected h.1).1

lemma richSet_map {V W : Type*} {F : SimpleGraph V} {G : SimpleGraph W} (e : F ≃g G) (k : ℕ) :
    ∀ j S, RichSet F k j S → RichSet G k j (e '' S) := by
  intro j
  induction j with
  | zero =>
    intro S hS
    obtain ⟨hne, hc⟩ := connSet_of_connected hS.1
    refine ⟨connected_of_connSet (hne.image _) ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      refine (hc a ha b hb).lift e ?_
      rintro x y ⟨hx, hy, hxy⟩
      exact ⟨Set.mem_image_of_mem _ hx, Set.mem_image_of_mem _ hy, e.map_adj_iff.2 hxy⟩
    · rw [Set.ncard_image_of_injective _ e.injective]
      exact hS.2
  | succ j ih =>
    intro S hS
    obtain ⟨hne, hc⟩ := connSet_of_connected hS.1
    obtain ⟨T, hT, hdisj⟩ := hS.2
    refine ⟨connected_of_connSet (hne.image _) ?_, fun i => e '' T i, fun i => ⟨?_, ih _ (hT i).2⟩, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      refine (hc a ha b hb).lift e ?_
      rintro x y ⟨hx, hy, hxy⟩
      exact ⟨Set.mem_image_of_mem _ hx, Set.mem_image_of_mem _ hy, e.map_adj_iff.2 hxy⟩
    · exact Set.image_mono (hT i).1
    · intro i i' hii'
      exact (Set.disjoint_image_iff e.injective).2 (hdisj hii')

/-! ### Minors -/

lemma connSet_biUnion {V W : Type*} {G : SimpleGraph W} {F : SimpleGraph V} (B : W → Set V)
    (hBc : ∀ w, ConnSet F (B w))
    (hBn : ∀ w, (B w).Nonempty)
    (hadj : ∀ ⦃u v⦄, G.Adj u v → ∃ x ∈ B u, ∃ y ∈ B v, F.Adj x y)
    {S : Set W} (hS : ConnSet G S) : ConnSet F (⋃ v ∈ S, B v) := by
  set U : Set V := ⋃ v ∈ S, B v with hU
  have hBU : ∀ v ∈ S, B v ⊆ U := fun v hv x hx => Set.mem_biUnion hv hx
  have inB : ∀ v ∈ S, ∀ x ∈ B v, ∀ y ∈ B v,
      Relation.ReflTransGen (fun x y => x ∈ U ∧ y ∈ U ∧ F.Adj x y) x y := by
    intro v hv x hx y hy
    refine (hBc v x hx y hy).lift id ?_
    rintro a b ⟨ha, hb, hab⟩
    exact ⟨hBU v hv ha, hBU v hv hb, hab⟩
  have key : ∀ v ∈ S, ∀ w, Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ G.Adj x y) v w →
      ∀ x ∈ B v, ∀ y ∈ B w,
        Relation.ReflTransGen (fun x y => x ∈ U ∧ y ∈ U ∧ F.Adj x y) x y := by
    intro v hv w hw x hx
    induction hw with
    | refl => exact fun y hy => inB v hv x hx y hy
    | @tail w' w'' _ hstep ih =>
      intro y hy
      obtain ⟨x1, hx1, x2, hx2, h12⟩ := hadj hstep.2.2
      refine (ih x1 hx1).trans ?_
      refine Relation.ReflTransGen.head ⟨hBU _ hstep.1 hx1, hBU _ hstep.2.1 hx2, h12⟩ ?_
      exact inB _ hstep.2.1 _ hx2 _ hy
  intro a ha b hb
  obtain ⟨v, hv, hav⟩ := Set.mem_iUnion₂.1 ha
  obtain ⟨w, hw, hbw⟩ := Set.mem_iUnion₂.1 hb
  exact key v hv w (hS v hv w hw) a hav b hbw

lemma exists_finite_connSet {V : Type*} (F : SimpleGraph V) (U : Set V) (hU : ConnSet F U)
    (hne : U.Nonempty) (n : ℕ)
    (hn : ∀ C : Finset V, (C : Set V) ⊆ U → C.card < n → ∃ x ∈ U, x ∉ C) :
    ∀ m, 1 ≤ m → m ≤ n → ∃ C : Finset V, (C : Set V) ⊆ U ∧ C.card = m ∧ ConnSet F C := by
  classical
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro _ hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · obtain ⟨x, hx⟩ := hne
      refine ⟨{x}, by simpa using hx, by simp, ?_⟩
      intro a ha b hb
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
      subst ha; subst hb
      exact Relation.ReflTransGen.refl
    · obtain ⟨C, hCU, hCc, hCconn⟩ := ih hm (by omega)
      obtain ⟨x, hxU, hxC⟩ := hn C hCU (by omega)
      have hCne : C.Nonempty := by
        rw [← Finset.card_pos]; omega
      obtain ⟨c0, hc0⟩ := hCne
      -- crossing edge
      have cross : ∀ y, Relation.ReflTransGen (fun x y => x ∈ U ∧ y ∈ U ∧ F.Adj x y) c0 y →
          y ∈ C ∨ ∃ c ∈ C, ∃ y' ∈ U, y' ∉ C ∧ F.Adj c y' := by
        intro y hy
        induction hy with
        | refl => exact Or.inl hc0
        | @tail b d _ hbd ih =>
          rcases ih with hb | ⟨c, hc, y', hy', hy'C, hadj⟩
          · by_cases hd : d ∈ C
            · exact Or.inl hd
            · exact Or.inr ⟨b, hb, d, hbd.2.1, hd, hbd.2.2⟩
          · exact Or.inr ⟨c, hc, y', hy', hy'C, hadj⟩
      rcases cross x (hU c0 (hCU hc0) x hxU) with h | ⟨c, hc, yy, hyU, hyC, hadj⟩
      · exact absurd h hxC
      · refine ⟨insert yy C, ?_, ?_, ?_⟩
        · intro z hz
          rw [Finset.coe_insert] at hz
          rcases hz with rfl | hz
          · exact hyU
          · exact hCU hz
        · rw [Finset.card_insert_of_notMem hyC, hCc]
        · -- connectivity
          have hmono : ∀ a b : V, a ∈ (C : Set V) → b ∈ (C : Set V) →
              Relation.ReflTransGen (fun x y => x ∈ (C : Set V) ∧ y ∈ (C : Set V) ∧ F.Adj x y) a b →
              Relation.ReflTransGen (fun x y => x ∈ ((insert yy C : Finset V) : Set V) ∧
                y ∈ ((insert yy C : Finset V) : Set V) ∧ F.Adj x y) a b := by
            intro a b _ _ h
            refine h.lift id ?_
            rintro p q ⟨hp, hq, hpq⟩
            exact ⟨by simp [Finset.mem_coe] at hp ⊢; exact Or.inr hp,
              by simp [Finset.mem_coe] at hq ⊢; exact Or.inr hq, hpq⟩
          have toC : ∀ a ∈ ((insert yy C : Finset V) : Set V),
              Relation.ReflTransGen (fun x y' => x ∈ ((insert yy C : Finset V) : Set V) ∧
                y' ∈ ((insert yy C : Finset V) : Set V) ∧ F.Adj x y') a c := by
            intro a ha
            have ha' : a = yy ∨ a ∈ C := by simpa using ha
            rcases ha' with rfl | ha'
            · exact Relation.ReflTransGen.single ⟨by simp, by simp [hc], hadj.symm⟩
            · exact hmono a c ha' hc (hCconn a ha' c hc)
          have fromC : ∀ b ∈ ((insert yy C : Finset V) : Set V),
              Relation.ReflTransGen (fun x y' => x ∈ ((insert yy C : Finset V) : Set V) ∧
                y' ∈ ((insert yy C : Finset V) : Set V) ∧ F.Adj x y') c b := by
            intro b hb
            have hb' : b = yy ∨ b ∈ C := by simpa using hb
            rcases hb' with rfl | hb'
            · exact Relation.ReflTransGen.single ⟨by simp [hc], by simp, hadj⟩
            · exact hmono c b hc hb' (hCconn c hc b hb')
          intro a ha b hb
          exact (toC a ha).trans (fromC b hb)

lemma richSet_minor {V W : Type*} {G : SimpleGraph W} {F : SimpleGraph V} (M : MinorModel G F)
    (k : ℕ) : ∀ j S, RichSet G k j S →
      ∃ S', RichSet F k j S' ∧ S' ⊆ ⋃ v ∈ S, M.branchSet v := by
  classical
  have hBn : ∀ w, (M.branchSet w).Nonempty := fun w => (connSet_of_connected (M.connected w)).1
  have hBc : ∀ w, ConnSet F (M.branchSet w) := fun w => (connSet_of_connected (M.connected w)).2
  intro j
  induction j with
  | zero =>
    intro S hS
    obtain ⟨hne, hc⟩ := connSet_of_connected hS.1
    have hUc : ConnSet F (⋃ v ∈ S, M.branchSet v) := connSet_biUnion M.branchSet hBc hBn
      (fun u v h => M.adjacent h) hc
    have hUne : (⋃ v ∈ S, M.branchSet v).Nonempty := by
      obtain ⟨v, hv⟩ := hne
      obtain ⟨x, hx⟩ := hBn v
      exact ⟨x, Set.mem_biUnion hv hx⟩
    have hSfin : S.Finite := Set.finite_of_ncard_pos (by have := hS.2; omega)
    have hn : ∀ C : Finset V, (C : Set V) ⊆ (⋃ v ∈ S, M.branchSet v) → C.card < k + 1 →
        ∃ x ∈ (⋃ v ∈ S, M.branchSet v), x ∉ C := by
      intro C hCU hCc
      by_contra hcon
      push_neg at hcon
      have hsub : (⋃ v ∈ S, M.branchSet v) ⊆ (C : Set V) := hcon
      -- ncard S ≤ ncard U ≤ card C
      choose g hg using hBn
      have hinj : Set.InjOn g S := by
        intro a _ b _ hab
        by_contra hne'
        have hd := M.disjoint hne'
        exact Set.disjoint_left.1 hd (hg a) (hab ▸ hg b)
      have h1 : (g '' S).ncard = S.ncard := Set.ncard_image_of_injOn hinj
      have h2 : g '' S ⊆ (C : Set V) := by
        rintro _ ⟨a, ha, rfl⟩
        exact hsub (Set.mem_biUnion ha (hg a))
      have h3 := Set.ncard_le_ncard h2 (Finset.finite_toSet C)
      rw [Set.ncard_coe_finset] at h3
      have := hS.2
      omega
    obtain ⟨C, hCU, hCc, hCconn⟩ := exists_finite_connSet F _ hUc hUne (k + 1) hn (k + 1) (by omega)
      le_rfl
    refine ⟨(C : Set V), ⟨connected_of_connSet ?_ hCconn, ?_⟩, hCU⟩
    · rw [Finset.coe_nonempty, ← Finset.card_pos]; omega
    · rw [Set.ncard_coe_finset]; omega
  | succ j ih =>
    intro S hS
    obtain ⟨hne, hc⟩ := connSet_of_connected hS.1
    obtain ⟨T, hT, hdisj⟩ := hS.2
    have hUc : ConnSet F (⋃ v ∈ S, M.branchSet v) := connSet_biUnion M.branchSet hBc hBn
      (fun u v h => M.adjacent h) hc
    have hUne : (⋃ v ∈ S, M.branchSet v).Nonempty := by
      obtain ⟨v, hv⟩ := hne
      obtain ⟨x, hx⟩ := hBn v
      exact ⟨x, Set.mem_biUnion hv hx⟩
    choose T' hT'1 hT'2 using fun i => ih (T i) (hT i).2
    refine ⟨⋃ v ∈ S, M.branchSet v, ⟨connected_of_connSet hUne hUc, T', fun i => ⟨?_, hT'1 i⟩, ?_⟩,
      subset_rfl⟩
    · refine (hT'2 i).trans ?_
      intro x hx
      obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.1 hx
      exact Set.mem_biUnion ((hT i).1 hv) hxv
    · intro i i' hii'
      refine Set.disjoint_left.2 fun x hx hx' => ?_
      obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.1 (hT'2 i hx)
      obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.1 (hT'2 i' hx')
      have hvw : v = w := by
        by_contra hne'
        exact Set.disjoint_left.1 (M.disjoint hne') hxv hxw
      subst hvw
      exact Set.disjoint_left.1 (hdisj hii') hv hw

/-! ### The bottom graph on one vertex -/

lemma not_richSet_bot {k : ℕ} (hk : 1 ≤ k) : ∀ j S, ¬ RichSet (⊥ : SimpleGraph (Fin 1)) k j S := by
  intro j
  cases j with
  | zero =>
    intro S hS
    have h1 : S.ncard ≤ (Set.univ : Set (Fin 1)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    have := hS.2
    omega
  | succ j =>
    intro S hS
    obtain ⟨T, hT, hdisj⟩ := hS.2
    obtain ⟨x, hx⟩ := RichSet.nonempty (hT ⟨0, by omega⟩).2
    obtain ⟨y, hy⟩ := RichSet.nonempty (hT ⟨1, by omega⟩).2
    have hxy : x = y := Subsingleton.elim _ _
    subst hxy
    have hne : (⟨0, by omega⟩ : Fin (k + 1)) ≠ ⟨1, by omega⟩ := by simp
    exact Set.disjoint_left.1 (hdisj hne) hx hy

/-! ### Rich graphs have no shallow decompositions -/

section Decomp

variable {P : Pattern} {Δ k0 k : ℕ} (D : DepthDecomposition P Δ k0)

lemma iter_root (n : ℕ) : D.parent^[n] D.root = D.root :=
  Function.iterate_fixed D.parent_root n

/-- Depth of a node. -/
noncomputable def dep (t : D.Node) : ℕ :=
  open Classical in
  Nat.find (⟨Δ, D.depth_le t⟩ : ∃ n, D.parent^[n] t = D.root)

lemma dep_spec (t : D.Node) : D.parent^[dep D t] t = D.root := by
  classical
  unfold dep
  convert Nat.find_spec (⟨Δ, D.depth_le t⟩ : ∃ n, D.parent^[n] t = D.root)

lemma dep_min (t : D.Node) (n : ℕ) (h : D.parent^[n] t = D.root) : dep D t ≤ n := by
  classical
  unfold dep
  convert Nat.find_min' (⟨Δ, D.depth_le t⟩ : ∃ n, D.parent^[n] t = D.root) h

lemma dep_le (t : D.Node) : dep D t ≤ Δ := dep_min D t Δ (D.depth_le t)

lemma dep_root : dep D D.root = 0 := by
  have := dep_min D D.root 0 rfl
  omega

lemma dep_parent (t : D.Node) (ht : t ≠ D.root) : dep D (D.parent t) + 1 = dep D t := by
  have h1 := dep_spec D t
  have hne : dep D t ≠ 0 := by
    intro h0
    rw [h0] at h1
    exact ht h1
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
  rw [hm, Function.iterate_succ_apply] at h1
  have h2 := dep_min D (D.parent t) m h1
  have h3 := dep_spec D (D.parent t)
  have h4 : dep D t ≤ dep D (D.parent t) + 1 := by
    apply dep_min
    rw [Function.iterate_succ_apply]
    exact h3
  omega

lemma dep_iter (x : D.Node) (hx : x ≠ D.root) :
    ∀ (i : ℕ) (s : D.Node), D.parent^[i] s = x → dep D s = dep D x + i := by
  intro i
  induction i with
  | zero => intro s hs; simpa using congrArg (dep D) hs
  | succ i ih =>
    intro s hs
    rw [Function.iterate_succ_apply] at hs
    have hs0 : s ≠ D.root := by
      rintro rfl
      rw [D.parent_root, iter_root] at hs
      exact hx hs.symm
    have := dep_parent D s hs0
    have := ih _ hs
    omega

/-- children of `t` -/
lemma child_dep {t c : D.Node} (hc : D.parent c = t) (hne : c ≠ t) :
    c ≠ D.root ∧ dep D c = dep D t + 1 := by
  have hr : c ≠ D.root := by
    rintro rfl
    exact hne (by rw [← hc, D.parent_root])
  refine ⟨hr, ?_⟩
  have := dep_parent D c hr
  rw [hc] at this
  omega

lemma child_unique {t c c' σ : D.Node} (hc : D.parent c = t) (hne : c ≠ t)
    (hc' : D.parent c' = t) (hne' : c' ≠ t) (h : ∃ a, D.parent^[a] σ = c)
    (h' : ∃ b, D.parent^[b] σ = c') : c = c' := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  obtain ⟨hr, hd⟩ := child_dep D hc hne
  obtain ⟨hr', hd'⟩ := child_dep D hc' hne'
  have e1 := dep_iter D c hr a σ ha
  have e2 := dep_iter D c' hr' b σ hb
  have : a = b := by omega
  subst this
  rw [← ha, ← hb]

lemma exists_top (v : P.A ⊕ P.B) : ∃ τ, v ∈ D.bag τ ∧ v ∉ D.bag (D.parent τ) ∧
    ∀ s, v ∈ D.bag s → ∃ i, D.parent^[i] s = τ := by
  classical
  have climb : ∀ s, v ∈ D.bag s →
      ∃ i, v ∈ D.bag (D.parent^[i] s) ∧ v ∉ D.bag (D.parent (D.parent^[i] s)) := by
    intro s hs
    have hex : ∃ n, v ∉ D.bag (D.parent^[n] s) := ⟨Δ, by rw [D.depth_le, D.bag_root]; simp⟩
    obtain ⟨n, hn, hmin⟩ : ∃ n, v ∉ D.bag (D.parent^[n] s) ∧
        ∀ m < n, v ∈ D.bag (D.parent^[m] s) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun m hm => not_not.mp (Nat.find_min hex hm)⟩
    cases n with
    | zero => exact absurd hs (by simpa using hn)
    | succ i =>
      refine ⟨i, hmin i (Nat.lt_succ_self i), ?_⟩
      rwa [← Function.iterate_succ_apply' D.parent]
  obtain ⟨s0, hs0⟩ := D.exists_mem_bag v
  obtain ⟨i0, hi0, hi0'⟩ := climb s0 hs0
  refine ⟨D.parent^[i0] s0, hi0, hi0', fun s hs => ?_⟩
  obtain ⟨i, hi, hi'⟩ := climb s hs
  exact ⟨i, D.connected v _ _ hi hi' hi0 hi0'⟩

/-- The top node of a vertex. -/
noncomputable def top (v : P.A ⊕ P.B) : D.Node := Classical.choose (exists_top D v)

lemma top_mem (v : P.A ⊕ P.B) : v ∈ D.bag (top D v) := (Classical.choose_spec (exists_top D v)).1

lemma top_anc (v : P.A ⊕ P.B) {s : D.Node} (hs : v ∈ D.bag s) :
    ∃ i, D.parent^[i] s = top D v := (Classical.choose_spec (exists_top D v)).2.2 s hs

lemma adj_bag {u v : P.A ⊕ P.B} (h : (underlying P).Adj u v) :
    ∃ s, u ∈ D.bag s ∧ v ∈ D.bag s := by
  rw [underlying, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨a, b, rfl, rfl, hab⟩ | ⟨a, b, rfl, rfl, hab⟩
  · exact D.exists_edge_mem_bag a b hab
  · obtain ⟨s, h1, h2⟩ := D.exists_edge_mem_bag a b hab
    exact ⟨s, h2, h1⟩

lemma step {S : Set (P.A ⊕ P.B)} (hS : S.Nonempty) (hc : ConnSet (underlying P) S) (t : D.Node)
    (h1 : ∀ v ∈ S, ∃ i, D.parent^[i] (top D v) = t) (h2 : ∀ v ∈ S, v ∉ D.bag t) :
    ∃ c, D.parent c = t ∧ c ≠ t ∧ ∀ v ∈ S, ∃ i, D.parent^[i] (top D v) = c := by
  classical
  have exch : ∀ v ∈ S, ∃ c, D.parent c = t ∧ c ≠ t ∧ ∃ i, D.parent^[i] (top D v) = c := by
    intro v hv
    have hex := h1 v hv
    obtain ⟨m, hm, hmin⟩ : ∃ m, D.parent^[m] (top D v) = t ∧
        ∀ m' < m, D.parent^[m'] (top D v) ≠ t :=
      ⟨Nat.find hex, Nat.find_spec hex, fun m' hm' => Nat.find_min hex hm'⟩
    cases m with
    | zero =>
      exfalso
      apply h2 v hv
      rw [← hm]
      exact top_mem D v
    | succ i =>
      refine ⟨D.parent^[i] (top D v), ?_, hmin i (Nat.lt_succ_self i), i, rfl⟩
      rw [← Function.iterate_succ_apply' D.parent]
      exact hm
  obtain ⟨v0, hv0⟩ := hS
  obtain ⟨c0, hc0, hne0, hi0⟩ := exch v0 hv0
  refine ⟨c0, hc0, hne0, ?_⟩
  have key : ∀ v, Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ (underlying P).Adj x y) v0 v →
      ∃ i, D.parent^[i] (top D v) = c0 := by
    intro v hv
    induction hv with
    | refl => exact hi0
    | @tail u w _ hstep ih =>
      obtain ⟨hu, hw, hadj⟩ := hstep
      obtain ⟨s0, hs1, hs2⟩ := adj_bag D hadj
      obtain ⟨i, hi⟩ := top_anc D u hs1
      obtain ⟨j, hj⟩ := top_anc D w hs2
      obtain ⟨c1, hc1, hne1, hi1⟩ := exch w hw
      obtain ⟨a, ha⟩ := ih
      rcases le_total i j with hij | hji
      · have e : D.parent^[j - i] (top D u) = top D w := by
          rw [← hi, ← Function.iterate_add_apply, ← hj]
          congr 1; omega
        obtain ⟨b, hb⟩ := hi1
        have hb' : D.parent^[b + (j - i)] (top D u) = c1 := by
          rw [Function.iterate_add_apply, e]; exact hb
        have : c0 = c1 := child_unique D hc0 hne0 hc1 hne1 ⟨a, ha⟩ ⟨_, hb'⟩
        subst this
        exact ⟨b, hb⟩
      · have e : D.parent^[i - j] (top D w) = top D u := by
          rw [← hj, ← Function.iterate_add_apply, ← hi]
          congr 1; omega
        refine ⟨a + (i - j), ?_⟩
        rw [Function.iterate_add_apply, e]; exact ha
  intro v hv
  exact key v (hc v0 hv0 v hv)

lemma main (hbag : ∀ t, (D.bag t).card ≤ k) :
    ∀ (j : ℕ) (S : Set (P.A ⊕ P.B)), RichSet (underlying P) k j S → ∀ t : D.Node,
      (∀ v ∈ S, ∃ i, D.parent^[i] (top D v) = t) → (∀ v ∈ S, v ∉ D.bag t) →
      Δ ≤ dep D t + j + 1 → False := by
  intro j
  induction j with
  | zero =>
    intro S hS t h1 h2 h3
    obtain ⟨hne, hc⟩ := connSet_of_connected hS.1
    obtain ⟨c, hc1, hc2, hc3⟩ := step D hne hc t h1 h2
    obtain ⟨hr, hd⟩ := child_dep D hc1 hc2
    have hsub : S ⊆ (D.bag c : Set _) := by
      intro v hv
      obtain ⟨i, hi⟩ := hc3 v hv
      have e := dep_iter D c hr i _ hi
      have := dep_le D (top D v)
      have hi0 : i = 0 := by omega
      subst hi0
      simp only [Function.iterate_zero, id] at hi
      rw [Finset.mem_coe, ← hi]
      exact top_mem D v
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at this
    have := hS.2
    have := hbag c
    omega
  | succ j ih =>
    intro S hS t h1 h2 h3
    obtain ⟨hne, hc⟩ := connSet_of_connected hS.1
    obtain ⟨T, hT, hdisj⟩ := hS.2
    obtain ⟨c, hc1, hc2, hc3⟩ := step D hne hc t h1 h2
    obtain ⟨hr, hd⟩ := child_dep D hc1 hc2
    have hex : ∃ i, ∀ v ∈ T i, v ∉ D.bag c := by
      by_contra hcon
      push_neg at hcon
      choose g hgT hgb using hcon
      have hinj : Set.InjOn g (Finset.univ : Finset (Fin (k + 1))) := by
        intro i _ i' _ heq
        by_contra hne'
        exact Set.disjoint_left.1 (hdisj hne') (hgT i) (heq ▸ hgT i')
      have := Finset.card_le_card_of_injOn g (s := Finset.univ) (t := D.bag c)
        (fun i _ => hgb i) hinj
      have := hbag c
      simp at *
      omega
    obtain ⟨i, hi⟩ := hex
    refine ih (T i) (hT i).2 c (fun v hv => hc3 v ((hT i).1 hv)) hi ?_
    omega

end Decomp

end RichBasic

/-- Richness is invariant under isomorphism. -/
theorem isRich_iso {V W : Type} {F : SimpleGraph V} {G : SimpleGraph W} (e : F ≃g G) {k Δ : ℕ} :
    IsRich F k Δ ↔ IsRich G k Δ :=
  ⟨fun ⟨S, hS⟩ => ⟨_, RichBasic.richSet_map e k _ S hS⟩,
   fun ⟨S, hS⟩ => ⟨_, RichBasic.richSet_map e.symm k _ S hS⟩⟩

/-- Richness passes from a minor to the graph (for `k ≥ 1`... any `k`). -/
theorem isRich_of_isMinor {V W : Type} {G : SimpleGraph W} {F : SimpleGraph V}
    (h : IsMinor G F) {k Δ : ℕ} (hG : IsRich G k Δ) : IsRich F k Δ := by
  obtain ⟨M⟩ := h
  obtain ⟨S, hS⟩ := hG
  obtain ⟨S', hS', _⟩ := RichBasic.richSet_minor M k _ S hS
  exact ⟨S', hS'⟩

/-- A pattern whose underlying graph is `(Δ,k)`-rich has `Δ`-forestwidth `≥ k`. -/
theorem not_forestwidthLE_of_isRich {P : Pattern} {k Δ : ℕ} (hk : 1 ≤ k) (hΔ : 1 ≤ Δ)
    (h : IsRich (underlying P) k Δ) : ¬ ForestwidthLE Δ (k - 1) P := by
  rintro ⟨D⟩
  obtain ⟨S, hS⟩ := h
  refine RichBasic.main D (k := k) (fun t => by have := D.card_bag_le t; omega) (Δ - 1) S hS
    D.root ?_ ?_ ?_
  · intro v _
    exact ⟨Δ, D.depth_le _⟩
  · intro v _
    rw [D.bag_root]
    simp
  · rw [RichBasic.dep_root]
    omega

theorem not_isRich_bot {k Δ : ℕ} (hk : 1 ≤ k) : ¬ IsRich (⊥ : SimpleGraph (Fin 1)) k Δ := by
  rintro ⟨S, hS⟩
  exact RichBasic.not_richSet_bot hk _ S hS

end Lax461425Proofs.DepthHierarchy
