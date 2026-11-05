import Lax461425Proofs.Section6ABPToSkewRecoveryLabels
import Lax461425Proofs.SymmetricABPBasic

/-! Polynomial orbit bounds for the ABP-to-skew conversion, using all extensions. -/

namespace Lax461425Proofs.Section6ABPToSkew

open Lax461425 Lax461425.Circuits Lax461425.SymmetricABPs Lax461425.MatrixSymmetry
open scoped Classical

set_option maxHeartbeats 1000000

noncomputable section

variable {K : Type*} [CommSemiring K] {n : ℕ}
variable (G : ABP (Fin n × Fin n) K)

/-- Edge indices whose endpoints lie in two specified vertex orbits. -/
def candidates (S : Type*) (u v : G.Vertex) : Set (Edge G × S) :=
  {z | z.1.1.1 ∈ G.orbit u ∧ z.1.1.2 ∈ G.orbit v}

theorem candidates_card (S : Type*) [Fintype S] (u v : G.Vertex) :
    (candidates G S u v).ncard ≤
      (G.orbit u).ncard * (G.orbit v).ncard * Fintype.card S := by
  let f : Edge G × S → (G.Vertex × G.Vertex) × S := fun z => (z.1.1, z.2)
  have hh : (candidates G S u v).ncard ≤
      (((G.orbit u ×ˢ G.orbit v) ×ˢ (Set.univ : Set S))).ncard := by
    apply Set.ncard_le_ncard_of_injOn f
    · intro z hz; exact ⟨hz, Set.mem_univ _⟩
    · intro z hz w hw hzw
      apply Prod.ext
      · apply Subtype.ext; exact congrArg (fun p => p.1) hzw
      · exact congrArg (fun p => p.2) hzw
  simpa only [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card] using hh

theorem orbit_le_indexed (S : Type*) [Fintype S] (mk : Edge G → S → Gate G)
    (g : Gate G) (u v : G.Vertex)
    (him : ∀ (γ : Γ n) (τ : Gate G ≃ Gate G), Extends (circuit G) τ (actVar γ) →
      ∃ (f : Edge G) (y : S), τ g = mk f y ∧
        f.1.1 ∈ G.orbit u ∧ f.1.2 ∈ G.orbit v) :
    (MatrixSymmetry.orbit (circuit G) g).ncard ≤
      G.orbitSize ^ 2 * Fintype.card S := by
  have hs : MatrixSymmetry.orbit (circuit G) g ⊆
      (fun z : Edge G × S => mk z.1 z.2) '' candidates G S u v := by
    rintro w ⟨γ, τ, hτ, rfl⟩
    obtain ⟨f, y, he, hu, hv⟩ := him γ τ hτ
    exact ⟨(f, y), ⟨hu, hv⟩, he.symm⟩
  calc
    _ ≤ ((fun z : Edge G × S => mk z.1 z.2) '' candidates G S u v).ncard :=
      Set.ncard_le_ncard hs
    _ ≤ (candidates G S u v).ncard := Set.ncard_image_le
    _ ≤ (G.orbit u).ncard * (G.orbit v).ncard * Fintype.card S := candidates_card G S u v
    _ ≤ G.orbitSize ^ 2 * Fintype.card S := by
      apply Nat.mul_le_mul_right
      rw [pow_two]
      apply Nat.mul_le_mul
      · exact Finset.le_sup (f := fun w => (G.orbit w).ncard) (Finset.mem_univ u)
      · exact Finset.le_sup (f := fun w => (G.orbit w).ncard) (Finset.mem_univ v)

theorem recovered_vertex_mem (γ : Γ n) (τ : Gate G ≃ Gate G)
    (hτ : Extends (circuit G) τ (actVar γ)) (v : G.Vertex) :
    recoverVertices G τ (Equiv.prodCongr γ.1 γ.2) hτ v ∈ G.orbit v := by
  let π : Equiv.Perm (Fin n × Fin n) := Equiv.prodCongr γ.1 γ.2
  exact ⟨γ, recoverVertices G τ π hτ, recover_extends G τ π hτ, rfl⟩

theorem orbit_vertex_le (v : G.Vertex) :
    (MatrixSymmetry.orbit (circuit G) (.vertex v)).ncard ≤ G.orbitSize := by
  have hs : MatrixSymmetry.orbit (circuit G) (.vertex v) ⊆ Gate.vertex '' G.orbit v := by
    rintro w ⟨γ, τ, hτ, rfl⟩
    exact ⟨recoverVertices G τ (Equiv.prodCongr γ.1 γ.2) hτ v,
      recovered_vertex_mem G γ τ hτ v, (recoverVertex_spec G τ (Equiv.prodCongr γ.1 γ.2) hτ v).symm⟩
  have hcard : (Gate.vertex '' G.orbit v).ncard ≤ (G.orbit v).ncard := Set.ncard_image_le
  exact (Set.ncard_le_ncard hs).trans (hcard.trans
    (Finset.le_sup (f := fun w => (G.orbit w).ncard) (Finset.mem_univ v)))

theorem orbit_term_le (e : Edge G) (x : Option (Fin n × Fin n)) :
    (MatrixSymmetry.orbit (circuit G) (.term e x)).ncard ≤ G.orbitSize ^ 2 * (n ^ 2 + 1) := by
  apply (orbit_le_indexed G (Option (Fin n × Fin n)) Gate.term (.term e x) e.1.1 e.1.2 ?_).trans
  · simp [Fintype.card_option, Fintype.card_prod, pow_two]
  · intro γ τ hτ
    let π : Equiv.Perm (Fin n × Fin n) := Equiv.prodCongr γ.1 γ.2
    refine ⟨recoveredEdges G τ π hτ e, Option.map π x, term_image G τ π hτ e x, ?_, ?_⟩
    · exact recovered_vertex_mem G γ τ hτ e.1.1
    · exact recovered_vertex_mem G γ τ hτ e.1.2

theorem orbit_coeff_le (e : Edge G) (x : Option (Fin n × Fin n)) :
    (MatrixSymmetry.orbit (circuit G) (.coeff e x)).ncard ≤ G.orbitSize ^ 2 * (n ^ 2 + 1) := by
  apply (orbit_le_indexed G (Option (Fin n × Fin n)) Gate.coeff (.coeff e x) e.1.1 e.1.2 ?_).trans
  · simp [Fintype.card_option, Fintype.card_prod, pow_two]
  · intro γ τ hτ
    let π : Equiv.Perm (Fin n × Fin n) := Equiv.prodCongr γ.1 γ.2
    refine ⟨recoveredEdges G τ π hτ e, Option.map π x, ?_, ?_, ?_⟩
    · exact (coeff_image G τ π hτ (term_image G τ π hτ e x)).1
    · exact recovered_vertex_mem G γ τ hτ e.1.1
    · exact recovered_vertex_mem G γ τ hτ e.1.2

theorem inputVar_image (γ : Γ n) (τ : Gate G ≃ Gate G)
    (hτ : Extends (circuit G) τ (actVar γ)) (e : Edge G) (x : Fin n × Fin n) :
    τ (.inputVar e x) = .inputVar
      (recoveredEdges G τ (Equiv.prodCongr γ.1 γ.2) hτ e) (actVar γ x) := by
  let π : Equiv.Perm (Fin n × Fin n) := Equiv.prodCongr γ.1 γ.2
  obtain ⟨f, hf⟩ := inputVar_image_exists G τ π hτ e x
  have hw := preserves_wire G τ π hτ (.term e (some x)) (.inputVar e x)
  rw [term_image G τ π hτ, hf] at hw
  have he : recoveredEdges G τ π hτ e = f := by
    by_contra hn
    simp [wire, hn] at hw
  rw [hf, ← he]
  rfl

theorem orbit_inputVar_le (e : Edge G) (x : Fin n × Fin n) :
    (MatrixSymmetry.orbit (circuit G) (.inputVar e x)).ncard ≤
      G.orbitSize ^ 2 * (n ^ 2 + 1) := by
  apply (orbit_le_indexed G (Fin n × Fin n) Gate.inputVar (.inputVar e x) e.1.1 e.1.2 ?_).trans
  · simp only [Fintype.card_prod, Fintype.card_fin, pow_two]
    gcongr
    omega
  · intro γ τ hτ
    refine ⟨recoveredEdges G τ (Equiv.prodCongr γ.1 γ.2) hτ e,
      actVar γ x, inputVar_image G γ τ hτ e x, ?_, ?_⟩
    · exact recovered_vertex_mem G γ τ hτ e.1.1
    · exact recovered_vertex_mem G γ τ hτ e.1.2

theorem sourceOne_image (γ : Γ n) (τ : Gate G ≃ Gate G)
    (hτ : Extends (circuit G) τ (actVar γ)) : τ .sourceOne = .sourceOne := by
  let π : Equiv.Perm (Fin n × Fin n) := Equiv.prodCongr γ.1 γ.2
  have hl : label G (τ .sourceOne) = .const 1 := hτ.1 .sourceOne
  have hi : (label G (τ .sourceOne)).IsInput := by rw [hl]; trivial
  have hw := preserves_wire G τ π hτ (.vertex G.source) .sourceOne
  rw [recoverVertex_spec G τ π hτ] at hw
  have hp : 0 < wire G (.vertex (recoverVertex G τ π hτ G.source)) (τ .sourceOne) := by
    rw [hw]
    simp [wire]
  exact (input_child_vertex G hi hp).2

theorem orbit_sourceOne_le :
    (MatrixSymmetry.orbit (circuit G) .sourceOne).ncard ≤ 1 := by
  have hs : MatrixSymmetry.orbit (circuit G) .sourceOne ⊆ {Gate.sourceOne} := by
    rintro w ⟨γ, τ, hτ, rfl⟩
    exact sourceOne_image G γ τ hτ
  calc
    _ ≤ ({Gate.sourceOne} : Set (Gate G)).ncard := Set.ncard_le_ncard hs
    _ = 1 := Set.ncard_singleton _

/-- A polynomial bound on every gate orbit, including private input occurrences. -/
theorem circuit_orbitSize_le : MatrixSymmetry.orbitSize (circuit G) ≤
    G.orbitSize + G.orbitSize ^ 2 * (n ^ 2 + 1) + 1 := by
  apply Finset.sup_le
  intro g _
  cases g with
  | vertex v => exact (orbit_vertex_le G v).trans (by omega)
  | term e x => exact (orbit_term_le G e x).trans (by omega)
  | coeff e x => exact (orbit_coeff_le G e x).trans (by omega)
  | inputVar e x => exact (orbit_inputVar_le G e x).trans (by omega)
  | sourceOne => exact (orbit_sourceOne_le G).trans (by omega)

end
end Lax461425Proofs.Section6ABPToSkew
