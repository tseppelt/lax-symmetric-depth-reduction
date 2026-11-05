import Lax461425.SymmetricABPs

/-! Layered ABPs, used to give the summands of Lemma 6.5 distinct path lengths. -/

namespace Lax461425Proofs.Section6Layering

open Lax461425.SymmetricABPs

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A consecutive-layer certificate, retained when combining the ABPs of Section 6.
Every source-to-sink path has length `layer G.sink`. -/
structure Layering {V K : Type*} (G : ABP V K) where
  layer : G.Vertex → ℕ
  source_layer : layer G.source = 0
  edge_layer : ∀ u v, G.edge u v → layer v = layer u + 1

end Lax461425Proofs.Section6Layering
