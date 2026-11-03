import Lax461425.SectionSix
import Lax461425Proofs.Section6Characterisation
import Lax461425Proofs.SymmetricABPEquivariance
import Lax461425Proofs.SkewCircuitCharacterisation
import Lax461425Proofs.HomomorphismSpanning

/-!
Section 6 proof entrypoint. The implementation contains the explicit ABP-to-skew circuit,
the assignment-layer ABP for a path decomposition, and the weighted family construction.
All gate orbits quantify over every extending automorphism. The skew/pathwidth direction
is proved by refining Tim's construction. General homomorphism spanning is independently
proved in `HomomorphismSpanning`.
-/
