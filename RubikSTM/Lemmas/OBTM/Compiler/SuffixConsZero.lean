import RubikSTM.Proofs.OBTM.Compiler.SuffixConsZero
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false

theorem RubikOBTMCompiler.suffix_cons_zero :
    ∀ {L s : ℕ} {K : Fin L → Type*} [∀ i, Monoid (K i)]
  (a : RubikOBTMCompiler.Profile L K) (w : Fin s → RubikOBTMCompiler.Profile L K) (i : Fin L), RubikOBTMCompiler.suffix (Fin.cons a w) 0 i = a i * RubikOBTMCompiler.suffix w 0 i :=
  @proof_RubikOBTMCompiler_suffix_cons_zero
