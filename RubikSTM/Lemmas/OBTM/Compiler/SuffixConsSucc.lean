import RubikSTM.Proofs.OBTM.Compiler.SuffixConsSucc
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false

theorem RubikOBTMCompiler.suffix_cons_succ :
    ∀ {L s : ℕ} {K : Fin L → Type*} [∀ i, Monoid (K i)]
  (a : RubikOBTMCompiler.Profile L K) (w : Fin s → RubikOBTMCompiler.Profile L K) (b : ℕ) (i : Fin L), RubikOBTMCompiler.suffix (Fin.cons a w) (b+1) i = RubikOBTMCompiler.suffix w b i :=
  @proof_RubikOBTMCompiler_suffix_cons_succ
