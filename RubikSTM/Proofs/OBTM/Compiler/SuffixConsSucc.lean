import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_suffix_cons_succ {L s : ℕ} {K : Fin L → Type*} [∀ i, Monoid (K i)]
  (a : RubikOBTMCompiler.Profile L K) (w : Fin s → RubikOBTMCompiler.Profile L K) (b : ℕ) (i : Fin L) :
  RubikOBTMCompiler.suffix (Fin.cons a w) (b+1) i = RubikOBTMCompiler.suffix w b i := by
  simp [RubikOBTMCompiler.suffix,List.ofFn_succ]

#print axioms proof_RubikOBTMCompiler_suffix_cons_succ
