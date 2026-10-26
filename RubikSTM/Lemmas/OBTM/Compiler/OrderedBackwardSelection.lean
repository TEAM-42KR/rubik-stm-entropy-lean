import RubikSTM.Proofs.OBTM.Compiler.OrderedBackwardSelection
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false

theorem RubikOBTMCompiler.ordered_backward_selection :
    ∀ {I : Type*} [LinearOrder I] {L : ℕ}
  {K : Fin L → Type*} [∀ i, CommGroup (K i)] {X : Type*}
  (Y : Finset I) (act : (i : Fin L) → K i → Equiv.Perm X)
  (A : (i : Fin L) → Finset (K i)) (hA : RubikOBTMCompiler.UniversalOwnProfile act A)
  (x y : Y → X), ∃ w : I → RubikOBTMCompiler.Profile L K, (∀ b∈Y, ∀ i, w b i∈A i) ∧
    ∀ b : Y, RubikOBTMCompiler.phasePerm act (fun i => ∏ d∈Y.filter (fun d => b.val ≤ d), w d i)
      (x b) = y b :=
  @proof_RubikOBTMCompiler_ordered_backward_selection
