import RubikSTM.Proofs.OBTM.Compiler.BackwardSelection
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false

theorem RubikOBTMCompiler.backward_selection :
    ∀ {L s : ℕ} {K : Fin L → Type*} [∀ i, CommGroup (K i)] {X : Type*}
  (act : (i : Fin L) → K i → Equiv.Perm X) (A : (i : Fin L) → Finset (K i))
  (hA : RubikOBTMCompiler.UniversalOwnProfile act A) (x y : Fin s → X), ∃ w : Fin s → RubikOBTMCompiler.Profile L K, (∀ d i, w d i ∈ A i) ∧
    ∀ b : Fin s, RubikOBTMCompiler.phasePerm act (fun i => RubikOBTMCompiler.suffix w b.val i) (x b) = y b :=
  @proof_RubikOBTMCompiler_backward_selection
