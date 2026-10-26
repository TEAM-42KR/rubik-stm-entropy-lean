import RubikSTM.Proofs.OBTM.Compiler.SlabCommute
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.slab_commute :
    ∀ {n : ℕ} (u v w : Fin n), Commute (RubikOBTM.Band.slabPerm u v) (RubikOBTM.Band.slabPerm u w) :=
  @proof_RubikOBTMCompiler_slab_commute
