import RubikSTM.Proofs.Core.LevelCodeInj
import RubikSTM.Definitions.Core.Project
set_option autoImplicit false

theorem RubikCore.levelCode_inj :
    ∀ {n : ℕ} {x y : Fin n} (hx : RubikCore.IsLevel x) (hy : RubikCore.IsLevel y) (h : RubikCore.levelCode x = RubikCore.levelCode y), x = y :=
  @proof_RubikCore_levelCode_inj
