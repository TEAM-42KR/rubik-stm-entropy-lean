import RubikSTM.Proofs.Geometry.ApplyWordAppend
import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

theorem Rubik.applyWord_append :
    ∀ {n : ℕ} (u v : List (Rubik.Move n)) (c : Rubik.Colouring n), Rubik.applyWord (u ++ v) c = Rubik.applyWord v (Rubik.applyWord u c) :=
  @proof_Rubik_applyWord_append
