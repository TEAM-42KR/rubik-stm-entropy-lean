import RubikSTM.Proofs.OBTM.Band.SlabWordCorrect
import RubikSTM.Definitions.OBTM.Band.SlabWord
set_option autoImplicit false

theorem RubikOBTM.Band.slab_word_correct :
    ∀ {n : ℕ} (a u v : Fin n) (h : RubikOBTM.Band.Admissible n a u v), (RubikOBTM.Band.slabWord a u v h).length = 2 ∧ RubikOBTM.Band.wordPerm (RubikOBTM.Band.slabWord a u v h) = RubikOBTM.Band.slabPerm u v :=
  @proof_RubikOBTM_Band_slab_word_correct
