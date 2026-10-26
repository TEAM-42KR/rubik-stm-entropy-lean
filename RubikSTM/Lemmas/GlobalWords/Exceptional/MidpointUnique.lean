import RubikSTM.Proofs.GlobalWords.Exceptional.MidpointUnique
import Mathlib
set_option autoImplicit false

theorem RubikGlobalWord.Exceptional.midpoint_unique :
    ∀ {n : ℕ} (m k : Fin n) (hm : m.rev = m) (hk : k.rev = k), m = k :=
  @proof_RubikGlobalWord_Exceptional_midpoint_unique
