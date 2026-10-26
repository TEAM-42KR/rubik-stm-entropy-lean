import RubikSTM.Proofs.Bands.WordBand
import RubikSTM.Definitions.Bands.Band
set_option autoImplicit false

theorem RubikBand.wordBand :
    ∀ {n : ℕ} (a : Fin n) (w : List (Rubik.Move n)) (s : Rubik.Sticker n), RubikBand.Band a (RubikBand.wordPerm w s) ↔ RubikBand.Band a s :=
  @proof_RubikBand_wordBand
