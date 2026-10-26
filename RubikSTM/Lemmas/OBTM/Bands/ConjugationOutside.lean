import RubikSTM.Proofs.OBTM.Bands.ConjugationOutside
import RubikSTM.Definitions.Bands.Band
set_option autoImplicit false

theorem RubikBand.conjugationOutside :
    ∀ {n : ℕ} (a : Fin n) (w : List (Rubik.Move n))
  (hw : RubikBand.StrictControl a w) (q : Rubik.Axis) (Y : Finset (Fin n))
  (s : Rubik.Sticker n) (hs : ¬ (RubikBand.Band a s ∧ RubikBand.Bands Y s)), (RubikBand.wordPerm w * RubikBand.parallelBaseline q Y * (RubikBand.wordPerm w)⁻¹) s =
    RubikBand.parallelBaseline q Y s :=
  @proof_RubikBand_conjugationOutside
