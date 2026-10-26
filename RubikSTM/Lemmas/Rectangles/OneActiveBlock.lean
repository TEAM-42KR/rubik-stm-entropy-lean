import RubikSTM.Proofs.Rectangles.OneActiveBlock
import Mathlib
set_option autoImplicit false

theorem RubikRectangle.oneActiveBlock :
    ∀ {G : Type*} [Group G] {t : ℕ} (B F : G) (j : Fin t), (List.ofFn (fun q : Fin t => if q = j then F else B)).reverse.prod = B ^ (t - 1 - j.val) * F * B ^ j.val :=
  @proof_RubikRectangle_oneActiveBlock
