import RubikSTM.Proofs.Rectangles.ReachableView
import RubikSTM.Definitions.Rectangles.PayloadInterface
set_option autoImplicit false

theorem RubikRectangle.reachable_view :
    ∀ {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b) (hb : 0 < b.val ∧ b.val + 1 < n) (c : Rubik.Position n), ∃ x : RubikChannel.Paired.State, RubikRectangle.data x = RubikRectangle.view c.val a b hb :=
  @proof_RubikRectangle_reachable_view
