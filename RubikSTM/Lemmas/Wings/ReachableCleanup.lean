import RubikSTM.Proofs.Wings.ReachableCleanup
import RubikSTM.Definitions.Wings.IsMiddleSkeleton
set_option autoImplicit false

theorem RubikWing.reachable_cleanup :
    ∀ {n : ℕ} {c : Fin n} (hc : RubikWing.Admissible n c) (r : Rubik.Position n), ∃ w : List (Rubik.Move n), w.length ≤ RubikWing.uniformCost ∧ RubikBand.StrictControl c w ∧ (∀ i b, Rubik.applyWord w r.val (RubikWing.lab c i b) = Rubik.solved n (RubikWing.lab c i b)) ∧ (∀ s : Rubik.Sticker n, ¬ RubikBand.Band c s → RubikBand.wordPerm w s = s) :=
  @proof_RubikWing_reachable_cleanup
