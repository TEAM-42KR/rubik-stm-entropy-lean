import RubikSTM.Proofs.Construction.Control.Physical.WordAction
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
set_option autoImplicit false

theorem RubikConstruction.Control.Physical.word_action :
    ∀ {n : ℕ} (a b : Fin n) (ha : 1 ≤ a.val) (hb : 1 ≤ b.val) (has : 2 * a.val + 2 ≤ n) (hbs : 2 * b.val + 2 ≤ n) (hab : a ≠ b) (w : RubikConstruction.Control.Word) (i : Fin 24), RubikConstruction.Control.physicalEval a w (RubikConstruction.Control.lab a b i) = RubikConstruction.Control.lab a b (RubikConstruction.Control.finiteEval w i) :=
  @proof_RubikConstruction_Control_Physical_word_action
