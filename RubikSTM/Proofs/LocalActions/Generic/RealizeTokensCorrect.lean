import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
import RubikSTM.Lemmas.LocalActions.Generic.ConjugateBounded
import RubikSTM.Lemmas.LocalActions.Generic.ChronologicalAppend
import RubikSTM.Lemmas.LocalActions.Generic.LocalActionMul
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
open RubikLocal.Generic RubikConstruction.Control.Physical
theorem proof_RubikLocal_Generic_realize_tokens_correct (L : ℕ) (cw : Perm → ControlLetters)
    (hcw : ∀ q, (cw q).length ≤ L ∧ RubikConstruction.Control.finiteEval (FreeGroup.mk (cw q)) = q)
    {n : ℕ} (a b : Fin n) (hg : RubikGeometry.Generic n a b) (ts : List Token) :
    (realizeTokens a b cw ts).length ≤ ts.length * (2 * L + 8) ∧
      LocalAction a b (evalTokens ts) (chronological (realizeTokens a b cw ts)) := by
  induction ts with
  | nil =>
    constructor
    · simp [realizeTokens]
    · constructor <;> intros <;> rfl
  | cons t ts ih =>
    have ht := conjugate_bounded L cw hcw a b hg t
    constructor
    · simp only [realizeTokens, List.length_append, List.length_cons]
      calc
        _ ≤ ts.length * (2 * L + 8) + (2 * L + 8) := Nat.add_le_add ih.1 ht.1
        _ = _ := by ring
    · simpa only [realizeTokens, chronological_append, evalTokens, List.map_cons, List.prod_cons] using
        local_action_mul a b _ _ _ _ ht.2 ih.2
