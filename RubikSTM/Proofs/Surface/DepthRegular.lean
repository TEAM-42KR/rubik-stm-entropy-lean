import RubikSTM.Definitions.Surface.GenericRange
set_option autoImplicit false
open Rubik RubikGeometry RubikGlobal
open scoped Classical

theorem proof_RubikGlobal_depth_regular {n : ℕ} (i : RubikGlobal.I n) :
    RubikExceptional.Regular n (RubikGlobal.depth i) ∧
      RubikWing.Admissible n (RubikGlobal.depth i) := by
  have hi := i.isLt
  constructor <;> constructor <;> change _ ≤ _ <;> simp only [RubikGlobal.depth] <;> omega

#print axioms proof_RubikGlobal_depth_regular
