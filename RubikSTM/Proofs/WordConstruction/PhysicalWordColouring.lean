import Mathlib
import RubikSTM.Definitions.Geometry.StmGraph
import RubikSTM.Lemmas.WordConstruction.WordColouring
set_option autoImplicit false

theorem proof_RubikCompiler_physicalWordColouring (n : ℕ) (w : List (Rubik.Move n)) (c : Rubik.Colouring n) :
  Rubik.applyWord w c = fun s => c (((w.map Rubik.movePermutation).reverse.prod)⁻¹ s) := by
  exact RubikCompiler.wordColouring Rubik.movePermutation w c

#print axioms proof_RubikCompiler_physicalWordColouring
