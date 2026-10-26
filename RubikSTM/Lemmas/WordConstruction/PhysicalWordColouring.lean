import RubikSTM.Proofs.WordConstruction.PhysicalWordColouring
import Mathlib
import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

theorem RubikCompiler.physicalWordColouring :
    ∀ (n : ℕ) (w : List (Rubik.Move n)) (c : Rubik.Colouring n), Rubik.applyWord w c = fun s => c (((w.map Rubik.movePermutation).reverse.prod)⁻¹ s) :=
  @proof_RubikCompiler_physicalWordColouring
