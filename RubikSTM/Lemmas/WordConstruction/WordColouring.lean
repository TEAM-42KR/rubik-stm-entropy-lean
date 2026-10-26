import RubikSTM.Proofs.WordConstruction.WordColouring
import Mathlib
set_option autoImplicit false

theorem RubikCompiler.wordColouring :
    ∀ {M X C : Type*} (move : M → Equiv.Perm X)
  (w : List M) (c : X → C), w.foldl (fun state m => fun x => state ((move m)⁻¹ x)) c =
    fun x => c (((w.map move).reverse.prod)⁻¹ x) :=
  @proof_RubikCompiler_wordColouring
