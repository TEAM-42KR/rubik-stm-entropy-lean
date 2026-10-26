import RubikSTM.Proofs.WordConstruction.ConcatenateWords
import Mathlib
set_option autoImplicit false

theorem RubikCompiler.concatenateWords :
    ∀ {M X : Type*} (move : M → Equiv.Perm X)
  (ws : List (List M)) (b : ℕ) (hcost : ∀ w ∈ ws, w.length ≤ b), ((ws.flatten.map move).reverse.prod =
      (ws.map (fun w => (w.map move).reverse.prod)).reverse.prod) ∧
    ws.flatten.length = (ws.map List.length).sum ∧
    ws.flatten.length ≤ ws.length * b :=
  @proof_RubikCompiler_concatenateWords
