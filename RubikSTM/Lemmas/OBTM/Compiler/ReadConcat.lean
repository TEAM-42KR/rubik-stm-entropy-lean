import RubikSTM.Proofs.OBTM.Compiler.ReadConcat
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativePhaseModel
set_option autoImplicit false

theorem RubikOBTMCompiler.read_concat :
    ∀ {n : ℕ} {X : Type*} (read : Rubik.Colouring n → X)
  (ws : List (List (RubikOBTM.BlockMove n) × Equiv.Perm X))
  (h : ∀ t∈ws, ∀ c : Rubik.Colouring n, read (RubikOBTM.applyBlockWord t.1 c)=t.2 (read c)), ∀ c : Rubik.Colouring n,
  read (RubikOBTM.applyBlockWord ((ws.map Prod.fst).flatten) c) =
    ((ws.map Prod.snd).reverse.prod) (read c) :=
  @proof_RubikOBTMCompiler_read_concat
