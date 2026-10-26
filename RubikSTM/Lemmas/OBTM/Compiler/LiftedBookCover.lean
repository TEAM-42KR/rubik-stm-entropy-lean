import RubikSTM.Proofs.OBTM.Compiler.LiftedBookCover
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.VectorAction
set_option autoImplicit false

theorem RubikOBTMCompiler.lifted_book_cover :
    ∀ {T k L : ℕ} {Z : Type*} (hT : 0 < T)
  (K : Fin T → Type*) [∀ p, Group (K p)] (C : ∀ p, Finset (K p))
  (act : ∀ p, K p →* Equiv.Perm Z) (B : RubikOBTM.Periodic.Book hT K C k L)
  (hB : RubikOBTM.Periodic.CoversAll hT K C act B), RubikOBTMCompiler.UniversalOwnProfile
    (fun i : Fin L => (RubikOBTMCompiler.vectorAction (k:=k) (act (RubikOBTM.Periodic.phase T hT i))))
    (RubikOBTMCompiler.liftedBook hT K C B) :=
  @proof_RubikOBTMCompiler_lifted_book_cover
