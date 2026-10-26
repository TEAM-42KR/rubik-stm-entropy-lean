import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
import RubikSTM.Lemmas.LocalActions.Generic.UniformModel
import RubikSTM.Lemmas.LocalActions.Generic.RealizeTokensCorrect
import RubikSTM.Lemmas.Construction.Control.Physical.UniformSignedModel
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
open RubikLocal.Generic RubikConstruction.Control.Physical
theorem proof_RubikLocal_Generic_uniform_even_realization : ∃ C : ℕ, ∀ (n : ℕ) (a b : Fin n),
    RubikGeometry.Generic n a b → ∀ τ : Equiv.Perm (Fin 24), τ ∈ alternatingGroup (Fin 24) →
      ∃ ms : List (Move n), ms.length ≤ C ∧ LocalAction a b τ (chronological ms) := by
  classical
  obtain ⟨M, hM⟩ := uniform_model
  obtain ⟨L, hL⟩ := uniform_signed_model
  choose cw hcw using hL
  have hcw' : ∀ q, (cw q).length ≤ L ∧ RubikConstruction.Control.finiteEval (FreeGroup.mk (cw q)) = q :=
    fun q => ⟨(hcw q).1, (hcw q).2.1⟩
  refine ⟨M * (2 * L + 8), ?_⟩
  intro n a b hg τ hτ
  obtain ⟨ts, htlen, htval⟩ := hM τ hτ
  have h := realize_tokens_correct L cw hcw' a b hg ts
  refine ⟨realizeTokens a b cw ts, h.1.trans ?_, ?_⟩
  · exact Nat.mul_le_mul_right (2 * L + 8) htlen
  · simpa only [htval] using h.2
