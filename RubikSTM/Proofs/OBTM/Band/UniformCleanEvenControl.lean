import RubikSTM.Definitions.OBTM.Band.CleanAction
import RubikSTM.Lemmas.OBTM.Band.Finite.FiniteSignedWordBound
import RubikSTM.Lemmas.OBTM.Band.UniformTokenWords
set_option autoImplicit false
open Rubik RubikOBTM RubikOBTM.Band

theorem proof_RubikOBTM_Band_uniform_clean_even_control : ∃ C : ℕ, 0 < C ∧
    ∀ (n : ℕ) (a u v : Fin n), Admissible n a u v →
      ∀ p q : Equiv.Perm (Fin 24), p ∈ alternatingGroup (Fin 24) → q ∈ alternatingGroup (Fin 24) →
      ∃ w : List (BlockMove n), w.length ≤ C ∧ CleanAction a u v (p,q) (wordPerm w) := by
  obtain ⟨M,hM,hwords⟩ := Finite.finite_signed_word_bound
  obtain ⟨D,hD⟩ := uniform_token_words
  refine ⟨D*M+1,by omega,?_⟩
  intro n a u v h p q hp hq
  obtain ⟨ts,hts,he⟩ := hwords p q hp hq
  obtain ⟨w,hw,hclean⟩ := hD n a u v h ts
  refine ⟨w,?_,?_⟩
  · exact le_trans hw (le_trans (Nat.mul_le_mul_left D hts) (Nat.le_succ _))
  · simpa only [he] using hclean
