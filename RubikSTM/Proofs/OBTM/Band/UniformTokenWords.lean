import RubikSTM.Definitions.OBTM.Band.Finite.ModelEval
import RubikSTM.Lemmas.OBTM.Band.UniformKernelWords
import RubikSTM.Lemmas.OBTM.Band.NativeWordInverse
import RubikSTM.Lemmas.OBTM.Band.CleanActionOne
import RubikSTM.Lemmas.OBTM.Band.CleanActionMul
import RubikSTM.Lemmas.OBTM.Band.CleanActionInv
import RubikSTM.Lemmas.OBTM.Band.WordPermAppend
set_option autoImplicit false
open Rubik RubikOBTM RubikOBTM.Band
set_option maxHeartbeats 800000

theorem proof_RubikOBTM_Band_uniform_token_words : ∃ D : ℕ, ∀ (n : ℕ) (a u v : Fin n),
    Admissible n a u v → ∀ ts : List Finite.Token, ∃ w : List (BlockMove n),
      w.length ≤ D*ts.length ∧ CleanAction a u v (Finite.signedEval ts) (wordPerm w) := by
  obtain ⟨D,hD⟩ := uniform_kernel_words
  refine ⟨D,?_⟩
  intro n a u v h ts
  have single (t : Finite.Token) : ∃ w : List (BlockMove n), w.length ≤ D ∧
      CleanAction a u v (Finite.tokenValue t) (wordPerm w) := by
    obtain ⟨w,hlen,hclean⟩ := hD n a u v h t.1
    by_cases ht : t.2 = true
    · exact ⟨w,hlen,by simpa [Finite.tokenValue,ht] using hclean⟩
    · obtain ⟨wi,hilen,hieq⟩ := native_word_inverse w
      refine ⟨wi,by omega,?_⟩
      rw [hieq]
      simpa [Finite.tokenValue,ht] using clean_action_inv a u v (Finite.kernel t.1) (wordPerm w) hclean
  induction ts with
  | nil =>
    refine ⟨[],by simp,?_⟩
    exact clean_action_one a u v
  | cons t ts ih =>
    obtain ⟨wh,hhlen,hh⟩ := single t
    obtain ⟨wt,htlen,ht⟩ := ih
    refine ⟨wt++wh,?_,?_⟩
    · simp only [List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
      omega
    · rw [wordPerm_append]
      change CleanAction a u v (Finite.tokenValue t * Finite.signedEval ts) (wordPerm wh * wordPerm wt)
      exact clean_action_mul a u v _ _ _ _ hh ht
