import RubikSTM.Definitions.OBTM.Band.Finite.ModelEval
import RubikSTM.Lemmas.OBTM.Band.UniformRowWords
import RubikSTM.Lemmas.OBTM.Band.StmWordBlocks
import RubikSTM.Lemmas.OBTM.Band.NativeWordInverse
import RubikSTM.Lemmas.OBTM.Band.SlabWordCorrect
import RubikSTM.Lemmas.OBTM.Band.WordPermAppend
import RubikSTM.Lemmas.OBTM.Band.RowQuotientClean
set_option autoImplicit false
open Rubik RubikOBTM RubikOBTM.Band
set_option maxHeartbeats 1200000

theorem proof_RubikOBTM_Band_uniform_kernel_words : ∃ D : ℕ, ∀ (n : ℕ) (a u v : Fin n),
    Admissible n a u v → ∀ t : Finite.Alphabet, ∃ w : List (BlockMove n),
      w.length ≤ D ∧ CleanAction a u v (Finite.kernel t) (wordPerm w) := by
  obtain ⟨L,hL⟩ := uniform_row_words
  refine ⟨8*L+4,?_⟩
  intro n a u v h t
  have hn : 2 ≤ n := by have := h.row_small; omega
  have synth (ρ : Perm) : ∃ (ms : List (Move n)) (W : List (BlockMove n)),
      W.length ≤ 4*L+2 ∧ RubikBand.StrictControl a ms ∧
      (∀ d : Fin n, InInterval u v d → ∀ i : Fin 24,
        (RubikBand.wordPerm ms (plus a d i) = plus a d (ρ i)) ∧
        (RubikBand.wordPerm ms (minus a d i) = minus a d (ρ i))) ∧
      wordPerm W = RubikBand.wordPerm ms * slabPerm u v * (RubikBand.wordPerm ms)⁻¹ := by
    obtain ⟨ms,hlen,hstrict,hacts⟩ := hL n a h.row_pos h.row_small ρ
    obtain ⟨U,hUlen,hUeq⟩ := stm_word_blocks hn ms
    obtain ⟨Ui,hilen,hieq⟩ := native_word_inverse U
    let W := (Ui ++ slabWord a u v h) ++ U
    have hslen := (slab_word_correct a u v h).1
    have hseq := (slab_word_correct a u v h).2
    refine ⟨ms,W,?_,hstrict,?_,?_⟩
    · dsimp [W]
      simp only [List.length_append]
      omega
    · intro d hd i
      have hdpos : 1 ≤ d.val := le_trans h.lower_pos hd.1
      have hdsmall : 2*d.val+2 ≤ n := by
        have := h.upper_small
        have := hd.2
        omega
      have had : a ≠ d := by
        intro he
        have he' := congrArg Fin.val he
        have ho := h.row_outside
        rcases hd with ⟨hl,hr⟩
        rcases ho with ho|ho <;> omega
      exact hacts d hdpos hdsmall had i
    · simp [W,wordPerm_append,hieq,hUeq,hseq,mul_assoc]
  obtain ⟨ms,U,hUlen,hm,hσ,hUeq⟩ := synth t.1
  obtain ⟨ns,V,hVlen,hn',hτ,hVeq⟩ := synth t.2
  obtain ⟨Vi,hilen,hieq⟩ := native_word_inverse V
  refine ⟨Vi++U,?_,?_⟩
  · simp only [List.length_append]
    omega
  · rw [wordPerm_append,hUeq,hieq,hVeq]
    exact row_quotient_clean a u v h t.1 t.2 ms ns hm hn' hσ hτ
