import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeCoalescedWord
import RubikSTM.Lemmas.OBTM.Compiler.BlockQuarterCommute
import RubikSTM.Lemmas.OBTM.Compiler.BlockQuarterFour
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_half_prefix_word_two {n : ℕ} (a : Rubik.Axis) (side : Bool) (B : List (Fin (n-1))) :
  RubikOBTM.Band.wordPerm (B.map (RubikOBTMCompiler.halfPrefix a side)) ^ 2 = 1 := by
  let P := fun b : Fin (n-1) => RubikOBTM.blockQuarter n a side b ^ 2
  have he (b : Fin (n-1)) : P b ^ 2=1 := by
    simpa only [P,← pow_mul] using RubikOBTMCompiler.block_quarter_four a side b
  have hc (b c : Fin (n-1)) : Commute (P b) (P c) :=
    ((RubikOBTMCompiler.block_quarter_commute a side side b c).pow_left 2).pow_right 2
  have H : ∀ bs : List (Fin (n-1)), ((bs.map P).reverse.prod)^2=1 := by
    intro bs
    induction bs with
    | nil => simp
    | cons b bs ih =>
      have hh : Commute (P b) ((bs.map P).reverse.prod) := by
        apply Commute.list_prod_right
        intro g hg
        obtain ⟨c,hc',rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hg)
        exact hc b c
      simp only [List.map_cons,List.reverse_cons,List.prod_append,List.prod_singleton]
      rw [hh.symm.mul_pow,ih,he,one_mul]
  simpa [RubikOBTM.Band.wordPerm,RubikOBTMCompiler.halfPrefix,RubikOBTM.blockPermutation,
    List.map_map,Function.comp_def,P] using H B

#print axioms proof_RubikOBTMCompiler_half_prefix_word_two
