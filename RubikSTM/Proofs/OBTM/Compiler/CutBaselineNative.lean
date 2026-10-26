import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.OBTM.Band.SlabPrefixDifference
import RubikSTM.Lemmas.OBTM.Compiler.NativeCoalescedLength
import RubikSTM.Lemmas.OBTM.Compiler.NativeCoalescedAction
import RubikSTM.Lemmas.OBTM.Compiler.SlabBaselineTwo
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_cut_baseline_native {n : ℕ} (Y B : Finset (Fin n))
  (hB : B ⊆ Y) (hY : ∀ d∈Y, 1 ≤ d.val ∧ d.val < n-1) :
  ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ B.card+1 ∧
    RubikOBTM.Band.wordPerm w = RubikOBTMCompiler.cutBaseline Y B ∧
    RubikOBTMCompiler.cutBaseline Y B ^ 2 = 1 := by
  classical
  by_cases hy : Y.Nonempty
  · let u := Y.min' hy
    have hu := hY u (Finset.min'_mem Y hy)
    let lower : Fin (n-1) := ⟨u.val-1,by omega⟩
    let upper (b : Fin n) : Fin (n-1) := if hb : b.val<n-1 then ⟨b.val,hb⟩ else lower
    let Bs := B.toList.map upper
    let W := RubikOBTMCompiler.nativeCoalescedWord 2 true lower Bs
    have he : RubikOBTMCompiler.slabBaseline 2 true lower Bs = RubikOBTMCompiler.cutBaseline Y B := by
      unfold RubikOBTMCompiler.slabBaseline RubikOBTMCompiler.cutBaseline
      rw [dif_pos hy]
      simp only [Bs,List.map_map,Function.comp_def]
      apply congrArg (fun l : List (Equiv.Perm (Rubik.Sticker n)) => l.reverse.prod)
      apply List.map_congr_left
      intro b hb
      have hbY := hB (Finset.mem_toList.mp hb)
      have hbc := hY b hbY
      have hub : u.val ≤ b.val := Finset.min'_le Y b hbY
      have hs : RubikOBTM.Band.slabPerm u b = RubikOBTM.blockQuarter n 2 true (upper b) *
          (RubikOBTM.blockQuarter n 2 true lower)⁻¹ := by
        simpa only [upper,dif_pos hbc.2,lower] using
          RubikOBTM.Band.slab_prefix_difference u b hu.1 hub hbc.2
      exact (congrArg (fun p : Equiv.Perm (Rubik.Sticker n) => p^2) hs).symm
    refine ⟨W,?_,?_,?_⟩
    · simpa only [W,Bs,List.length_map,Finset.length_toList] using
        (RubikOBTMCompiler.native_coalesced_length 2 true lower Bs).2
    · exact (RubikOBTMCompiler.native_coalesced_action 2 true lower Bs).trans he
    · rw [← he]
      exact RubikOBTMCompiler.slab_baseline_two 2 true lower Bs
  · have hb : B=∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨b,hb⟩
      exact hy ⟨b,hB hb⟩
    subst B
    exact ⟨[],by simp,by simp [RubikOBTM.Band.wordPerm,RubikOBTMCompiler.cutBaseline,hy],
      by simp [RubikOBTMCompiler.cutBaseline,hy]⟩

#print axioms proof_RubikOBTMCompiler_cut_baseline_native
