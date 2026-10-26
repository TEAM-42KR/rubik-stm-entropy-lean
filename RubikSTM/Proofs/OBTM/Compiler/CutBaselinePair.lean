import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.OBTM.Band.SlabActionIf
open RubikOBTMCompiler RubikOBTM.Band
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_cut_baseline_pair {n : ℕ} {A Y : Finset (Fin n)}
    (hAY : RubikPayload.Admissible A Y) (hY : Set.OrdConnected (Y : Set (Fin n)))
    {a b : Fin n} (ha : a ∈ A) (hb : b ∈ Y) (B : Finset (Fin n)) (hB : B ⊆ Y) :
    (∀ i, cutBaseline Y B (plus a b i) =
      plus a b ((halfPair ^ (B.filter (fun d => b ≤ d)).card).1 i)) ∧
    (∀ i, cutBaseline Y B (minus a b i) =
      minus a b ((halfPair ^ (B.filter (fun d => b ≤ d)).card).2 i)) := by
  classical
  have hy : Y.Nonempty := ⟨b,hb⟩
  let u := Y.min' hy
  let v := Y.max' hy
  have huY : u ∈ Y := Finset.min'_mem Y hy
  have hvY : v ∈ Y := Finset.max'_mem Y hy
  have hbounds (d : Fin n) (hd : d ∈ Y) : InInterval u v d :=
    ⟨Finset.min'_le Y d hd,Finset.le_max' Y d hd⟩
  have hband : Admissible n a u v := by
    refine ⟨(hAY.1 a ha).1,(hAY.1 a ha).2,(hAY.2.1 u huY).1,
      (hbounds v hvY).1,(hAY.2.1 v hvY).2,?_⟩
    have han : a ∉ Y := Finset.disjoint_left.mp hAY.2.2 ha
    by_contra h
    have haI : a ∈ Set.Icc u v := by
      have h1 := a.isLt
      change u.val ≤ a.val ∧ a.val ≤ v.val
      push_neg at h
      exact ⟨h.1,h.2⟩
    exact han (hY.out huY hvY haI)
  have hstepP (d : Fin n) (hd : d ∈ Y) (i : Fin 24) :
      (slabPerm u d ^ 2) (plus a b i) =
        plus a b ((halfPair.1 ^ (if b ≤ d then 1 else 0)) i) := by
    have hs := slab_action_if a u v hband d b (hbounds d hd) (hbounds b hb)
    by_cases hbd : b ≤ d
    · have hbd' : b.val ≤ d.val := hbd
      simpa only [pow_two,Equiv.Perm.mul_apply,hs,if_pos hbd,if_pos hbd',pow_one,halfPair,
        Prod.fst,pow_two] using congrArg (slabPerm u d) ((hs i).1)
    · have hbd' : ¬ b.val ≤ d.val := hbd
      simp only [pow_two,Equiv.Perm.mul_apply]
      rw [(hs i).1]
      simp only [if_neg hbd',Equiv.Perm.one_apply]
      rw [(hs i).1]
      simp [hbd,hbd']
  have hstepM (d : Fin n) (hd : d ∈ Y) (i : Fin 24) :
      (slabPerm u d ^ 2) (minus a b i) =
        minus a b ((halfPair.2 ^ (if b ≤ d then 1 else 0)) i) := by
    have hs := slab_action_if a u v hband d b (hbounds d hd) (hbounds b hb)
    by_cases hbd : b ≤ d
    · have hbd' : b.val ≤ d.val := hbd
      simpa only [pow_two,Equiv.Perm.mul_apply,hs,if_pos hbd,if_pos hbd',pow_one,halfPair,
        Prod.snd,pow_two] using congrArg (slabPerm u d) ((hs i).2)
    · have hbd' : ¬ b.val ≤ d.val := hbd
      simp only [pow_two,Equiv.Perm.mul_apply]
      rw [(hs i).2]
      simp only [if_neg hbd',Equiv.Perm.one_apply]
      rw [(hs i).2]
      simp [hbd,hbd']
  have hl (lab : Fin 24 → Rubik.Sticker n) (tau : Equiv.Perm (Fin 24))
      (hs : ∀ d ∈ Y, ∀ i, (slabPerm u d ^ 2) (lab i) =
        lab ((tau ^ (if b ≤ d then 1 else 0)) i))
      (cuts : List (Fin n)) (hc : ∀ d ∈ cuts, d ∈ Y) (i : Fin 24) :
      (cuts.map (fun d => slabPerm u d ^ 2)).reverse.prod (lab i) =
        lab ((tau ^ (cuts.filter (fun d => decide (b ≤ d))).length) i) := by
    induction cuts generalizing i with
    | nil => simp
    | cons d cuts ih =>
      simp only [List.map_cons,List.reverse_cons,List.prod_append,List.prod_singleton,
        Equiv.Perm.mul_apply]
      rw [hs d (hc d (by simp)) i,ih (by intro z hz; exact hc z (by simp [hz]))]
      by_cases hbd : b ≤ d
      · simp [hbd,pow_succ,Equiv.Perm.mul_apply]
      · simp [hbd]
  have hcnt : (B.toList.filter (fun d => decide (b ≤ d))).length =
      (B.filter (fun d => b ≤ d)).card := by
    simpa only [List.toFinset_filter,Finset.toList_toFinset,decide_eq_true_eq] using
      (List.toFinset_card_of_nodup (B.nodup_toList.filter (fun d => decide (b ≤ d)))).symm
  constructor
  · intro i
    simpa only [cutBaseline,dif_pos hy,u,Prod.pow_fst,hcnt] using
      hl (plus a b) halfPair.1 hstepP B.toList (by
        intro d hd; exact hB (Finset.mem_toList.mp hd)) i
  · intro i
    simpa only [cutBaseline,dif_pos hy,u,Prod.pow_snd,hcnt] using
      hl (minus a b) halfPair.2 hstepM B.toList (by
        intro d hd; exact hB (Finset.mem_toList.mp hd)) i
