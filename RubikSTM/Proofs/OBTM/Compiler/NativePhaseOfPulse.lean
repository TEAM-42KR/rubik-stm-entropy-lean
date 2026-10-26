import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.OBTM.Compiler.WordConcat
import RubikSTM.Lemmas.OBTM.Band.WordPermAppend
import RubikSTM.Lemmas.OBTM.Compiler.CoalesceFinset
import RubikSTM.Lemmas.OBTM.Compiler.CutBaselineGrouped
import RubikSTM.Lemmas.OBTM.Compiler.CutBaselineBand
import RubikSTM.Lemmas.Payloads.RectanglesBands
set_option autoImplicit false
open RubikOBTMCompiler

theorem proof_RubikOBTMCompiler_native_phase_of_pulse (C : ℕ) (hP : NativePulseInterface C) {n k : ℕ}
    (A Y : Finset (Fin n)) (hAY : RubikPayload.Admissible A Y)
    (hY : Set.OrdConnected (Y : Set (Fin n))) (p : RubikOBTM.Finite.Phase)
    (row : Fin n → Fin k) (D : Finset (Fin k → RubikOBTM.Finite.Intrinsic))
    (hD : ∀ g ∈ D, ∀ z, g z ∈ RubikOBTM.Finite.nativeC)
    (choice : Fin n → Fin k → RubikOBTM.Finite.Intrinsic)
    (hchoice : ∀ d ∈ Y, choice d ∈ D) :
    ∃ w : List (RubikOBTM.BlockMove n),
      w.length ≤ Y.card + C*(A.card+1)*D.card ∧
      (∀ a ∈ A, ∀ b ∈ Y, NativeActsPair a b w
        (RubikOBTM.Finite.inclusion (RubikOBTM.Finite.phaseHom p
          ((∏ d ∈ Y.filter (fun d => b ≤ d), choice d) (row a))))) ∧
      ∀ s : Rubik.Sticker n, ¬ RubikPayload.Rectangles A Y s →
        RubikOBTM.Band.wordPerm w s = fullBaseline Y s := by
  classical
  let cuts (g : Fin k → RubikOBTM.Finite.Intrinsic) := Y.filter (fun d => choice d=g)
  have H (g : Fin k → RubikOBTM.Finite.Intrinsic) (hg : g ∈ D) :=
    hP A Y hAY hY p (fun a => g (row a)) (fun a ha => hD g hg (row a))
      (cuts g) (Finset.filter_subset _ _)
  let V (g : Fin k → RubikOBTM.Finite.Intrinsic) : List (RubikOBTM.BlockMove n) :=
    if hg : g ∈ D then Classical.choose (H g hg) else []
  have hV (g : Fin k → RubikOBTM.Finite.Intrinsic) (hg : g ∈ D) :
      (V g).length ≤ (cuts g).card+C*(A.card+1) ∧
      (∀ a ∈ A, ∀ b ∈ Y, NativeActsPair a b (V g)
        (RubikOBTM.Finite.inclusion (RubikOBTM.Finite.phaseHom p (g (row a))) ^
          ((cuts g).filter (fun d => b ≤ d)).card)) ∧
      (∀ s, ¬ RubikPayload.Rectangles A Y s →
        RubikOBTM.Band.wordPerm (V g) s = cutBaseline Y (cuts g) s) := by
    simpa only [V,dif_pos hg] using Classical.choose_spec (H g hg)
  let W := (D.toList.map V).flatten
  have hlen : W.length = ∑ g ∈ D, (V g).length := by
    rw [(word_concat (D.toList.map V)).2]
    simpa only [List.map_map,Function.comp_def,Finset.toList_toFinset] using
      (List.sum_toFinset (fun g => (V g).length) D.nodup_toList).symm
  have hcnt : (∑ g ∈ D, (cuts g).card) = Y.card := by
    simpa only [cuts,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,mul_one] using
      (Finset.sum_fiberwise_of_maps_to (s:=Y) (t:=D) (g:=choice) hchoice (fun _ => (1:ℕ)))
  refine ⟨W,?_,?_,?_⟩
  · rw [hlen]
    calc
      (∑ g ∈ D, (V g).length) ≤ ∑ g ∈ D, ((cuts g).card+C*(A.card+1)) :=
        Finset.sum_le_sum (fun g hg => (hV g hg).1)
      _ = Y.card+C*(A.card+1)*D.card := by
        rw [Finset.sum_add_distrib,hcnt]
        simp [Nat.mul_comm]
  · intro a ha b hb
    let f : (Fin k → RubikOBTM.Finite.Intrinsic) →* RubikPayload.Pair :=
      { toFun := fun g => RubikOBTM.Finite.inclusion (RubikOBTM.Finite.phaseHom p (g (row a)))
        map_one' := by simp
        map_mul' := by intro g h; simp }
    let e (g : Fin k → RubikOBTM.Finite.Intrinsic) := ((cuts g).filter (fun d => b ≤ d)).card
    have heq : ((D.toList.map (fun g => g ^ e g)).reverse.prod) =
        ∏ d ∈ Y.filter (fun d => b ≤ d), choice d := by
      rw [List.prod_reverse]
      rw [← List.prod_toFinset _ D.nodup_toList,Finset.toList_toFinset]
      exact coalesce_finset Y choice D hchoice (fun d => b ≤ d)
    have hl (gs : List (Fin k → RubikOBTM.Finite.Intrinsic))
        (hgs : ∀ g ∈ gs, g ∈ D) :
        NativeActsPair a b ((gs.map V).flatten)
          (f ((gs.map (fun g => g ^ e g)).reverse.prod)) := by
      induction gs with
      | nil => simp [NativeActsPair,RubikOBTM.Band.wordPerm]
      | cons g gs ih =>
        have ht := ih (by intro z hz; exact hgs z (by simp [hz]))
        have hg := (hV g (hgs g (by simp))).2.1 a ha b hb
        have hp : NativeActsPair a b (V g) (f (g ^ e g)) := by
          rw [map_pow]
          exact hg
        simp only [List.map_cons,List.flatten_cons,List.reverse_cons,List.prod_append,
          List.prod_singleton,map_mul]
        constructor
        · intro i
          rw [RubikOBTM.Band.wordPerm_append,Equiv.Perm.mul_apply,hp.1]
          exact ht.1 ((f (g^e g)).1 i)
        · intro i
          rw [RubikOBTM.Band.wordPerm_append,Equiv.Perm.mul_apply,hp.2]
          exact ht.2 ((f (g^e g)).2 i)
    have hh := hl D.toList (by intro g hg; exact Finset.mem_toList.mp hg)
    rw [heq] at hh
    exact hh
  · intro s hs
    have hc (z : Fin k → RubikOBTM.Finite.Intrinsic) (hz : z ∈ D) (x : Rubik.Sticker n)
        (hx : ¬ RubikPayload.Rectangles A Y x) :
        RubikOBTM.Band.wordPerm (V z) x = cutBaseline Y (cuts z) x := (hV z hz).2.2 x hx
    have hInv (g : Fin k → RubikOBTM.Finite.Intrinsic) (x : Rubik.Sticker n)
        (hx : ¬ RubikPayload.Rectangles A Y x) :
        ¬ RubikPayload.Rectangles A Y (cutBaseline Y (cuts g) x) := by
      intro hr
      have hg := RubikOBTMCompiler.cut_baseline_band Y (cuts g)
      have hr' := (RubikPayload.rectanglesBands hAY _).mp hr
      apply hx
      apply (RubikPayload.rectanglesBands hAY _).mpr
      constructor
      · rcases hr'.1 with ⟨a,ha,hb⟩
        exact ⟨a,ha,(hg a x).mp hb⟩
      · rcases hr'.2 with ⟨b,hb,hc⟩
        exact ⟨b,hb,(hg b x).mp hc⟩
    have hl (gs : List (Fin k → RubikOBTM.Finite.Intrinsic))
        (hgs : ∀ g ∈ gs, g ∈ D) (x : Rubik.Sticker n)
        (hx : ¬ RubikPayload.Rectangles A Y x) :
        RubikOBTM.Band.wordPerm ((gs.map V).flatten) x =
          ((gs.map (fun g => cutBaseline Y (cuts g))).reverse.prod) x := by
      induction gs generalizing x with
      | nil => simp [RubikOBTM.Band.wordPerm]
      | cons g gs ih =>
        simp only [List.map_cons,List.flatten_cons,List.reverse_cons,List.prod_append,List.prod_singleton,
          RubikOBTM.Band.wordPerm_append,Equiv.Perm.mul_apply]
        rw [hc g (hgs g (by simp)) x hx]
        exact ih (by intro z hz; exact hgs z (by simp [hz])) _ (hInv g x hx)
    have hh := hl D.toList (by intro g hg; exact Finset.mem_toList.mp hg) s hs
    rw [RubikOBTMCompiler.cut_baseline_grouped Y choice D hchoice] at hh
    exact hh
