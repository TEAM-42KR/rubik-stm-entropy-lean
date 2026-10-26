import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.OBTM.Compiler.WordConcat
import RubikSTM.Lemmas.OBTM.Compiler.ReadConcat
import RubikSTM.Lemmas.Rectangles.OneActiveBlock
import RubikSTM.Lemmas.OBTM.Compiler.CommonFrameProgram
import RubikSTM.Lemmas.OBTM.Compiler.OutsideRestoration
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_native_framed_word {n L t : ℕ} {X J D : Type*}
  (read : Rubik.Colouring n → J → D → X) (owner : J → Fin t)
  (B : D → Equiv.Perm X) (hB : ∀ b, B b ^ 2 = 1)
  (F : Fin L → J → D → Equiv.Perm X)
  (ws : Fin L → Fin t → List (RubikOBTM.BlockMove n))
  (hcell : ∀ i j c a b, read (RubikOBTM.applyBlockWord (ws i j) c) a b =
    (if j = owner a then F i a b else B b) (read c a b))
  (Q : Equiv.Perm (Rubik.Sticker n)) (hQ : Q^2=1)
  (S : Set (Rubik.Sticker n)) (hInv : ∀ x∈S, Q x ∈ S)
  (houtside : ∀ i j x, x∈S → RubikOBTM.Band.wordPerm (ws i j) x=Q x)
  (c d : Rubik.Colouring n) (ht : t%2=1) (hL : L%2=0)
  (hraw : ∀ a b, (List.ofFn (fun i => F i a b)).reverse.prod
    ((B b ^ ((owner a).val%2)) (read c a b)) =
      (B b ^ ((owner a).val%2)) (read d a b))
  (cost : ℕ) (hcost : ∀ i j, (ws i j).length ≤ cost) :
  (RubikOBTMCompiler.nativeProgram ws).length ≤ L*t*cost ∧
    (∀ a b, read (RubikOBTM.applyBlockWord (RubikOBTMCompiler.nativeProgram ws) c) a b=read d a b) ∧
    ∀ x∈S, RubikOBTM.Band.wordPerm (RubikOBTMCompiler.nativeProgram ws) x=x := by
  classical
  have hflat (vs : List (List (RubikOBTM.BlockMove n))) := (RubikOBTMCompiler.word_concat vs).1
  have hlen (vs : List (List (RubikOBTM.BlockMove n))) := (RubikOBTMCompiler.word_concat vs).2
  have hclayer (i : Fin L) : (List.ofFn (ws i)).flatten.length ≤ t*cost := by
    rw [hlen]
    simp only [List.map_ofFn,List.sum_ofFn]
    calc
      (∑ j, (ws i j).length) ≤ ∑ _j : Fin t, cost := Finset.sum_le_sum (fun j hj => hcost i j)
      _ = t*cost := by simp
  have hc : (RubikOBTMCompiler.nativeProgram ws).length ≤ L*t*cost := by
    rw [RubikOBTMCompiler.nativeProgram,hlen]
    simp only [List.map_ofFn,List.sum_ofFn]
    calc
      (∑ i, (List.ofFn (ws i)).flatten.length) ≤ ∑ _i : Fin L, t*cost :=
        Finset.sum_le_sum (fun i hi => hclayer i)
      _ = L*t*cost := by simp [Nat.mul_assoc]
  refine ⟨hc,?_,?_⟩
  · intro a b
    let j := owner a
    let fs : List (Equiv.Perm X) := List.ofFn (fun i => F i a b)
    let gs : Fin L → Equiv.Perm X := fun i => B b ^ (t-(j.val+1))*F i a b*B b^j.val
    have hlayer (i : Fin L) (z : Rubik.Colouring n) :
        read (RubikOBTM.applyBlockWord (List.ofFn (ws i)).flatten z) a b = gs i (read z a b) := by
      have hs : ∀ u∈List.ofFn (fun q => (ws i q,if q=j then F i a b else B b)),
          ∀ c : Rubik.Colouring n, read (RubikOBTM.applyBlockWord u.1 c) a b=u.2 (read c a b) := by
        intro u hu c
        obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hu
        exact hcell i q c a b
      have hh := RubikOBTMCompiler.read_concat (fun c => read c a b)
        (List.ofFn (fun q => (ws i q,if q=j then F i a b else B b))) hs z
      have he : t-1-j.val=t-(j.val+1) := by omega
      simpa only [List.map_ofFn,Function.comp_def,Prod.fst,Prod.snd,
        RubikRectangle.oneActiveBlock,he,gs] using hh
    have hs : ∀ u∈List.ofFn (fun i => ((List.ofFn (ws i)).flatten,gs i)),
        ∀ c : Rubik.Colouring n, read (RubikOBTM.applyBlockWord u.1 c) a b=u.2 (read c a b) := by
      intro u hu c
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
      exact hlayer i c
    have hh := RubikOBTMCompiler.read_concat (fun c => read c a b)
      (List.ofFn (fun i => ((List.ofFn (ws i)).flatten,gs i))) hs c
    have hp := (RubikOBTMCompiler.common_frame_program (B b) (hB b) t (j.val+1)
      (by omega) (by have := j.isLt; omega) ht fs (read c a b) (read d a b)
      (by simpa only [fs,j,Nat.add_sub_cancel,Equiv.Perm.smul_def] using hraw a b)).2
    have he : fs.map (fun f => B b^(t-(j.val+1))*f*B b^(j.val+1-1))=List.ofFn gs := by
      simp only [fs,List.map_ofFn,Nat.add_sub_cancel]; rfl
    rw [he] at hp
    have hh' : read (RubikOBTM.applyBlockWord (RubikOBTMCompiler.nativeProgram ws) c) a b=
        (List.ofFn gs).reverse.prod (read c a b) := by
      simpa only [RubikOBTMCompiler.nativeProgram,List.map_ofFn,Function.comp_def,Prod.fst,Prod.snd] using hh
    exact hh'.trans hp
  · let layers := List.ofFn (fun i : Fin L => List.ofFn (fun j : Fin t => RubikOBTM.Band.wordPerm (ws i j)))
    have hc := RubikOBTMCompiler.outside_restoration Q hQ S hInv layers (by
      intro bs hbs p hp x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hbs
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
      exact houtside i j x hx) (by
      simp only [layers,List.map_ofFn,List.length_ofFn,List.sum_ofFn,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
      simp [Nat.mul_mod,hL])
    have he : RubikOBTM.Band.wordPerm (RubikOBTMCompiler.nativeProgram ws)=
        (layers.map (fun bs => bs.reverse.prod)).reverse.prod := by
      simp only [RubikOBTMCompiler.nativeProgram,hflat,List.map_ofFn,layers,Function.comp_def]
    intro x hx
    rw [he]
    exact hc x hx

#print axioms proof_RubikOBTMCompiler_native_framed_word
