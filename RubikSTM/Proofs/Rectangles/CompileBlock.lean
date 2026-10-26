import RubikSTM.Definitions.Rectangles.ColumnRealizes
import RubikSTM.Lemmas.Rectangles.PartitionColumns
import RubikSTM.Lemmas.Rectangles.LabelsOutsideBands
import RubikSTM.Lemmas.Rectangles.RectanglesInvariant
import RubikSTM.Lemmas.Payloads.RectanglesBands
import RubikSTM.Lemmas.Payloads.AdmissibleGeneric
import RubikSTM.Lemmas.Payloads.BaselinePhysical
import RubikSTM.Lemmas.Payloads.SingleIndexWordAction
import RubikSTM.Lemmas.Bands.SliceCommute
set_option autoImplicit false

open RubikRectangle RubikPayload
open scoped Classical

theorem proof_RubikRectangle_compileBlock (C : ℕ) (hP : PayloadInterface C) {n k : ℕ}
    (A Y : Finset (Fin n)) (hAY : Admissible A Y) (hAk : A.card ≤ k)
    (row : Fin n → Fin k) (D : Finset (Fin k → RubikChannel.Paired.Letter))
    (choice : Fin n → Fin k → RubikChannel.Paired.Letter)
    (hchoice : ∀ b ∈ Y, choice b ∈ D) :
    ∃ w : List (Rubik.Move n),
      w.length ≤ Y.card + C * (k + 1) * D.card ∧
        ColumnRealizes A Y (fun a b => (choice b (row a)).val) w := by
  classical
  let Yf (f : Fin k → RubikChannel.Paired.Letter) := Y.filter (fun b => choice b = f)
  have had (f : Fin k → RubikChannel.Paired.Letter) : Admissible A (Yf f) := by
    refine ⟨hAY.1, ?_, ?_⟩
    · intro b hb; exact hAY.2.1 b (Finset.mem_filter.mp hb).1
    · exact Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hAY.2.2
  have hchoose (f : Fin k → RubikChannel.Paired.Letter) :=
    hP A (Yf f) (had f) (fun a => (f (row a)).val) (fun a _ => (f (row a)).property)
  choose wf hlen hreal using hchoose
  let W := D.toList.flatMap wf
  have hsum : ∑ f ∈ D, (Yf f).card = Y.card := by
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using
      Finset.sum_fiberwise_of_maps_to hchoice (fun _ => (1 : ℕ))
  have hcost : W.length ≤ Y.card + C * (k + 1) * D.card := by
    calc
      W.length = ∑ f ∈ D, (wf f).length := by
        simp only [W, List.length_flatMap, Finset.sum_map_toList]
      _ ≤ ∑ f ∈ D, ((Yf f).card + C * (k + 1)) := by
        apply Finset.sum_le_sum
        intro f hf
        exact (hlen f).trans (Nat.add_le_add_left
          (Nat.mul_le_mul_left C (Nat.add_le_add_right hAk 1)) _)
      _ = Y.card + C * (k + 1) * D.card := by
        rw [Finset.sum_add_distrib, hsum]
        simp [Nat.mul_comm]
  have cat (u v : List (Rubik.Move n)) : RubikBand.wordPerm (u ++ v) =
      RubikBand.wordPerm v * RubikBand.wordPerm u := by
    simp [RubikBand.wordPerm, List.map_append, List.reverse_append, List.prod_append]
  have hsub (f : Fin k → RubikChannel.Paired.Letter) (s : Rubik.Sticker n) :
      Rectangles A (Yf f) s → Rectangles A Y s := by
    rintro ⟨a,ha,b,hb,hs⟩
    exact ⟨a,ha,b,(Finset.mem_filter.mp hb).1,hs⟩
  have hext (ls : List (Fin k → RubikChannel.Paired.Letter)) (s : Rubik.Sticker n)
      (hs : ¬ Rectangles A Y s) :
      RubikBand.wordPerm (ls.flatMap wf) s =
        RubikBand.wordPerm (ls.flatMap (fun f => baselineWord (Yf f))) s := by
    induction ls generalizing s with
    | nil => rfl
    | cons f ls ih =>
      simp only [List.flatMap_cons, cat, Equiv.Perm.mul_apply]
      rw [(hreal f).2 s (fun hh => hs (hsub f s hh))]
      exact ih _ ((not_congr (RubikRectangle.rectangles_invariant A Y (baselineWord (Yf f)) s)).mpr hs)
  have hwords : (D.toList.flatMap (fun f => baselineWord (Yf f))).Perm (baselineWord Y) := by
    have hp := (RubikRectangle.partition_columns D Y choice hchoice).map
      (fun b => (2,b.rev,0) : Fin n → Rubik.Move n)
    simp only [List.map_flatMap, Function.comp_def] at hp
    convert hp using 1 <;> congr 1
    funext f
    unfold baselineWord
    congr 1
    apply congrArg (fun S : Finset (Fin n) => S.sort (· ≤ ·))
    ext b
    simp only [Yf, Finset.mem_filter]
  have hc (ls : List (Fin n)) : (ls.map (Rubik.sliceQuarter n 2)).Pairwise Commute := by
    induction ls with
    | nil => exact List.Pairwise.nil
    | cons a ls ih =>
      simp only [List.map_cons, List.pairwise_cons]
      refine ⟨?_,ih⟩
      intro p hp
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
      exact RubikBand.sliceCommute 2 a b
  have href : ((baselineWord Y).map Rubik.movePermutation).reverse.Pairwise Commute := by
    simpa only [baselineWord, List.map_map, List.map_reverse, Function.comp_def,
      Rubik.movePermutation, Fin.val_zero, zero_add, pow_one] using
      hc (((Y.sort (· ≤ ·)).map Fin.rev).reverse)
  have hbase : RubikBand.wordPerm (D.toList.flatMap (fun f => baselineWord (Yf f))) = columnBaseline Y := by
    have hp := (List.reverse_perm ((baselineWord Y).map Rubik.movePermutation)).trans
      ((hwords.map Rubik.movePermutation).symm.trans (List.reverse_perm _).symm)
    exact (hp.prod_eq' href).symm
  refine ⟨W,hcost,?_,?_⟩
  · intro a ha b hbY hb
    have hg := RubikPayload.admissibleGeneric hAY ha hbY
    have hstep : ∀ f ∈ D.toList, ∀ i,
        RubikBand.wordPerm (wf f) (RubikGeometry.lab a b i) =
          RubikGeometry.lab a b (if f = choice b then (choice b (row a)).val.1 i else i) ∧
        RubikBand.wordPerm (wf f) (RubikOrbit.minusLab a b hb i) =
          RubikOrbit.minusLab a b hb (if f = choice b then (choice b (row a)).val.2 i else i) := by
      intro f hf i
      by_cases he : f = choice b
      · subst f
        have hbF : b ∈ Yf (choice b) := Finset.mem_filter.mpr ⟨hbY,rfl⟩
        simpa using (hreal (choice b)).1 a ha b hbF hb i
      · have haF : a ∉ Yf f := by
          intro ham
          exact Finset.disjoint_left.mp hAY.2.2 ha (Finset.mem_filter.mp ham).1
        have hbF : b ∉ Yf f := by simp [Yf, Ne.symm he]
        have hout := RubikRectangle.labels_outside_bands hg hb (Yf f)
          (had f).2.1 haF hbF i
        have hpnot : ¬ Rectangles A (Yf f) (RubikGeometry.lab a b i) :=
          fun h => hout.1 ((RubikPayload.rectanglesBands (had f) _).mp h).2
        have hmnot : ¬ Rectangles A (Yf f) (RubikOrbit.minusLab a b hb i) :=
          fun h => hout.2 ((RubikPayload.rectanglesBands (had f) _).mp h).2
        rw [(hreal f).2 _ hpnot, (hreal f).2 _ hmnot]
        simp only [he, if_false]
        exact ⟨(RubikPayload.baselinePhysical (Yf f)).2 _ hout.1,
          (RubikPayload.baselinePhysical (Yf f)).2 _ hout.2⟩
    have hp := RubikPayload.singleIndexWordAction D.toList D.nodup_toList (choice b) wf
      (RubikGeometry.lab a b) (choice b (row a)).val.1 (fun f hf i => (hstep f hf i).1)
    have hm := RubikPayload.singleIndexWordAction D.toList D.nodup_toList (choice b) wf
      (RubikOrbit.minusLab a b hb) (choice b (row a)).val.2 (fun f hf i => (hstep f hf i).2)
    exact ⟨by simpa only [Finset.mem_toList, hchoice b hbY, if_true] using hp,
      by simpa only [Finset.mem_toList, hchoice b hbY, if_true] using hm⟩
  · intro s hs
    exact (hext D.toList s hs).trans (congrArg (fun p : Equiv.Perm (Rubik.Sticker n) => p s) hbase)

#print axioms proof_RubikRectangle_compileBlock
