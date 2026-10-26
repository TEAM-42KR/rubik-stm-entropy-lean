import RubikSTM.Definitions.Rectangles.Layout
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Lemmas.Rectangles.LayoutExists
import RubikSTM.Lemmas.Rectangles.LayoutRowsCard
import RubikSTM.Lemmas.Rectangles.ReachableView
import RubikSTM.Lemmas.Rectangles.DataWord
import RubikSTM.Lemmas.Rectangles.DataAct
import RubikSTM.Lemmas.Rectangles.CompileBlock
import RubikSTM.Lemmas.Rectangles.FramedWord
import RubikSTM.Lemmas.Rectangles.LabelsOutsideBands
import RubikSTM.Lemmas.Payloads.BaselinePhysical
import RubikSTM.Lemmas.Payloads.BaselineAction
import RubikSTM.Lemmas.Payloads.RectanglesBands
import RubikSTM.Lemmas.Payloads.AdmissibleGeneric
import RubikSTM.Lemmas.WordConstruction.PhysicalWordColouring
set_option autoImplicit false

open RubikRectangle RubikPayload
open scoped Classical

theorem proof_RubikRectangle_compile_rectangle (C : ℕ) (hP : PayloadInterface C) {n : ℕ}
    (X Y : Finset (Fin n)) (hXY : Admissible X Y) (k L M : ℕ) (hk : 0 < k)
    (hL : 4 ∣ L) (Book : RubikCodebook.Book RubikChannel.Paired.Letter k L)
    (hBook : RubikCodebook.CoversAll RubikChannel.Paired.act Book)
    (hM : ∀ i, (Book i).card ≤ M) (c d : Rubik.Position n) :
    ∃ w : List (Rubik.Move n),
      w.length ≤ L * (rowCeil X.card k + 3) * (Y.card + C * (k + 1) * M) ∧
      RubikGlobalWord.Recolour {s | Rectangles X Y s} c.val d.val w := by
  classical
  obtain ⟨P⟩ := RubikRectangle.layout_exists X hk
  have hproper (b : Y) : 0 < b.val.val ∧ b.val.val + 1 < n := by
    obtain ⟨h0,h1⟩ := hXY.2.1 b.val b.property
    omega
  have hxc (a : X) (b : Y) := RubikRectangle.reachable_view
    (RubikPayload.admissibleGeneric hXY a.property b.property) (hproper b) c
  have hxd (a : X) (b : Y) := RubikRectangle.reachable_view
    (RubikPayload.admissibleGeneric hXY a.property b.property) (hproper b) d
  choose xc hx using hxc
  choose xd hy using hxd
  let e (a : X) : Fin P.blocks × Fin k := (P.owner a.val,P.row a.val)
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact P.injective a.val a.property b.val b.property (congrArg Prod.fst hab) (congrArg Prod.snd hab)
  let xv (j : Fin P.blocks) (b : Y) (r : Fin k) :=
    Function.extend e (fun a => xc a b) (fun _ => RubikChannel.Paired.seedState) (j,r)
  let yv (j : Fin P.blocks) (b : Y) (r : Fin k) :=
    Function.extend e (fun a => xd a b) (fun _ => RubikChannel.Paired.seedState) (j,r)
  let β := RubikChannel.Colour.pairAction RubikChannel.Paired.Seed B
  have hchoose (j : Fin P.blocks) (b : Y) :
      ∃ w : Fin L → Fin k → RubikChannel.Paired.Letter,
        (∀ i, w i ∈ Book i) ∧
        RubikCodebook.eval RubikChannel.Paired.act w (fun r => (β ^ (j.val % 4)) (xv j b r)) =
          fun r => (β ^ (j.val % 4)) (yv j b r) :=
    hBook _ _
  choose path hpath hpathEnd using hchoose
  let choice (i : Fin L) (j : Fin P.blocks) (b : Fin n) : Fin k → RubikChannel.Paired.Letter :=
    if hb : b ∈ Y then path j ⟨b,hb⟩ i else fun _ => RubikChannel.Paired.loopLetter
  have hchoices (i : Fin L) (j : Fin P.blocks) (b : Fin n) (hb : b ∈ Y) : choice i j b ∈ Book i := by
    simpa only [choice, dif_pos hb] using hpath j ⟨b,hb⟩ i
  have hrows (j : Fin P.blocks) : Admissible (P.rows j) Y := by
    refine ⟨?_,hXY.2.1,Finset.disjoint_of_subset_left (Finset.filter_subset _ _) hXY.2.2⟩
    intro a ha
    exact hXY.1 a (Finset.mem_filter.mp ha).1
  have hbuild (i : Fin L) (j : Fin P.blocks) :
      ∃ w : List (Rubik.Move n), w.length ≤ Y.card + C * (k + 1) * (Book i).card ∧
        ColumnRealizes (P.rows j) Y (fun a b => (choice i j b (P.row a)).val) w := by
    by_cases hz : P.rows j = ∅
    · refine ⟨baselineWord Y, ?_, ?_, ?_⟩
      · rw [(RubikPayload.baselinePhysical Y).1]
        exact Nat.le_add_right _ _
      · intro a ha
        simp only [hz, Finset.notMem_empty] at ha
      · intro s hs
        rfl
    · exact RubikRectangle.compileBlock C hP (P.rows j) Y (hrows j)
        (RubikRectangle.layout_rows_card P j) P.row (Book i) (choice i j) (hchoices i j)
  choose ws hwsLen hwsReal using hbuild
  let F (i : Fin L) (a : X) (b : Y) : Pair :=
    (path (P.owner a.val) b i (P.row a.val)).val
  have hframe : Framed X Y (fun a : X => P.owner a.val) F ws := by
    constructor
    · intro a b hb i j
      by_cases hj : j = P.owner a.val
      · subst j
        have ha : a.val ∈ P.rows (P.owner a.val) := Finset.mem_filter.mpr ⟨a.property,rfl⟩
        simpa [choice, F, b.property] using
          (hwsReal i (P.owner a.val)).1 a.val ha b.val b.property hb
      · simp only [hj, if_false]
        have ha : a.val ∉ P.rows j := by
          intro ha
          exact hj (Finset.mem_filter.mp ha).2.symm
        have hb' : b.val ∉ P.rows j := by
          intro hb'
          exact Finset.disjoint_left.mp hXY.2.2 (Finset.mem_filter.mp hb').1 b.property
        constructor <;> intro r
        · have hout := RubikRectangle.labels_outside_bands
            (RubikPayload.admissibleGeneric hXY a.property b.property) hb (P.rows j) (hrows j).1 ha hb' r
          have hnot : ¬ Rectangles (P.rows j) Y (RubikGeometry.lab a.val b.val r) :=
            fun hh => hout.1 ((RubikPayload.rectanglesBands (hrows j) _).mp hh).1
          rw [(hwsReal i j).2 _ hnot, (RubikPayload.baselineAction hXY a.property b.property hb r).1]
          rfl
        · have hout := RubikRectangle.labels_outside_bands
            (RubikPayload.admissibleGeneric hXY a.property b.property) hb (P.rows j) (hrows j).1 ha hb' r
          have hnot : ¬ Rectangles (P.rows j) Y (RubikOrbit.minusLab a.val b.val hb r) :=
            fun hh => hout.2 ((RubikPayload.rectanglesBands (hrows j) _).mp hh).1
          rw [(hwsReal i j).2 _ hnot, (RubikPayload.baselineAction hXY a.property b.property hb r).2]
          rfl
    · intro i j s hs
      apply (hwsReal i j).2
      rintro ⟨a,ha,b,hb,hh⟩
      exact hs ⟨a,(Finset.mem_filter.mp ha).1,b,hb,hh⟩
  have hpow (p : ℕ) (z : RubikChannel.Paired.State) :
      data ((β ^ p) z) = rawAction (B ^ p) (data z) := by
    have hh := (RubikChannel.Colour.pairAction RubikChannel.Paired.Seed).map_pow B p
    change data (((RubikChannel.Colour.pairAction RubikChannel.Paired.Seed B) ^ p) z) = _
    rw [← hh]
    exact RubikRectangle.data_act (B ^ p) z
  have hraw : ∀ (a : X) (b : Y) (hb : 0 < b.val.val ∧ b.val.val + 1 < n),
      rawAction ((List.ofFn (fun i => F i a b)).reverse.prod)
        (rawAction (B ^ ((P.owner a.val).val % 4)) (view c.val a.val b.val hb)) =
      rawAction (B ^ ((P.owner a.val).val % 4)) (view d.val a.val b.val hb) := by
    intro a b hb
    have hxa : xv (P.owner a.val) b (P.row a.val) = xc a b := he.extend_apply _ _ a
    have hya : yv (P.owner a.val) b (P.row a.val) = xd a b := he.extend_apply _ _ a
    have hw := congrFun (hpathEnd (P.owner a.val) b) (P.row a.val)
    change (List.ofFn (fun i => path (P.owner a.val) b i (P.row a.val))).foldl
      (fun z letter => RubikChannel.Paired.act letter z)
      ((β ^ ((P.owner a.val).val % 4)) (xv (P.owner a.val) b (P.row a.val))) =
        (β ^ ((P.owner a.val).val % 4)) (yv (P.owner a.val) b (P.row a.val)) at hw
    rw [hxa,hya] at hw
    have hd := congrArg data hw
    rw [RubikRectangle.data_word, hpow, hpow, hx, hy] at hd
    simpa only [F, List.map_ofFn, Function.comp_def] using hd
  have hcost (i : Fin L) (j : Fin P.blocks) :
      (ws i j).length ≤ Y.card + C * (k + 1) * M :=
    (hwsLen i j).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hM i)) _)
  have hw := RubikRectangle.framed_word X Y hXY (fun a : X => P.owner a.val) F ws hframe
    c.val d.val P.mod_four (Nat.mod_eq_zero_of_dvd hL) hraw _ hcost
  refine ⟨program ws, ?_, hw.2.1, ?_⟩
  · exact hw.1.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left L P.bound))
  · intro s hs
    have hinv : (RubikBand.wordPerm (program ws))⁻¹ s = s := by
      apply (RubikBand.wordPerm (program ws)).injective
      simpa using (hw.2.2 s hs).symm
    rw [RubikCompiler.physicalWordColouring]
    change c.val ((RubikBand.wordPerm (program ws))⁻¹ s) = c.val s
    rw [hinv]

#print axioms proof_RubikRectangle_compile_rectangle
