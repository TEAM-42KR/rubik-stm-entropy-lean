import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Definitions.OBTM.Compiler.VectorAction
import RubikSTM.Lemmas.OBTM.Compiler.NativeOddLayout
import RubikSTM.Lemmas.OBTM.Compiler.NativeLayoutRowsCard
import RubikSTM.Lemmas.OBTM.Compiler.OddPadding
import RubikSTM.Lemmas.OBTM.Compiler.CommonReachableView
import RubikSTM.Lemmas.OBTM.Compiler.CommonLabels
import RubikSTM.Lemmas.OBTM.Compiler.LiftedBookCover
import RubikSTM.Lemmas.OBTM.Compiler.LiftedBookCard
import RubikSTM.Lemmas.OBTM.Compiler.OrderedBackwardSelection
import RubikSTM.Lemmas.OBTM.Compiler.NativePhaseOfPulse
import RubikSTM.Lemmas.OBTM.Compiler.NativePairOutsideRows
import RubikSTM.Lemmas.OBTM.Compiler.CutBaselinePair
import RubikSTM.Lemmas.OBTM.Compiler.CellBaselineTwo
import RubikSTM.Lemmas.OBTM.Compiler.NativePairColouring
import RubikSTM.Lemmas.OBTM.Compiler.NativeVectorData
import RubikSTM.Lemmas.OBTM.Compiler.NativeFramedWord
import RubikSTM.Lemmas.OBTM.Compiler.CutBaselineNative
import RubikSTM.Lemmas.OBTM.Compiler.FullBaselineRectangles
import RubikSTM.Lemmas.Rectangles.DataAct
import RubikSTM.Lemmas.Payloads.AdmissibleGeneric
import RubikSTM.Lemmas.Orbits.FlipLabel
import RubikSTM.Lemmas.OBTM.Band.WordPermApply
set_option autoImplicit false
open RubikOBTMCompiler RubikRectangle RubikPayload

theorem proof_RubikOBTMCompiler_rectangle_of_native_pulse (hP : ∃ C : ℕ, NativePulseInterface C) :
    RubikOBTM.Global.RectangleCompiler := by
  classical
  obtain ⟨C,hP⟩ := hP
  refine ⟨C,?_⟩
  intro n X Y hXY hY k L M hk hL hL4 hT Book hBook hM c d
  obtain ⟨P⟩ := native_odd_layout X hk
  have hproper (b : Y) : 0 < b.val.val ∧ b.val.val+1<n := by
    have hh := hXY.2.1 b.val b.property
    dsimp [Half] at hh
    omega
  have hxc (a : X) (b : Y) := common_reachable_view
    (RubikPayload.admissibleGeneric hXY a.property b.property) (hproper b) c
  have hxd (a : X) (b : Y) := common_reachable_view
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
  let β (b : Y) := RubikChannel.Colour.pairAction RubikChannel.Paired.Seed (cellBaseline Y b.val)
  let D := liftedBook hT (fun _ => RubikOBTM.Finite.Intrinsic) RubikOBTM.Finite.periodicC Book
  let act : (i : Fin L) → (Fin k → RubikOBTM.Finite.Intrinsic) → Equiv.Perm (Fin k → RubikChannel.Paired.State) :=
    fun i => vectorAction (k:=k) (RubikOBTM.Finite.periodicAct (RubikOBTM.Periodic.phase _ hT i))
  have hD := lifted_book_cover hT (fun _ => RubikOBTM.Finite.Intrinsic)
    RubikOBTM.Finite.periodicC RubikOBTM.Finite.periodicAct Book hBook
  have hchoose (j : Fin P.blocks) := ordered_backward_selection Y act D hD
    (fun b r => (β b ^ (j.val%2)) (xv j b r))
    (fun b r => (β b ^ (j.val%2)) (yv j b r))
  choose path hpath hpathEnd using hchoose
  let choice (i : Fin L) (j : Fin P.blocks) (b : Fin n) := path j b i
  have hchoices (i : Fin L) (j : Fin P.blocks) (b : Fin n) (hb : b ∈ Y) :
      choice i j b ∈ D i := hpath j b hb i
  have hrows (j : Fin P.blocks) : Admissible (P.rows j) Y := by
    refine ⟨?_,hXY.2.1,hXY.2.2.mono_left (Finset.filter_subset _ _)⟩
    intro a ha
    exact hXY.1 a (Finset.mem_filter.mp ha).1
  have hDnative (i : Fin L) (g : Fin k → RubikOBTM.Finite.Intrinsic) (hg : g ∈ D i)
      (z : Fin k) : g z ∈ RubikOBTM.Finite.nativeC := by
    simp only [D,liftedBook,Finset.mem_image] at hg
    obtain ⟨w,hw,hg'⟩ := hg
    have he : (w z).val = g z := congrFun hg' z
    rw [← he]
    exact (w z).property
  have hbuild (i : Fin L) (j : Fin P.blocks) := native_phase_of_pulse C hP (P.rows j) Y
    (hrows j) hY (RubikOBTM.Finite.phaseAt (RubikOBTM.Periodic.phase _ hT i)) P.row (D i)
    (hDnative i) (choice i j) (hchoices i j)
  choose ws hwsLen hwsActs hwsOut using hbuild
  let pair (i : Fin L) (a : X) (b : Y) : Pair :=
    RubikOBTM.Finite.inclusion (RubikOBTM.Finite.phaseHom
      (RubikOBTM.Finite.phaseAt (RubikOBTM.Periodic.phase _ hT i))
      ((∏ z ∈ Y.filter (fun z => b.val ≤ z), choice i (P.owner a.val) z) (P.row a.val)))
  let F (i : Fin L) (a : X) (b : Y) := rawHom (pair i a b)
  let Braw (b : Y) := rawHom (cellBaseline Y b.val)
  have hcell (i : Fin L) (j : Fin P.blocks) (z : Rubik.Colouring n) (a : X) (b : Y) :
      commonView (RubikOBTM.applyBlockWord (ws i j) z) a.val b.val =
        (if j=P.owner a.val then F i a b else Braw b) (commonView z a.val b.val) := by
    by_cases hj : j=P.owner a.val
    · subst j
      have ha : a.val ∈ P.rows (P.owner a.val) := Finset.mem_filter.mpr ⟨a.property,rfl⟩
      rw [if_pos rfl]
      exact native_pair_colouring a.val b.val _ _
        (hwsActs i (P.owner a.val) a.val ha b.val b.property) z
    · have ha : a.val ∉ P.rows j := by
        intro h
        exact hj (Finset.mem_filter.mp h).2.symm
      have hg : NativeActsPair a.val b.val (ws i j) (cellBaseline Y b.val) := by
        have hout := native_pair_outside_rows hXY (Finset.filter_subset _ _) a.property ha b.property
        have hb := cut_baseline_pair hXY hY a.property b.property Y (Finset.Subset.refl _)
        constructor
        · intro r
          exact (hwsOut i j _ (hout r).1).trans (hb.1 r)
        · intro r
          exact (hwsOut i j _ (hout r).2).trans (hb.2 r)
      rw [if_neg hj]
      exact native_pair_colouring a.val b.val _ _ hg z
  have hBraw (b : Y) : Braw b ^ 2 = 1 := by
    rw [← map_pow,cell_baseline_two,map_one]
  have hbaseProper : ∀ b∈Y, 1 ≤ b.val ∧ b.val<n-1 := by
    intro b hb
    have hh := hXY.2.1 b hb
    dsimp [Half] at hh
    omega
  have hQ : fullBaseline Y ^ 2 = 1 :=
    (cut_baseline_native Y Y (Finset.Subset.refl _) hbaseProper).choose_spec.2.2
  have hInv (s : Rubik.Sticker n) (hs : ¬ Rectangles X Y s) :
      ¬ Rectangles X Y (fullBaseline Y s) :=
    fun h => hs ((full_baseline_rectangles hXY s).mp h)
  have hOutside (i : Fin L) (j : Fin P.blocks) (s : Rubik.Sticker n)
      (hs : ¬ Rectangles X Y s) : RubikOBTM.Band.wordPerm (ws i j) s = fullBaseline Y s := by
    apply hwsOut i j
    rintro ⟨a,ha,b,hb,hr⟩
    exact hs ⟨a,(Finset.mem_filter.mp ha).1,b,hb,hr⟩
  have hpow (b : Y) (m : ℕ) (z : RubikChannel.Paired.State) :
      data ((β b ^ m) z) = (Braw b ^ m) (data z) := by
    rw [← (RubikChannel.Colour.pairAction RubikChannel.Paired.Seed).map_pow]
    rw [← rawHom.map_pow]
    exact RubikRectangle.data_act _ _
  have hraw (a : X) (b : Y) : (List.ofFn (fun i => F i a b)).reverse.prod
      ((Braw b ^ ((P.owner a.val).val%2)) (commonView c.val a.val b.val)) =
        (Braw b ^ ((P.owner a.val).val%2)) (commonView d.val a.val b.val) := by
    have hxa : xv (P.owner a.val) b (P.row a.val) = xc a b := he.extend_apply _ _ a
    have hya : yv (P.owner a.val) b (P.row a.val) = xd a b := he.extend_apply _ _ a
    have hw := congrFun (hpathEnd (P.owner a.val) b) (P.row a.val)
    let ps : List (Fin k → Pair) := List.ofFn (fun i : Fin L => fun r =>
      RubikOBTM.Finite.inclusion (RubikOBTM.Finite.phaseHom
        (RubikOBTM.Finite.phaseAt (RubikOBTM.Periodic.phase _ hT i))
        ((∏ z ∈ Y.filter (fun z => b.val ≤ z), path (P.owner a.val) z i) r)))
    have hprog : phasePerm act
        (fun i => ∏ z ∈ Y.filter (fun z => b.val ≤ z), path (P.owner a.val) z i) =
        (ps.map (fun g => coordinatePerm (fun r =>
          RubikChannel.Colour.pairAction RubikChannel.Paired.Seed (g r)))).reverse.prod := by
      simp only [phasePerm,ps,List.map_ofFn]
      rfl
    have hv := hpathEnd (P.owner a.val) b
    rw [hprog] at hv
    have hd := congrArg (fun z : Fin k → RubikChannel.Paired.State => data (z (P.row a.val))) hv
    rw [native_vector_data,hpow,hpow,hxa,hya,hx,hy] at hd
    have hp : ps.map (fun g => g (P.row a.val)) = List.ofFn (fun i => pair i a b) := by
      simp only [ps,List.map_ofFn,pair,choice]
      rfl
    rw [hp] at hd
    have hm : rawHom (List.ofFn (fun i => pair i a b)).reverse.prod =
        (List.ofFn (fun i => F i a b)).reverse.prod := by
      simpa only [List.map_reverse,List.map_ofFn,Function.comp_def,F] using
        rawHom.map_list_prod (List.ofFn (fun i => pair i a b)).reverse
    change rawHom (List.ofFn (fun i => pair i a b)).reverse.prod
      ((Braw b ^ ((P.owner a.val).val%2)) (commonView c.val a.val b.val)) =
        (Braw b ^ ((P.owner a.val).val%2)) (commonView d.val a.val b.val) at hd
    rw [hm] at hd
    exact hd
  have hcost (i : Fin L) (j : Fin P.blocks) :
      (ws i j).length ≤ Y.card+C*(k+1)*M := by
    have hcard := (lifted_book_card hT (fun _ => RubikOBTM.Finite.Intrinsic)
      RubikOBTM.Finite.periodicC Book i).trans (hM i)
    have hrow := native_layout_rows_card P j
    exact (hwsLen i j).trans (Nat.add_le_add_left
      (Nat.mul_le_mul (Nat.mul_le_mul_left C (Nat.add_le_add_right hrow 1)) hcard) _)
  have ht : P.blocks%2=1 := by
    rw [P.blocks_eq]
    exact (odd_padding _).2
  have hfr := native_framed_word (fun z (a : X) (b : Y) => commonView z a.val b.val)
    (fun a : X => P.owner a.val) Braw hBraw F ws hcell (fullBaseline Y) hQ
    {s | ¬ Rectangles X Y s} hInv hOutside c.val d.val ht
    (by exact Nat.mod_eq_zero_of_dvd (dvd_trans (by decide : 2 ∣ 4) hL4)) hraw _ hcost
  refine ⟨nativeProgram ws,?_,?_,?_⟩
  · have hb : P.blocks ≤ rowCeil X.card k+3 := by
      rw [P.blocks_eq]
      have hp := (odd_padding (rowCeil X.card k)).1
      omega
    exact hfr.1.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left L hb))
  · intro s hs
    rcases hs with ⟨a,ha,b,hb,hr⟩
    have hh := hfr.2.1 (⟨a,ha⟩ : X) (⟨b,hb⟩ : Y)
    have hg := RubikPayload.admissibleGeneric hXY ha hb
    have hp := hproper (⟨b,hb⟩ : Y)
    rcases hr with ⟨r,rfl⟩ | ⟨r,rfl⟩
    · have hc := congrFun (congrArg Prod.fst hh) r
      simpa only [commonView,Function.comp_def,(common_labels hg hp r).1] using hc
    · have hc := congrFun (congrArg Prod.snd hh) (RubikOrbit.swapPhi⁻¹ r)
      have hm : RubikOBTM.Band.minus a b (RubikOrbit.swapPhi⁻¹ r) = RubikGeometry.lab b a r := by
        rw [(common_labels hg hp _).2,RubikOrbit.flipLabel hg hp]
        simp
      simpa only [commonView,Function.comp_def,hm] using hc
  · intro s hs
    have hinv : (RubikOBTM.Band.wordPerm (nativeProgram ws))⁻¹ s=s := by
      apply (RubikOBTM.Band.wordPerm (nativeProgram ws)).injective
      simpa using (hfr.2.2 s hs).symm
    rw [RubikOBTM.Band.wordPerm_apply,hinv]
