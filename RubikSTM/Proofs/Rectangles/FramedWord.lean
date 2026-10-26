import RubikSTM.Definitions.Rectangles.Framed
import RubikSTM.Lemmas.Rectangles.OneActiveBlock
import RubikSTM.Lemmas.Rectangles.ActsPairFlatten
import RubikSTM.Lemmas.Rectangles.PairColouring
import RubikSTM.Lemmas.Rectangles.RectanglesInvariant
import RubikSTM.Lemmas.Rectangles.ColumnBaselineFour
import RubikSTM.Lemmas.WordConstruction.PaddedProgram
import RubikSTM.Lemmas.WordConstruction.ExteriorCancellation
import RubikSTM.Lemmas.WordConstruction.ConcatenateWords
import RubikSTM.Lemmas.Orbits.MinusRange
import RubikSTM.Lemmas.Payloads.AdmissibleGeneric
set_option autoImplicit false

open RubikRectangle RubikPayload

theorem proof_RubikRectangle_framed_word {n L t : ℕ} (X Y : Finset (Fin n)) (hXY : Admissible X Y)
    (owner : X → Fin t) (F : Fin L → X → Y → Pair)
    (ws : Fin L → Fin t → List (Rubik.Move n)) (hframe : Framed X Y owner F ws)
    (c d : Rubik.Colouring n) (ht : t % 4 = 1) (hL : L % 4 = 0)
    (hraw : ∀ (a : X) (b : Y) (hb : 0 < b.val.val ∧ b.val.val + 1 < n),
      rawAction ((List.ofFn (fun i => F i a b)).reverse.prod)
        (rawAction (B ^ ((owner a).val % 4)) (view c a.val b.val hb)) =
      rawAction (B ^ ((owner a).val % 4)) (view d a.val b.val hb))
    (cost : ℕ) (hcost : ∀ i j, (ws i j).length ≤ cost) :
    (program ws).length ≤ L * t * cost ∧
      (∀ s : Rubik.Sticker n, Rectangles X Y s → Rubik.applyWord (program ws) c s = d s) ∧
      (∀ s : Rubik.Sticker n, ¬ Rectangles X Y s → RubikBand.wordPerm (program ws) s = s) := by
  classical
  letI : MulAction Pair Data := MulAction.compHom Data rawHom
  have hB : (B : Pair) ^ 4 = 1 := by decide
  have hfn {A D : Type} {q : ℕ} (R : A → D → Prop)
      (f : Fin q → A) (g : Fin q → D) (h : ∀ i, R (f i) (g i)) :
      List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      exact List.Forall₂.cons (h 0) (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ))
  have hflat (vs : List (List (Rubik.Move n))) :
      RubikBand.wordPerm vs.flatten = (vs.map RubikBand.wordPerm).reverse.prod := by
    induction vs with
    | nil => rfl
    | cons v vs ih =>
      simp only [List.flatten_cons, List.map_cons, List.reverse_cons,
        List.prod_append, List.prod_singleton]
      simp only [RubikBand.wordPerm, List.map_append, List.reverse_append, List.prod_append] at *
      rw [ih]
  have hview (a : X) (b : Y) (hb : 0 < b.val.val ∧ b.val.val + 1 < n) :
      view (Rubik.applyWord (program ws) c) a.val b.val hb = view d a.val b.val hb := by
    let j := owner a
    let fs : List Pair := List.ofFn (fun i => F i a b)
    let glayer : Fin L → Pair := fun i => B ^ (t - (j.val + 1)) * F i a b * B ^ j.val
    have hlayer (i : Fin L) : ActsPair a.val b.val hb (List.ofFn (ws i)).flatten (glayer i) := by
      have hh := RubikRectangle.actsPair_flatten a.val b.val hb
        (List.ofFn (ws i)) (List.ofFn (fun q => if q = j then F i a b else B))
        (hfn _ _ _ (hframe.1 a b hb i))
      have he : t - 1 - j.val = t - (j.val + 1) := by omega
      simpa only [RubikRectangle.oneActiveBlock, he] using hh
    have hall : ActsPair a.val b.val hb (program ws) (List.ofFn glayer).reverse.prod :=
      RubikRectangle.actsPair_flatten a.val b.val hb _ _ (hfn _ _ _ hlayer)
    have hp := (RubikCompiler.paddedProgram B hB t (j.val + 1) (by omega)
      (by have hj := j.isLt; omega) ht fs (view c a.val b.val hb) (view d a.val b.val hb)
      (by
        simpa only [Nat.add_sub_cancel, MulAction.compHom_smul_def, Equiv.Perm.smul_def,
          rawHom, MonoidHom.coe_mk, OneHom.coe_mk, j, fs] using hraw a b hb)).2
    have heq : fs.map (fun f => B ^ (t - (j.val + 1)) * f * B ^ (j.val + 1 - 1)) =
        List.ofFn glayer := by simp only [fs, List.map_ofFn, Nat.add_sub_cancel]; rfl
    rw [heq] at hp
    exact (RubikRectangle.pairColouring a.val b.val hb (program ws)
      (List.ofFn glayer).reverse.prod hall c).trans hp
  have hclayer (i : Fin L) : (List.ofFn (ws i)).flatten.length ≤ t * cost := by
    simpa only [List.length_ofFn] using
      (RubikCompiler.concatenateWords Rubik.movePermutation (List.ofFn (ws i)) cost (by
        intro w hw
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
        exact hcost i j)).2.2
  have hctotal : (program ws).length ≤ L * t * cost := by
    simpa only [program, List.length_ofFn, Nat.mul_assoc] using
      (RubikCompiler.concatenateWords Rubik.movePermutation
        (List.ofFn (fun i => (List.ofFn (ws i)).flatten)) (t * cost) (by
          intro w hw
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
          exact hclayer i)).2.2
  refine ⟨hctotal, ?_, ?_⟩
  · intro s hs
    obtain ⟨a, ha, b, hbY, hs⟩ := hs
    have hb : 0 < b.val ∧ b.val + 1 < n := by
      obtain ⟨h0,h1⟩ := hXY.2.1 b hbY
      omega
    have hv := hview ⟨a,ha⟩ ⟨b,hbY⟩ hb
    rcases hs with hp | hm
    · obtain ⟨i,rfl⟩ := hp
      exact congrFun (congrArg Prod.fst hv) i
    · rw [← RubikOrbit.minusRange (RubikPayload.admissibleGeneric hXY ha hbY) hb] at hm
      obtain ⟨i,rfl⟩ := hm
      exact congrFun (congrArg Prod.snd hv) i
  · let Z := columnBaseline Y
    let S : Set (Rubik.Sticker n) := {s | ¬ Rectangles X Y s}
    let layers := List.ofFn (fun i : Fin L => List.ofFn (fun j : Fin t => RubikBand.wordPerm (ws i j)))
    have hinv : ∀ s ∈ S, Z • s ∈ S := by
      intro s hs
      exact (not_congr (RubikRectangle.rectangles_invariant X Y (baselineWord Y) s)).mpr hs
    have hc := RubikCompiler.exteriorCancellation Z (RubikRectangle.columnBaseline_four Y) S hinv
      layers (by intro bs hbs; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hbs; simpa using ht)
      (by
        intro bs hbs p hp s hs
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hbs
        obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
        exact hframe.2 i j s hs)
      (by simpa [layers] using hL)
    intro s hs
    have he : RubikBand.wordPerm (program ws) = (layers.map (fun bs => bs.reverse.prod)).reverse.prod := by
      simp only [program, hflat, List.map_ofFn, layers, Function.comp_def]
    rw [he]
    exact hc s hs

#print axioms proof_RubikRectangle_framed_word
