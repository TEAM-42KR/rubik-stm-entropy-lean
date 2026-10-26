import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.OBTM.Compiler.CommonLabels
import RubikSTM.Lemmas.Rectangles.LabelsOutsideBands
import RubikSTM.Lemmas.Payloads.AdmissibleGeneric
import RubikSTM.Lemmas.Payloads.RectanglesBands
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_native_pair_outside_rows {n : ℕ} {X A Y : Finset (Fin n)}
    (hXY : RubikPayload.Admissible X Y) (hAX : A ⊆ X)
    {a b : Fin n} (ha : a ∈ X) (haA : a ∉ A) (hb : b ∈ Y) (i : Fin 24) :
    ¬ RubikPayload.Rectangles A Y (RubikOBTM.Band.plus a b i) ∧
      ¬ RubikPayload.Rectangles A Y (RubikOBTM.Band.minus a b i) := by
  have hg := RubikPayload.admissibleGeneric hXY ha hb
  have hb' : 0 < b.val ∧ b.val+1<n := by
    have hh := hXY.2.1 b hb
    dsimp [RubikPayload.Half] at hh
    omega
  have hAY : RubikPayload.Admissible A Y :=
    ⟨(fun x hx => hXY.1 x (hAX hx)),hXY.2.1,hXY.2.2.mono_left hAX⟩
  have hbA : b ∉ A := fun h => Finset.disjoint_left.mp hXY.2.2 (hAX h) hb
  have h0 := RubikRectangle.labels_outside_bands hg hb' A hAY.1 haA hbA i
  have hl := RubikOBTMCompiler.common_labels hg hb' i
  constructor
  · intro h
    apply h0.1
    rw [← hl.1]
    exact ((RubikPayload.rectanglesBands hAY _).mp h).1
  · intro h
    apply h0.2
    rw [← hl.2]
    exact ((RubikPayload.rectanglesBands hAY _).mp h).1
