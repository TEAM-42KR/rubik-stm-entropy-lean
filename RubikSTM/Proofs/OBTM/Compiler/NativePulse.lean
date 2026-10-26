import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.OBTM.Compiler.PulseCleanSetup
import RubikSTM.Lemmas.OBTM.Compiler.PulseCutAction
import RubikSTM.Lemmas.OBTM.Compiler.NativeEvenConjugators
import RubikSTM.Lemmas.OBTM.Compiler.NativeInverseWord
import RubikSTM.Lemmas.OBTM.Compiler.CutBaselineNative
import RubikSTM.Lemmas.OBTM.Compiler.CutBaselineBand
import RubikSTM.Lemmas.OBTM.Band.WordPermAppend
import RubikSTM.Lemmas.Payloads.RectanglesBands
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_native_pulse : ∃ C : ℕ, RubikOBTMCompiler.NativePulseInterface C := by
  classical
  obtain ⟨K, setup⟩ := RubikOBTMCompiler.pulse_clean_setup
  refine ⟨2*K+1, ?_⟩
  intro n A Y hAY hord p g hg B hB
  have roots (a : Fin n) : ∃ σ τ : RubikOBTM.Finite.A, a ∈ A →
      σ.val * RubikOBTM.Band.actualSlabPlus^2 * σ.val⁻¹ = (RubikOBTM.Finite.phaseHom p (g a)).1.val ∧
      τ.val * RubikOBTM.Band.actualSlabMinus^2 * τ.val⁻¹ = (RubikOBTM.Finite.phaseHom p (g a)).2.val := by
    by_cases ha : a ∈ A
    · obtain ⟨σ, τ, hσ, hτ⟩ := RubikOBTMCompiler.native_even_conjugators p (g a) (hg a ha)
      exact ⟨σ, τ, fun _ => ⟨hσ,hτ⟩⟩
    · exact ⟨1,1,fun ha' => (ha ha').elim⟩
  choose σ τ conjugates using roots
  obtain ⟨U, hU, actU, outsideU⟩ := setup A Y hAY hord σ τ
  obtain ⟨V, hV, hVperm⟩ := RubikOBTMCompiler.native_inverse_word U
  obtain ⟨N, hN, hNperm, hNtwo⟩ := RubikOBTMCompiler.cut_baseline_native Y B hB (by
    intro d hd
    have h := hAY.2.1 d hd
    exact ⟨h.1, by have hsmall := h.2; omega⟩)
  let W := V ++ N ++ U
  have hW : RubikOBTM.Band.wordPerm W = RubikOBTM.Band.wordPerm U *
      RubikOBTMCompiler.cutBaseline Y B * (RubikOBTM.Band.wordPerm U)⁻¹ := by
    dsimp [W]
    rw [RubikOBTM.Band.wordPerm_append, RubikOBTM.Band.wordPerm_append, hVperm, hNperm]
    exact (mul_assoc _ _ _).symm
  refine ⟨W, ?_, ?_, ?_⟩
  · dsimp [W]
    simp only [List.length_append]
    nlinarith
  · intro a ha b hb
    let r : RubikPayload.Pair := ((σ a).val,(τ a).val)
    let k := (B.filter (fun d => b ≤ d)).card
    have hconj : r * RubikOBTMCompiler.halfPair * r⁻¹ =
        RubikOBTM.Finite.inclusion (RubikOBTM.Finite.phaseHom p (g a)) := by
      apply Prod.ext
      · exact (conjugates a ha).1
      · exact (conjugates a ha).2
    have hp : (RubikOBTM.Finite.inclusion (RubikOBTM.Finite.phaseHom p (g a))) ^ k =
        r * RubikOBTMCompiler.halfPair ^ k * r⁻¹ := by
      rw [← hconj, conj_pow]
    have hQ := RubikOBTMCompiler.pulse_cut_action hAY hord B hB ha hb
    have hinvP (i : Fin 24) :
        (RubikOBTM.Band.wordPerm U)⁻¹ (RubikOBTM.Band.plus a b i) =
          RubikOBTM.Band.plus a b ((σ a).val⁻¹ i) := by
      apply (RubikOBTM.Band.wordPerm U).injective
      simp only [← Equiv.Perm.mul_apply, mul_inv_cancel]
      change RubikOBTM.Band.plus a b i = RubikOBTM.Band.wordPerm U
        (RubikOBTM.Band.plus a b ((σ a).val⁻¹ i))
      rw [(actU a ha b hb).1]
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel]
      rfl
    have hinvM (i : Fin 24) :
        (RubikOBTM.Band.wordPerm U)⁻¹ (RubikOBTM.Band.minus a b i) =
          RubikOBTM.Band.minus a b ((τ a).val⁻¹ i) := by
      apply (RubikOBTM.Band.wordPerm U).injective
      simp only [← Equiv.Perm.mul_apply, mul_inv_cancel]
      change RubikOBTM.Band.minus a b i = RubikOBTM.Band.wordPerm U
        (RubikOBTM.Band.minus a b ((τ a).val⁻¹ i))
      rw [(actU a ha b hb).2]
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel]
      rfl
    dsimp only [RubikOBTMCompiler.NativeActsPair]
    change (∀ i, RubikOBTM.Band.wordPerm W (RubikOBTM.Band.plus a b i) =
        RubikOBTM.Band.plus a b (((RubikOBTM.Finite.inclusion (RubikOBTM.Finite.phaseHom p (g a))) ^ k).1 i)) ∧
      ∀ i, RubikOBTM.Band.wordPerm W (RubikOBTM.Band.minus a b i) =
        RubikOBTM.Band.minus a b (((RubikOBTM.Finite.inclusion (RubikOBTM.Finite.phaseHom p (g a))) ^ k).2 i)
    rw [hp]
    constructor
    · intro i
      rw [hW]
      change RubikOBTM.Band.wordPerm U
        (RubikOBTMCompiler.cutBaseline Y B ((RubikOBTM.Band.wordPerm U)⁻¹ (RubikOBTM.Band.plus a b i))) = _
      rw [hinvP, hQ.1, (actU a ha b hb).1]
      rfl
    · intro i
      rw [hW]
      change RubikOBTM.Band.wordPerm U
        (RubikOBTMCompiler.cutBaseline Y B ((RubikOBTM.Band.wordPerm U)⁻¹ (RubikOBTM.Band.minus a b i))) = _
      rw [hinvM, hQ.2, (actU a ha b hb).2]
      rfl
  · intro s hs
    have hInv : (RubikOBTM.Band.wordPerm U)⁻¹ s = s := by
      apply (RubikOBTM.Band.wordPerm U).injective
      simp only [← Equiv.Perm.mul_apply, mul_inv_cancel]
      exact (outsideU s hs).symm
    have hQout : ¬RubikPayload.Rectangles A Y (RubikOBTMCompiler.cutBaseline Y B s) := by
      intro hq
      obtain ⟨⟨a,ha,has⟩,⟨b,hb,hbs⟩⟩ := (RubikPayload.rectanglesBands hAY _).mp hq
      apply hs
      apply (RubikPayload.rectanglesBands hAY s).mpr
      exact ⟨⟨a,ha,(RubikOBTMCompiler.cut_baseline_band Y B a s).mp has⟩,
        ⟨b,hb,(RubikOBTMCompiler.cut_baseline_band Y B b s).mp hbs⟩⟩
    rw [hW]
    change RubikOBTM.Band.wordPerm U
      (RubikOBTMCompiler.cutBaseline Y B ((RubikOBTM.Band.wordPerm U)⁻¹ s)) = _
    rw [hInv, outsideU _ hQout]
