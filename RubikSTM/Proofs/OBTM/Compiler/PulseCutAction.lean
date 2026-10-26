import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.OBTM.Compiler.PulseIntervalData
import RubikSTM.Lemmas.OBTM.Band.SlabActionIf
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_pulse_cut_action {n : ℕ} {A Y : Finset (Fin n)} (h : RubikPayload.Admissible A Y)
    (hord : Set.OrdConnected (Y : Set (Fin n))) (B : Finset (Fin n)) (hB : B ⊆ Y)
    {a b : Fin n} (ha : a ∈ A) (hb : b ∈ Y) :
    (∀ i, RubikOBTMCompiler.cutBaseline Y B (RubikOBTM.Band.plus a b i) =
      RubikOBTM.Band.plus a b ((RubikOBTMCompiler.halfPair ^ (B.filter (fun d => b ≤ d)).card).1 i)) ∧
    (∀ i, RubikOBTMCompiler.cutBaseline Y B (RubikOBTM.Band.minus a b i) =
      RubikOBTM.Band.minus a b ((RubikOBTMCompiler.halfPair ^ (B.filter (fun d => b ≤ d)).card).2 i)) := by
  classical
  have hY : Y.Nonempty := ⟨b, hb⟩
  have hdata := RubikOBTMCompiler.pulse_interval_data h hord hY
  have hadm := hdata.2.1 a ha
  have hact (d : Fin n) (hd : d ∈ B) (i : Fin 24) :=
    RubikOBTM.Band.slab_action_if a (Y.min' hY) (Y.max' hY) hadm d b
      ((hdata.1 d).mp (hB hd)) ((hdata.1 b).mp hb) i
  have count : (B.filter (fun d => b ≤ d)).card =
      B.toList.countP (fun d => decide (b ≤ d)) := by
    simpa only [Finset.toList_toFinset] using
      (B.nodup_toList.card_eq_countP (P:=fun d => b ≤ d))
  have H (lab : Fin 24 → Rubik.Sticker n) (q : Equiv.Perm (Fin 24))
      (acts : ∀ d ∈ B, ∀ i : Fin 24,
        RubikOBTM.Band.slabPerm (Y.min' hY) d (lab i) = lab ((if b ≤ d then q else 1) i)) :
      ∀ ls : List (Fin n), (∀ d ∈ ls, d ∈ B) → ∀ i : Fin 24,
      ((ls.map (fun d => RubikOBTM.Band.slabPerm (Y.min' hY) d ^ 2)).reverse.prod) (lab i) =
        lab (((q^2) ^ (ls.countP (fun d => decide (b ≤ d)))) i) := by
    intro ls hls
    induction ls with
    | nil => intro i; simp
    | cons d ls ih =>
      intro i
      have hd := hls d (by simp)
      have htail : ∀ e ∈ ls, e ∈ B := fun e he => hls e (by simp [he])
      have hsq : (RubikOBTM.Band.slabPerm (Y.min' hY) d ^ 2) (lab i) =
          if b ≤ d then lab ((q^2) i) else lab i := by
        simp only [pow_two, Equiv.Perm.mul_apply, acts d hd]
        by_cases hbd : b ≤ d <;> simp [hbd]
      simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton,
        Equiv.Perm.mul_apply]
      rw [hsq]
      by_cases hbd : b ≤ d
      · rw [if_pos hbd, ih htail]
        simp [hbd, pow_succ, Equiv.Perm.mul_apply]
      · rw [if_neg hbd, ih htail]
        simp [hbd]
  unfold RubikOBTMCompiler.cutBaseline
  rw [dif_pos hY]
  rw [count]
  constructor
  · intro i
    simpa [RubikOBTMCompiler.halfPair] using
      H (RubikOBTM.Band.plus a b) RubikOBTM.Band.actualSlabPlus
        (fun d hd i => by simpa only [Fin.le_def] using (hact d hd i).1)
        B.toList (fun d hd => Finset.mem_toList.mp hd) i
  · intro i
    simpa [RubikOBTMCompiler.halfPair] using
      H (RubikOBTM.Band.minus a b) RubikOBTM.Band.actualSlabMinus
        (fun d hd i => by simpa only [Fin.le_def] using (hact d hd i).2)
        B.toList (fun d hd => Finset.mem_toList.mp hd) i
