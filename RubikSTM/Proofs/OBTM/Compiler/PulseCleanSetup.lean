import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.OBTM.Compiler.PulseIntervalData
import RubikSTM.Lemmas.OBTM.Compiler.PulseLabelsAvoidRow
import RubikSTM.Lemmas.OBTM.Band.UniformCleanEvenControl
import RubikSTM.Lemmas.OBTM.Band.PairedRangeIff
import RubikSTM.Lemmas.OBTM.Band.WordPermAppend
import RubikSTM.Lemmas.Payloads.RectanglesBands
import RubikSTM.Lemmas.Payloads.AdmissibleGeneric
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_pulse_clean_setup : ∃ K : ℕ, ∀ {n : ℕ} (A Y : Finset (Fin n)),
    RubikPayload.Admissible A Y → Set.OrdConnected (Y : Set (Fin n)) →
    ∀ σ τ : Fin n → RubikOBTM.Finite.A, ∃ U : List (RubikOBTM.BlockMove n),
      U.length ≤ K*A.card ∧
      (∀ a ∈ A, ∀ b ∈ Y, RubikOBTMCompiler.NativeActsPair a b U ((σ a).val,(τ a).val)) ∧
      ∀ s : Rubik.Sticker n, ¬RubikPayload.Rectangles A Y s →
        RubikOBTM.Band.wordPerm U s = s := by
  classical
  obtain ⟨K, hK, control⟩ := RubikOBTM.Band.uniform_clean_even_control
  refine ⟨K, ?_⟩
  intro n A Y hAY hord σ τ
  by_cases hY : Y.Nonempty
  · have H : ∀ S : Finset (Fin n), RubikPayload.Admissible S Y →
        ∃ U : List (RubikOBTM.BlockMove n), U.length ≤ K*S.card ∧
        (∀ a ∈ S, ∀ b ∈ Y, RubikOBTMCompiler.NativeActsPair a b U ((σ a).val,(τ a).val)) ∧
        ∀ s : Rubik.Sticker n, ¬RubikPayload.Rectangles S Y s →
          RubikOBTM.Band.wordPerm U s = s := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        intro hS
        refine ⟨[], by simp, ?_, ?_⟩
        · simp
        · intro s hs; rfl
      | @insert a S ha ih =>
        intro hS
        have hsub : S ⊆ insert a S := Finset.subset_insert _ _
        have hSY : RubikPayload.Admissible S Y :=
          ⟨fun c hc => hS.1 c (hsub hc), hS.2.1,
            Finset.disjoint_left.mpr (fun c hc hcy => Finset.disjoint_left.mp hS.2.2 (hsub hc) hcy)⟩
        obtain ⟨U, hU, actU, outsideU⟩ := ih hSY
        have haI : a ∈ insert a S := Finset.mem_insert_self _ _
        have hdata := RubikOBTMCompiler.pulse_interval_data hS hord hY
        have hadm := hdata.2.1 a haI
        obtain ⟨V, hV, actV, outsideV⟩ :=
          control n a (Y.min' hY) (Y.max' hY) hadm
            (σ a).val (τ a).val (σ a).property (τ a).property
        have skipU (b : Fin n) (hb : b ∈ Y) (i : Fin 24) :
            RubikOBTM.Band.wordPerm U (RubikOBTM.Band.plus a b i) = RubikOBTM.Band.plus a b i ∧
            RubikOBTM.Band.wordPerm U (RubikOBTM.Band.minus a b i) = RubikOBTM.Band.minus a b i := by
          have hg := RubikPayload.admissibleGeneric hS haI hb
          have havoid (c : Fin n) (hc : c ∈ S) :=
            RubikOBTMCompiler.pulse_labels_avoid_row hg (hSY.1 c hc)
              (by intro he; exact ha (he ▸ hc))
              (by intro he; exact Finset.disjoint_left.mp hSY.2.2 hc (he.symm ▸ hb)) i
          constructor
          · apply outsideU
            intro hs
            obtain ⟨c, hc, hcs⟩ := ((RubikPayload.rectanglesBands hSY _).mp hs).1
            exact (havoid c hc).1 hcs
          · apply outsideU
            intro hs
            obtain ⟨c, hc, hcs⟩ := ((RubikPayload.rectanglesBands hSY _).mp hs).1
            exact (havoid c hc).2 hcs
        have skipV (c : Fin n) (hc : c ∈ S) (b : Fin n) (hb : b ∈ Y) (i : Fin 24) :
            RubikOBTM.Band.wordPerm V (RubikOBTM.Band.plus c b i) = RubikOBTM.Band.plus c b i ∧
            RubikOBTM.Band.wordPerm V (RubikOBTM.Band.minus c b i) = RubikOBTM.Band.minus c b i := by
          have hg := RubikPayload.admissibleGeneric hSY hc hb
          have havoid := RubikOBTMCompiler.pulse_labels_avoid_row hg (hS.1 a haI)
            (by intro he; exact ha (he ▸ hc))
            (by intro he; exact Finset.disjoint_left.mp hS.2.2 haI (he.symm ▸ hb)) i
          constructor
          · apply outsideV
            intro hs
            exact havoid.1 ((RubikOBTM.Band.paired_range_iff _ _ _ hadm _).mp hs).1
          · apply outsideV
            intro hs
            exact havoid.2 ((RubikOBTM.Band.paired_range_iff _ _ _ hadm _).mp hs).1
        refine ⟨V ++ U, ?_, ?_, ?_⟩
        · rw [List.length_append, Finset.card_insert_of_notMem ha]
          nlinarith
        · intro c hc b hb
          dsimp only [RubikOBTMCompiler.NativeActsPair]
          rw [RubikOBTM.Band.wordPerm_append]
          rcases Finset.mem_insert.mp hc with he | hc
          · subst c
            have hv := actV b ((hdata.1 b).mp hb)
            constructor
            · intro i
              change RubikOBTM.Band.wordPerm U (RubikOBTM.Band.wordPerm V (RubikOBTM.Band.plus a b i)) = _
              rw [(hv i).1]
              exact (skipU b hb ((σ a).val i)).1
            · intro i
              change RubikOBTM.Band.wordPerm U (RubikOBTM.Band.wordPerm V (RubikOBTM.Band.minus a b i)) = _
              rw [(hv i).2]
              exact (skipU b hb ((τ a).val i)).2
          · constructor
            · intro i
              change RubikOBTM.Band.wordPerm U (RubikOBTM.Band.wordPerm V (RubikOBTM.Band.plus c b i)) = _
              rw [(skipV c hc b hb i).1]
              exact (actU c hc b hb).1 i
            · intro i
              change RubikOBTM.Band.wordPerm U (RubikOBTM.Band.wordPerm V (RubikOBTM.Band.minus c b i)) = _
              rw [(skipV c hc b hb i).2]
              exact (actU c hc b hb).2 i
        · intro s hs
          rw [RubikOBTM.Band.wordPerm_append]
          change RubikOBTM.Band.wordPerm U (RubikOBTM.Band.wordPerm V s) = s
          rw [outsideV s (by intro hm; exact hs (hdata.2.2 a haI s hm))]
          apply outsideU
          intro hm
          obtain ⟨r, hr, b, hb, hlabel⟩ := hm
          exact hs ⟨r, hsub hr, b, hb, hlabel⟩
    exact H A hAY
  · have hYe : Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hY
    refine ⟨[], by simp, ?_, ?_⟩
    · simp [hYe]
    · intro s hs; rfl
