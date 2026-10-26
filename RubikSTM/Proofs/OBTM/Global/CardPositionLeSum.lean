import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.BlockMoveCard
import RubikSTM.Lemmas.OBTM.BlockReachable
import RubikSTM.Lemmas.OBTM.DiameterWordCover
import RubikSTM.Lemmas.OBTM.CountingWordCover
set_option autoImplicit false

theorem proof_RubikOBTM_Global_card_position_le_sum {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (Rubik.Position n) ≤
      ∑ j ∈ Finset.range (RubikOBTM.obtmDiameter n + 1), (18 * (n - 1)) ^ j := by
  classical
  let step : Rubik.Position n → RubikOBTM.BlockMove n → Rubik.Position n := fun s m =>
    ⟨RubikOBTM.applyBlock m s.val, RubikOBTM.block_reachable m s.val s.property⟩
  let start : Rubik.Position n := ⟨Rubik.solved n, ⟨[], rfl⟩⟩
  have hval : ∀ (w : List (RubikOBTM.BlockMove n)) (s : Rubik.Position n),
      (w.foldl step s).val = RubikOBTM.applyBlockWord w s.val := by
    intro w
    induction w with
    | nil => intro s; rfl
    | cons m w ih =>
        intro s
        change (w.foldl step (step s m)).val =
          RubikOBTM.applyBlockWord w (RubikOBTM.applyBlock m s.val)
        exact ih (step s m)
  have cover : ∀ s : Rubik.Position n, ∃ w : List (RubikOBTM.BlockMove n),
      w.length ≤ RubikOBTM.obtmDiameter n ∧ w.foldl step start = s := by
    intro s
    obtain ⟨w, hwlen, hw⟩ := RubikOBTM.diameter_word_cover hn s
    refine ⟨w, hwlen, ?_⟩
    apply Subtype.ext
    exact (hval w start).trans hw
  simpa only [RubikOBTM.blockMove_card] using
    (RubikOBTM.CountingWordCover step start (RubikOBTM.obtmDiameter n) cover)
