import RubikSTM.Definitions.OBTM.Global.WordCostEnvelope
import RubikSTM.Definitions.OBTM.Finite.PhaseAct
import RubikSTM.Definitions.OBTM.Periodic.SampleLaw
set_option autoImplicit false
open scoped Classical

def RubikOBTM.Global.Recolour {n : ℕ} (S : Set (Rubik.Sticker n))
    (c d : Rubik.Colouring n) (w : List (RubikOBTM.BlockMove n)) : Prop :=
  (∀ s ∈ S, RubikOBTM.applyBlockWord w c s = d s) ∧
    (∀ s ∉ S, RubikOBTM.applyBlockWord w c s = c s)

def RubikOBTM.Global.RectangleCompiler : Prop :=
  ∃ R : ℕ, ∀ (n : ℕ) (A Y : Finset (Fin n)),
    RubikPayload.Admissible A Y → Set.OrdConnected (Y : Set (Fin n)) →
    ∀ (k L M : ℕ), 0 < k → 0 < L → 4 ∣ L →
    ∀ (hT : 0 < RubikOBTM.Finite.period)
      (B : RubikOBTM.Periodic.Book hT (fun _ => RubikOBTM.Finite.Intrinsic)
        RubikOBTM.Finite.periodicC k L),
      RubikOBTM.Periodic.CoversAll hT (fun _ => RubikOBTM.Finite.Intrinsic)
        RubikOBTM.Finite.periodicC RubikOBTM.Finite.periodicAct B →
      (∀ i : Fin L, (B i).card ≤ M) →
      ∀ c d : Rubik.Position n, ∃ w : List (RubikOBTM.BlockMove n),
        w.length ≤ L * (RubikRectangle.rowCeil A.card k + 3) *
          (Y.card + R * (k + 1) * M) ∧
        RubikOBTM.Global.Recolour {s | RubikPayload.Rectangles A Y s} c.val d.val w

def RubikOBTM.Global.BookSupply : Prop :=
  ∀ η : ℝ, 0 < η → ∃ (L : ℕ) (ρ : ℝ) (K : ℕ),
    0 < L ∧ 4 ∣ L ∧ 0 < ρ ∧
    (L : ℝ) * ρ ≤ Real.log (RubikCostBridge.q ^ 2) + η ∧
    ∀ (hT : 0 < RubikOBTM.Finite.period) (k : ℕ), K ≤ k →
      ∃ B : RubikOBTM.Periodic.Book hT (fun _ => RubikOBTM.Finite.Intrinsic)
          RubikOBTM.Finite.periodicC k L,
        RubikOBTM.Periodic.CoversAll hT (fun _ => RubikOBTM.Finite.Intrinsic)
          RubikOBTM.Finite.periodicC RubikOBTM.Finite.periodicAct B ∧
        ∀ i : Fin L, ((B i).card : ℝ) ≤ Real.exp ((k : ℝ) * ρ)
