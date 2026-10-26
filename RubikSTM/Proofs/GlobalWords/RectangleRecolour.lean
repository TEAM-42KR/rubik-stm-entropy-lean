import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Lemmas.Rectangles.CompileRectangle
import RubikSTM.Lemmas.Payloads.PairedPayload
set_option autoImplicit false

open RubikRectangle RubikPayload

theorem proof_RubikGlobalWord_rectangle_recolour : ∃ C : ℕ, ∀ (n : ℕ) (A Y : Finset (Fin n)), Admissible A Y →
    ∀ (k L M : ℕ), 0 < k → 0 < L → 4 ∣ L →
    ∀ Book : RubikCodebook.Book RubikChannel.Paired.Letter k L,
      RubikCodebook.CoversAll RubikChannel.Paired.act Book →
      (∀ i : Fin L, (Book i).card ≤ M) → ∀ c d : Rubik.Position n,
    ∃ w : List (Rubik.Move n),
      w.length ≤ L * (rowCeil A.card k + 3) * (Y.card + C * (k + 1) * M) ∧
      RubikGlobalWord.Recolour {s | Rectangles A Y s} c.val d.val w := by
  obtain ⟨C,hC⟩ := RubikPayload.pairedPayload
  refine ⟨C,?_⟩
  intro n A Y hAY k L M hk hLpos hL Book hBook hM c d
  exact RubikRectangle.compile_rectangle C (fun {n} A Y => hC n A Y) A Y hAY
    k L M hk hL Book hBook hM c d

#print axioms proof_RubikGlobalWord_rectangle_recolour
