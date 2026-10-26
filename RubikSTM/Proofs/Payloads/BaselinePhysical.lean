import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem proof_RubikPayload_baselinePhysical {n : ℕ} (Y : Finset (Fin n)) :
  (RubikPayload.baselineWord Y).length = Y.card ∧
  ∀ s : Rubik.Sticker n, ¬ RubikBand.Bands Y s → RubikPayload.columnBaseline Y s = s := by
  constructor
  · simp [RubikPayload.baselineWord]
  · intro s hs
    have H : ∀ ls : List (Fin n), (∀ b ∈ ls, b ∈ Y) →
        RubikBand.wordPerm (ls.map (fun b => (2,b.rev,0))) s = s := by
      intro ls
      induction ls with
      | nil => intro hls; rfl
      | cons b ls ih =>
        intro hls
        have hcoord : Rubik.coordinate s.val.1 2 ≠ b.rev := by
          intro he
          exact hs ⟨b,hls b (by simp),⟨2,Or.inr he⟩⟩
        have hm : Rubik.movePermutation (2,b.rev,0) s = s := by
          simp [Rubik.movePermutation, Rubik.sliceQuarter, hcoord]
        have ht := ih (fun c hc => hls c (by simp [hc]))
        simpa only [RubikBand.wordPerm, List.map_cons, List.reverse_cons,
          List.prod_append, List.prod_singleton, Equiv.Perm.mul_apply, hm] using ht
    exact H _ (by intro b hb; simpa using hb)

#print axioms proof_RubikPayload_baselinePhysical
