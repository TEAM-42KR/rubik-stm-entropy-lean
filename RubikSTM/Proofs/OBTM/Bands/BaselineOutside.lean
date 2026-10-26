import RubikSTM.Definitions.Bands.Band
set_option autoImplicit false

theorem proof_RubikBand_baselineOutside {n : ℕ} (q : Rubik.Axis) (Y : Finset (Fin n))
  (s : Rubik.Sticker n) (hs : ¬ RubikBand.Bands Y s) :
  RubikBand.parallelBaseline q Y s = s := by
  have hnone : ∀ b ∈ Y, ¬ RubikBand.Band b s := by
    intro b hb hn
    exact hs ⟨b, hb, hn⟩
  have hp : ∀ ls : List (Fin n), (∀ b ∈ ls, b ∈ Y) →
      ((ls.map (Rubik.sliceQuarter n q)).reverse.prod) s = s := by
    intro ls
    induction ls with
    | nil => intro hls; rfl
    | cons l ls ih =>
      intro hls
      have hl : Rubik.coordinate s.val.1 q ≠ l := by
        intro he
        exact hnone l (hls l (by simp)) ⟨q, Or.inl he⟩
      have hf : Rubik.sliceQuarter n q l s = s := by simp [Rubik.sliceQuarter, hl]
      simpa only [List.map_cons, List.reverse_cons, List.prod_append,
        List.prod_singleton, Equiv.Perm.mul_apply, hf] using
        ih (fun b hb => hls b (by simp [hb]))
  exact hp _ (by intro b hb; simpa using hb)

#print axioms proof_RubikBand_baselineOutside
