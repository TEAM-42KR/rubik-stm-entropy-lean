import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.Channel.Paired.P
set_option autoImplicit false
open Rubik RubikGeometry
private theorem RubikGeometry.card_normalTable_orbit :
    Nat.card {f : Fin 24 → Normal // ∃ σ : Equiv.Perm (Fin 24), f = normalTable ∘ σ} =
      orbitColourings := by
  classical
  let G := DomMulAct (Equiv.Perm (Fin 24))
  have heq : {f : Fin 24 → Normal | ∃ σ : Equiv.Perm (Fin 24), f = normalTable ∘ σ} =
      MulAction.orbit G normalTable := by
    ext f
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨DomMulAct.mk σ, rfl⟩
    · rintro ⟨σ, hσ⟩
      exact ⟨DomMulAct.mk.symm σ, hσ.symm⟩
  have hfib : ∀ c : Normal, Fintype.card {i : Fin 24 // normalTable i = c} = 4 := by
    decide
  have hstab : Nat.card (MulAction.stabilizer G normalTable) = (Nat.factorial 4) ^ 6 := by
    calc
      _ = Nat.card {g : Equiv.Perm (Fin 24) // normalTable ∘ g = normalTable} :=
        Nat.card_congr (Equiv.subtypeEquiv DomMulAct.mk.symm (fun _ => Iff.rfl))
      _ = ∏ c : Normal, (Fintype.card {i : Fin 24 // normalTable i = c}).factorial := by
        rw [Nat.card_eq_fintype_card, DomMulAct.stabilizer_card]
      _ = (Nat.factorial 4) ^ 6 := by simp [hfib, Rubik.Normal]
  have hG : Nat.card G = Nat.factorial 24 := by
    rw [Nat.card_congr DomMulAct.mk.symm, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
  have hos := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G normalTable)
  rw [Nat.card_prod, hstab, hG] at hos
  calc
    _ = Nat.card (MulAction.orbit G normalTable) := Nat.card_congr (Equiv.setCongr heq)
    _ = orbitColourings := by
      unfold orbitColourings
      exact Nat.eq_div_of_mul_eq_right (by positivity) (by simpa [Nat.mul_comm] using hos)

private theorem RubikChannel.Paired.StateCard :
    Fintype.card RubikChannel.Paired.State = RubikGeometry.orbitColourings ^ 2 := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (RubikChannel.Colour.Orbit RubikGeometry.normalTable ×
    RubikChannel.Colour.Orbit RubikGeometry.normalTable) = RubikGeometry.orbitColourings ^ 2
  rw [Nat.card_prod]
  change Nat.card {f : Fin 24 → Rubik.Normal // ∃ σ : Equiv.Perm (Fin 24),
    f = RubikGeometry.normalTable ∘ σ} *
    Nat.card {f : Fin 24 → Rubik.Normal // ∃ σ : Equiv.Perm (Fin 24),
    f = RubikGeometry.normalTable ∘ σ} = RubikGeometry.orbitColourings ^ 2
  rw [RubikGeometry.card_normalTable_orbit, pow_two]

theorem proof_RubikChannel_Paired_log_card_div_eight :
    Real.log (Fintype.card RubikChannel.Paired.State : ℝ) / 8 = Rubik.entropyConstant := by
  have hq : (RubikGeometry.orbitColourings : ℝ) =
      (Nat.factorial 24 : ℝ) / (Nat.factorial 4 : ℝ) ^ 6 := by
    norm_num [RubikGeometry.orbitColourings, Nat.factorial]
  rw [RubikChannel.Paired.StateCard, Nat.cast_pow, Real.log_pow, hq]
  unfold Rubik.entropyConstant
  ring
