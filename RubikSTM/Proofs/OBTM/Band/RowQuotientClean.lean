import RubikSTM.Definitions.OBTM.Band.Finite.ModelEval
import RubikSTM.Lemmas.OBTM.Band.SlabActionBoth
import RubikSTM.Lemmas.OBTM.Band.StrictQuotientOutside
set_option autoImplicit false
open Rubik RubikOBTM.Band
set_option maxHeartbeats 1000000

theorem proof_RubikOBTM_Band_row_quotient_clean {n : ℕ} (a u v : Fin n) (h : RubikOBTM.Band.Admissible n a u v) (σ τ : Equiv.Perm (Fin 24)) (ms ns : List (Rubik.Move n)) (hm : RubikBand.StrictControl a ms) (hn : RubikBand.StrictControl a ns) (hσ : ∀ d : Fin n, RubikOBTM.Band.InInterval u v d → ∀ i : Fin 24, (RubikBand.wordPerm ms (RubikOBTM.Band.plus a d i) = RubikOBTM.Band.plus a d (σ i)) ∧ (RubikBand.wordPerm ms (RubikOBTM.Band.minus a d i) = RubikOBTM.Band.minus a d (σ i))) (hτ : ∀ d : Fin n, RubikOBTM.Band.InInterval u v d → ∀ i : Fin 24, (RubikBand.wordPerm ns (RubikOBTM.Band.plus a d i) = RubikOBTM.Band.plus a d (τ i)) ∧ (RubikBand.wordPerm ns (RubikOBTM.Band.minus a d i) = RubikOBTM.Band.minus a d (τ i))) : RubikOBTM.Band.CleanAction a u v (RubikOBTM.Band.Finite.kernel (σ,τ)) ((RubikBand.wordPerm ms * RubikOBTM.Band.slabPerm u v * (RubikBand.wordPerm ms)⁻¹) * (RubikBand.wordPerm ns * RubikOBTM.Band.slabPerm u v * (RubikBand.wordPerm ns)⁻¹)⁻¹)  := by
  have invact (f : Fin 24 → Sticker n) (P : Equiv.Perm (Sticker n)) (ρ : Perm)
      (hp : ∀ j, P (f j) = f (ρ j)) (j : Fin 24) :
      P⁻¹ (f j) = f (ρ⁻¹ j) := by
    apply Equiv.Perm.inv_eq_iff_eq.mpr
    simpa using (hp (ρ⁻¹ j)).symm
  have cact (f : Fin 24 → Sticker n) (P : Equiv.Perm (Sticker n)) (ρ T : Perm)
      (hp : ∀ j, P (f j) = f (ρ j))
      (hb : ∀ j, slabPerm u v (f j) = f (T j)) (j : Fin 24) :
      (P * slabPerm u v * P⁻¹) (f j) = f ((ρ*T*ρ⁻¹) j) := by
    change P (slabPerm u v (P⁻¹ (f j))) = f (ρ (T (ρ⁻¹ j)))
    rw [invact f P ρ hp j,hb (ρ⁻¹ j),hp (T (ρ⁻¹ j))]
  have qact (f : Fin 24 → Sticker n) (P Q : Equiv.Perm (Sticker n)) (ρ T : Perm)
      (hp : ∀ j, P (f j) = f (ρ j)) (hq : ∀ j, Q (f j) = f (T j)) (j : Fin 24) :
      (P*Q⁻¹) (f j) = f ((ρ*T⁻¹) j) := by
    change P (Q⁻¹ (f j)) = f (ρ (T⁻¹ j))
    rw [invact f Q T hq j,hp (T⁻¹ j)]
  constructor
  · intro d hd i
    constructor
    · have cp := cact (plus a d) (RubikBand.wordPerm ms) σ actualSlabPlus
        (fun j => (hσ d hd j).1) (fun j => (slab_action_both a u v h d hd j).1)
      have cq := cact (plus a d) (RubikBand.wordPerm ns) τ actualSlabPlus
        (fun j => (hτ d hd j).1) (fun j => (slab_action_both a u v h d hd j).1)
      simpa [Finite.kernel,Finite.conj] using qact (plus a d) _ _ _ _ cp cq i
    · have cp := cact (minus a d) (RubikBand.wordPerm ms) σ actualSlabMinus
        (fun j => (hσ d hd j).2) (fun j => (slab_action_both a u v h d hd j).2)
      have cq := cact (minus a d) (RubikBand.wordPerm ns) τ actualSlabMinus
        (fun j => (hτ d hd j).2) (fun j => (slab_action_both a u v h d hd j).2)
      simpa [Finite.kernel,Finite.conj] using qact (minus a d) _ _ _ _ cp cq i
  · intro s hs
    exact strict_quotient_outside a u v h ms ns hm hn s hs
