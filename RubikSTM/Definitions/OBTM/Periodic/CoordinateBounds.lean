import RubikSTM.Definitions.OBTM.Periodic.UniformMomentBounds
import RubikSTM.Definitions.Channel.ArrayLaw
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace RubikOBTM.Periodic

abbrev NativeConstant {K : Type*} [Group K] (C : Finset K) := {c : K // c ∈ C}

def coordinateRun {T : ℕ} {K Z : Type*} [Group K] (hT : 0 < T) (C : Finset K)
    (act : Fin T → K →* Equiv.Perm Z) {L : ℕ}
    (n : Fin L → K) (w : Fin L → NativeConstant C) (x : Z) : Z :=
  RubikChannel.run (fun i c => act (phase T hT i) (n i * c.val)) w x

def coordinateProb {T : ℕ} {K Z : Type*} [Group K] (hT : 0 < T) (C : Finset K)
    (hC : C.Nonempty) (act : Fin T → K →* Equiv.Perm Z) {L : ℕ}
    (n : Fin L → K) (x y : Z) : ℝ := by
  haveI : Nonempty (NativeConstant C) := hC.to_subtype
  exact (RubikJanson.uniformLaw (inferInstance : Nonempty (Fin L → NativeConstant C))).prob
    (fun w => coordinateRun hT C act n w x = y)

def coordinateJointProb {T : ℕ} {K Z : Type*} [Group K] (hT : 0 < T)
    (C : Finset K) (hC : C.Nonempty) (act : Fin T → K →* Equiv.Perm Z) {L : ℕ}
    (n : Fin L → K) (shared : Fin L → Bool) (x y : Z) : ℝ := by
  haveI : Nonempty (NativeConstant C) := hC.to_subtype
  exact (RubikJanson.uniformLaw
    (inferInstance : Nonempty (Fin L → NativeConstant C × NativeConstant C))).prob
      (fun w => coordinateRun hT C act n (fun i => (w i).1) x = y ∧
        coordinateRun hT C act n (fun i => if shared i then (w i).1 else (w i).2) x = y)

def CoordinateBounds {T : ℕ} {K Z : Type*} [Group K] [Fintype Z]
    (hT : 0 < T) (C : Finset K) (hC : C.Nonempty)
    (act : Fin T → K →* Equiv.Perm Z) (θ ρ : ℝ) : Prop :=
  ∀ L : ℕ, 0 < L → T ∣ L → ∀ n : Fin L → K, ∀ x y : Z,
    lowerEnvelope (Fintype.card Z) θ L T ≤ coordinateProb hT C hC act n x y ∧
      ∀ shared : Fin L → Bool, coordinateJointProb hT C hC act n shared x y ≤
        1 / (Fintype.card Z : ℝ) ^ 2 +
          ρ ^ (Finset.univ.filter (fun i => shared i = false)).card

end RubikOBTM.Periodic
