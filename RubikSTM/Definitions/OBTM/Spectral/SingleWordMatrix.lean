import RubikSTM.Definitions.OBTM.Periodic.CoordinateBounds
import RubikSTM.Definitions.OBTM.Spectral.PhaseKernel
set_option autoImplicit false

noncomputable section
open scoped Classical

namespace RubikOBTM.Spectral
open RubikOBTM.Periodic

def singleWordMatrix {T : ℕ} {K Z : Type*} [Group K] [Fintype Z]
    [DecidableEq Z] (hT : 0 < T) (C : Finset K) (hC : C.Nonempty)
    (act : Fin T → K →* Equiv.Perm Z) {L : ℕ} (n : Fin L → K) : Matrix Z Z ℝ :=
  RubikChannel.wordMatrix (RubikJanson.uniformLaw hC.to_subtype)
    (fun i c => act (phase T hT i) (n i * c.val))

def doubleWordMatrix {T : ℕ} {K Z : Type*} [Group K] [Fintype Z]
    [DecidableEq Z] (hT : 0 < T) (C : Finset K) (hC : C.Nonempty)
    (act : Fin T → K →* Equiv.Perm Z) {L : ℕ}
    (n : Fin L → K) (shared : Fin L → Bool) : Matrix (Z × Z) (Z × Z) ℝ := by
  haveI : Nonempty (NativeConstant C) := hC.to_subtype
  exact RubikChannel.wordMatrix
    (RubikJanson.uniformLaw (inferInstance : Nonempty (NativeConstant C × NativeConstant C)))
    (fun i c => (act (phase T hT i) (n i * c.1.val)).prodCongr
      (act (phase T hT i) (n i * (if shared i then c.1 else c.2).val)))

end RubikOBTM.Spectral
