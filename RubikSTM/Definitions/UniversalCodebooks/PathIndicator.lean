import RubikSTM.Definitions.JointProbabilities.DictionaryLaw
import RubikSTM.Definitions.Overlap.OverlapGraph
set_option autoImplicit false

noncomputable section
open scoped Classical
namespace RubikUniversal

abbrev Sample (Letter : Type*) (k L M : ℕ) := (Fin L × Fin M) → Fin k → Letter

def sampleBook {Letter : Type*} {k L M : ℕ} (W : Sample Letter k L M) :
    RubikCodebook.Book Letter k L :=
  fun i => Finset.univ.image (fun t : Fin M => W (i, t))

def pathIndicator {Letter State : Type*} (act : Letter → Equiv.Perm State)
    {k L M : ℕ} (x y : Fin k → State) :
    (Fin L → Fin M) → Sample Letter k L M → ℝ :=
  fun a W => if RubikJoint.endpointEvent act a x y W then 1 else 0

end RubikUniversal
