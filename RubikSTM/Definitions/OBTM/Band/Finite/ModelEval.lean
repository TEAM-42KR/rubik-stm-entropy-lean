import RubikSTM.Definitions.OBTM.Band.SlabWord
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.FreeGroup.Reduce
set_option autoImplicit false

namespace RubikOBTM.Band.Finite

abbrev Alphabet := Perm × Perm
abbrev Token := Alphabet × Bool
abbrev EvenPair := alternatingGroup Label × alternatingGroup Label

def conj (σ : Perm) : PairPerm :=
  (σ * actualSlabPlus * σ⁻¹, σ * actualSlabMinus * σ⁻¹)

def kernel (a : Alphabet) : PairPerm := conj a.1 * (conj a.2)⁻¹

def modelEval : FreeGroup Alphabet →* PairPerm := FreeGroup.lift kernel

def tokenValue (t : Token) : PairPerm := if t.2 then kernel t.1 else (kernel t.1)⁻¹

def signedEval (w : List Token) : PairPerm := (w.map tokenValue).prod

end RubikOBTM.Band.Finite
