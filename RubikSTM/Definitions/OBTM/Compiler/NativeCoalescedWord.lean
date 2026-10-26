import RubikSTM.Definitions.OBTM.Band.CleanAction
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false
namespace RubikOBTMCompiler

def halfPrefix {n : ℕ} (a : Rubik.Axis) (side : Bool) (b : Fin (n-1)) : RubikOBTM.BlockMove n :=
  (a,side,b,1)

def nativeCoalescedWord {n : ℕ} (a : Rubik.Axis) (side : Bool) (lower : Fin (n-1))
    (B : List (Fin (n-1))) : List (RubikOBTM.BlockMove n) :=
  (if B.length%2=0 then [] else [halfPrefix a side lower]) ++ B.map (halfPrefix a side)

def slabBaseline {n : ℕ} (a : Rubik.Axis) (side : Bool) (lower : Fin (n-1))
    (B : List (Fin (n-1))) : Equiv.Perm (Rubik.Sticker n) :=
  (B.map (fun b => (RubikOBTM.blockQuarter n a side b *
    (RubikOBTM.blockQuarter n a side lower)⁻¹)^2)).reverse.prod
end RubikOBTMCompiler
