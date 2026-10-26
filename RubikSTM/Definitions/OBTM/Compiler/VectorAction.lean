import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
import RubikSTM.Definitions.OBTM.Periodic.SampleLaw
set_option autoImplicit false

namespace RubikOBTMCompiler

def coordinatePerm {k : ℕ} {Z : Type*} (f : Fin k → Equiv.Perm Z) : Equiv.Perm (Fin k → Z) where
  toFun x := fun z => f z (x z)
  invFun x := fun z => (f z)⁻¹ (x z)
  left_inv x := by funext z; simp
  right_inv x := by funext z; simp

def vectorAction {k : ℕ} {K Z : Type*} [Group K] (act : K →* Equiv.Perm Z) :
    (Fin k → K) →* Equiv.Perm (Fin k → Z) where
  toFun g := coordinatePerm (fun z => act (g z))
  map_one' := by ext x z; simp [coordinatePerm]
  map_mul' g h := by ext x z; simp [coordinatePerm,map_mul]

noncomputable def liftedBook {T k L : ℕ} (hT : 0 < T) (K : Fin T → Type*)
    [∀ p, Group (K p)] (C : ∀ p, Finset (K p))
    (B : RubikOBTM.Periodic.Book hT K C k L) :
    (i : Fin L) → Finset (Fin k → K (RubikOBTM.Periodic.phase T hT i)) := by
  classical
  exact fun i => (B i).image (fun w z => (w z).val)
end RubikOBTMCompiler
