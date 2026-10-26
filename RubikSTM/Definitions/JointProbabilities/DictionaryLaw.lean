import RubikSTM.Definitions.Channel.ArrayLaw
import RubikSTM.Definitions.Codebook.Conditional.SampleEquiv
set_option autoImplicit false

noncomputable section
open scoped Classical

namespace RubikJoint

def sharedCount {L M : ℕ} (a b : Fin L → Fin M) : ℕ :=
  (Finset.univ.filter (fun i => a i = b i)).card

def sharedMask {C : Type*} {k L M : ℕ} (a b : Fin L → Fin M)
    (s : {i : Fin L // a i = b i} → Fin k → C) : Fin L → Fin k → Option C :=
  fun i j => if h : a i = b i then some (s ⟨i, h⟩ j) else none

def dictionaryLaw {C : Type*} [Fintype C] [Nonempty C] (k L M : ℕ) :
    RubikJanson.FiniteLaw ((Fin L × Fin M) → Fin k → C) :=
  RubikJanson.uniformLaw (inferInstance : Nonempty ((Fin L × Fin M) → Fin k → C))

def endpointEvent {C X : Type*} (act : C → Equiv.Perm X) {k L M : ℕ}
    (path : Fin L → Fin M) (x y : Fin k → X)
    (W : (Fin L × Fin M) → Fin k → C) : Prop :=
  RubikCodebook.eval act (fun i => W (i, path i)) x = y

end RubikJoint
