import Mathlib
set_option autoImplicit false

namespace RubikCodebook

abbrev Book (Letter : Type*) (k L : ℕ) := Fin L → Finset (Fin k → Letter)

def eval {Letter State : Type*} {k L : ℕ}
    (act : Letter → Equiv.Perm State) (w : Fin L → Fin k → Letter)
    (x : Fin k → State) : Fin k → State :=
  fun j => (List.ofFn (fun i => w i j)).foldl (fun z c => act c z) (x j)

def CoversPair {Letter State : Type*} {k L : ℕ}
    (act : Letter → Equiv.Perm State) (A : Book Letter k L)
    (x y : Fin k → State) : Prop :=
  ∃ w : Fin L → Fin k → Letter, (∀ i, w i ∈ A i) ∧ eval act w x = y

def CoversAll {Letter State : Type*} {k L : ℕ}
    (act : Letter → Equiv.Perm State) (A : Book Letter k L) : Prop :=
  ∀ x y : Fin k → State, CoversPair act A x y

noncomputable def layerwiseUnion {Letter : Type*} {k L R : ℕ}
    (books : Fin R → Book Letter k L) : Book Letter k L := by
  classical
  exact fun i => Finset.univ.biUnion (fun r => books r i)

end RubikCodebook
