import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

namespace RubikCore
open Rubik

def IsLevel {n : ℕ} (x : Fin n) : Prop :=
  x.val = 0 ∨ x.val = n - 1 ∨ x.rev = x

def IsCore {n : ℕ} (s : Sticker n) : Prop :=
  ∀ a : Axis, IsLevel (coordinate s.val.1 a)

abbrev CoreSticker (n : ℕ) := {s : Sticker n // IsCore s}
abbrev CoreColouring (n : ℕ) := CoreSticker n → Colour

noncomputable instance coreFintype (n : ℕ) : Fintype (CoreSticker n) := Fintype.ofFinite _

def project {n : ℕ} (c : Colouring n) : CoreColouring n := fun s => c s.val

def levelCode {n : ℕ} (x : Fin n) : Fin 3 :=
  if x.val = 0 then 0 else if x.val = n - 1 then 1 else 2

end RubikCore
