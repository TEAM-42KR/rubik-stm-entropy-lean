import Mathlib
set_option autoImplicit false

namespace RubikOBTMCompiler

abbrev Profile (L : ℕ) (K : Fin L → Type*) := (i : Fin L) → K i

def phasePerm {L : ℕ} {K : Fin L → Type*} {X : Type*}
    (act : (i : Fin L) → K i → Equiv.Perm X) (p : Profile L K) : Equiv.Perm X :=
  (List.ofFn (fun i => act i (p i))).reverse.prod

def UniversalOwnProfile {L : ℕ} {K : Fin L → Type*} [∀ i, Group (K i)] {X : Type*}
    (act : (i : Fin L) → K i → Equiv.Perm X) (A : (i : Fin L) → Finset (K i)) : Prop :=
  ∀ (x y : X) (n : Profile L K), ∃ w : Profile L K,
    (∀ i, w i ∈ A i) ∧ phasePerm act (fun i => n i * w i) x = y

def suffix {L s : ℕ} {K : Fin L → Type*} [∀ i, Monoid (K i)]
    (w : Fin s → Profile L K) (b : ℕ) (i : Fin L) : K i :=
  ((List.ofFn (fun d => w d i)).drop b).prod

def cuts {s : ℕ} {K : Type*} [DecidableEq K] (w : Fin s → K) (a : K) : Finset (Fin s) :=
  Finset.univ.filter (fun d => w d = a)

def oddPad (r : ℕ) : ℕ := (r+1)%2
end RubikOBTMCompiler
