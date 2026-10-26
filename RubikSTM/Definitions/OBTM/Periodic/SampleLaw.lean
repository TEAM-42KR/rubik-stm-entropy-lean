import RubikSTM.Definitions.FiniteProbability.ProductLaw
import RubikSTM.Definitions.Overlap.OverlapGraph
set_option autoImplicit false

noncomputable section
open scoped Classical

namespace RubikOBTM.Periodic

def phase (T : ℕ) (hT : 0 < T) {L : ℕ} (i : Fin L) : Fin T :=
  ⟨i.val % T, Nat.mod_lt _ hT⟩

abbrev Native {T : ℕ} (K : Fin T → Type*) [∀ p, Group (K p)]
    (C : ∀ p, Finset (K p)) (p : Fin T) := {c : K p // c ∈ C p}

abbrev Profile {T : ℕ} (hT : 0 < T) (K : Fin T → Type*) (k L : ℕ) :=
  ∀ i : Fin L, Fin k → K (phase T hT i)

abbrev Word {T : ℕ} (hT : 0 < T) (K : Fin T → Type*) [∀ p, Group (K p)]
    (C : ∀ p, Finset (K p)) (k L : ℕ) :=
  ∀ i : Fin L, Fin k → Native K C (phase T hT i)

abbrev Book {T : ℕ} (hT : 0 < T) (K : Fin T → Type*) [∀ p, Group (K p)]
    (C : ∀ p, Finset (K p)) (k L : ℕ) :=
  ∀ i : Fin L, Finset (Fin k → Native K C (phase T hT i))

abbrev Sample {T : ℕ} (hT : 0 < T) (K : Fin T → Type*) [∀ p, Group (K p)]
    (C : ∀ p, Finset (K p)) (k L M : ℕ) :=
  ∀ i : Fin L, Fin M → Fin k → Native K C (phase T hT i)

def eval {T : ℕ} {Z : Type*} (hT : 0 < T) (K : Fin T → Type*)
    [∀ p, Group (K p)] (C : ∀ p, Finset (K p))
    (act : ∀ p, K p →* Equiv.Perm Z) {k L : ℕ}
    (n : Profile hT K k L) (w : Word hT K C k L) (x : Fin k → Z) : Fin k → Z :=
  fun z => (List.ofFn (fun i : Fin L => act (phase T hT i) (n i z * (w i z).val))).foldl
    (fun s σ => σ s) (x z)

def CoversPair {T : ℕ} {Z : Type*} (hT : 0 < T) (K : Fin T → Type*)
    [∀ p, Group (K p)] (C : ∀ p, Finset (K p))
    (act : ∀ p, K p →* Equiv.Perm Z) {k L : ℕ}
    (A : Book hT K C k L) (x y : Fin k → Z) (n : Profile hT K k L) : Prop :=
  ∃ w : Word hT K C k L, (∀ i, w i ∈ A i) ∧ eval hT K C act n w x = y

def CoversAll {T : ℕ} {Z : Type*} (hT : 0 < T) (K : Fin T → Type*)
    [∀ p, Group (K p)] (C : ∀ p, Finset (K p))
    (act : ∀ p, K p →* Equiv.Perm Z) {k L : ℕ}
    (A : Book hT K C k L) : Prop :=
  ∀ x y : Fin k → Z, ∀ n : Profile hT K k L, CoversPair hT K C act A x y n

def sampleBook {T : ℕ} (hT : 0 < T) (K : Fin T → Type*) [∀ p, Group (K p)]
    (C : ∀ p, Finset (K p)) {k L M : ℕ} (W : Sample hT K C k L M) :
    Book hT K C k L := fun i => Finset.univ.image (fun u : Fin M => W i u)

def endpointEvent {T : ℕ} {Z : Type*} (hT : 0 < T) (K : Fin T → Type*)
    [∀ p, Group (K p)] (C : ∀ p, Finset (K p))
    (act : ∀ p, K p →* Equiv.Perm Z) {k L M : ℕ}
    (a : Fin L → Fin M) (x y : Fin k → Z) (n : Profile hT K k L)
    (W : Sample hT K C k L M) : Prop :=
  eval hT K C act n (fun i => W i (a i)) x = y

def pathIndicator {T : ℕ} {Z : Type*} (hT : 0 < T) (K : Fin T → Type*)
    [∀ p, Group (K p)] (C : ∀ p, Finset (K p))
    (act : ∀ p, K p →* Equiv.Perm Z) {k L M : ℕ}
    (x y : Fin k → Z) (n : Profile hT K k L) :
    (Fin L → Fin M) → Sample hT K C k L M → ℝ :=
  fun a W => if endpointEvent hT K C act a x y n W then 1 else 0

def sampleLaw {T : ℕ} (hT : 0 < T) (K : Fin T → Type*) [∀ p, Group (K p)]
    (C : ∀ p, Finset (K p)) (hC : ∀ p, (C p).Nonempty) (k L M : ℕ) :
    RubikJanson.FiniteLaw (Sample hT K C k L M) := by
  haveI : ∀ p : Fin T, Nonempty (Native K C p) := fun p => (hC p).to_subtype
  exact RubikJanson.uniformLaw inferInstance

end RubikOBTM.Periodic
