import RubikSTM.Definitions.OBTM.Compiler.NativeCoalescedWord
set_option autoImplicit false

namespace RubikOBTMCompiler

structure NativePhaseModel {n L r s : ℕ} {K : Fin L → Type*}
    [∀ i, CommGroup (K i)] {X : Type*}
    (act : (i : Fin L) → K i → Equiv.Perm X) (A : (i : Fin L) → Finset (K i))
    (a : Rubik.Axis) (side : Bool) (lower : Fin (n-1)) (upper : Fin s → Fin (n-1))
    (k C : ℕ) where
  view : Rubik.Colouring n → Fin r → Fin s → X
  frame : Fin r → Equiv.Perm X
  outside : Set (Rubik.Sticker n)
  outside_inv : ∀ x∈outside,
    slabBaseline a side lower (List.ofFn upper) x ∈ outside
  word : (i : Fin L) → (Fin r → Fin s → K i) → List (RubikOBTM.BlockMove n)
  cost : ∀ i w, (∀ j d, w j d ∈ A i) →
    (word i w).length ≤ (r+oddPad r)*(s+C*(k+1)*(A i).card)
  cell_action : ∀ i w, (∀ j d, w j d ∈ A i) → ∀ c : Rubik.Colouring n,
    ∀ j : Fin r, ∀ b : Fin s,
    view (RubikOBTM.applyBlockWord (word i w) c) j b =
      ((frame j)⁻¹ * act i (((List.ofFn (w j)).drop b.val).prod) * frame j) (view c j b)
  outside_action : ∀ i w, (∀ j d, w j d ∈ A i) → ∀ x∈outside,
    RubikOBTM.Band.wordPerm (word i w) x =
      (slabBaseline a side lower (List.ofFn upper) ^ (r+oddPad r)) x
end RubikOBTMCompiler
