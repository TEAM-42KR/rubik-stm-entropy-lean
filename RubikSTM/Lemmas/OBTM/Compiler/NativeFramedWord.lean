import RubikSTM.Proofs.OBTM.Compiler.NativeFramedWord
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.native_framed_word :
    ∀ {n L t : ℕ} {X J D : Type*}
  (read : Rubik.Colouring n → J → D → X) (owner : J → Fin t)
  (B : D → Equiv.Perm X) (hB : ∀ b, B b ^ 2 = 1)
  (F : Fin L → J → D → Equiv.Perm X)
  (ws : Fin L → Fin t → List (RubikOBTM.BlockMove n))
  (hcell : ∀ i j c a b, read (RubikOBTM.applyBlockWord (ws i j) c) a b =
    (if j = owner a then F i a b else B b) (read c a b))
  (Q : Equiv.Perm (Rubik.Sticker n)) (hQ : Q^2=1)
  (S : Set (Rubik.Sticker n)) (hInv : ∀ x∈S, Q x ∈ S)
  (houtside : ∀ i j x, x∈S → RubikOBTM.Band.wordPerm (ws i j) x=Q x)
  (c d : Rubik.Colouring n) (ht : t%2=1) (hL : L%2=0)
  (hraw : ∀ a b, (List.ofFn (fun i => F i a b)).reverse.prod
    ((B b ^ ((owner a).val%2)) (read c a b)) =
      (B b ^ ((owner a).val%2)) (read d a b))
  (cost : ℕ) (hcost : ∀ i j, (ws i j).length ≤ cost), (RubikOBTMCompiler.nativeProgram ws).length ≤ L*t*cost ∧
    (∀ a b, read (RubikOBTM.applyBlockWord (RubikOBTMCompiler.nativeProgram ws) c) a b=read d a b) ∧
    ∀ x∈S, RubikOBTM.Band.wordPerm (RubikOBTMCompiler.nativeProgram ws) x=x :=
  @proof_RubikOBTMCompiler_native_framed_word
