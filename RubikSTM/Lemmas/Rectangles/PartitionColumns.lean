import RubikSTM.Proofs.Rectangles.PartitionColumns
import Mathlib
set_option autoImplicit false
open scoped Classical

theorem RubikRectangle.partition_columns :
    ∀ {n : ℕ} {T : Type*} (D : Finset T) (Y : Finset (Fin n)) (choice : Fin n → T) (hchoice : ∀ b ∈ Y, choice b ∈ D), (D.toList.flatMap (fun f => (Y.filter (fun b => choice b = f)).sort (· ≤ ·))).Perm (Y.sort (· ≤ ·)) :=
  @proof_RubikRectangle_partition_columns
