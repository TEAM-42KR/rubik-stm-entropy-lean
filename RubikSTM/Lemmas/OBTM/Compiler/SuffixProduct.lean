import RubikSTM.Proofs.OBTM.Compiler.SuffixProduct
import Mathlib
set_option autoImplicit false

theorem RubikOBTMCompiler.suffix_product :
    ∀ {s : ℕ} {K : Type*} [CommMonoid K]
  (w : Fin s → K) (b : ℕ), ((List.ofFn w).drop b).prod =
    ∏ d ∈ (Finset.univ.filter (fun d : Fin s => b ≤ d.val)), w d :=
  @proof_RubikOBTMCompiler_suffix_product
