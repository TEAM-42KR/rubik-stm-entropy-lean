import RubikSTM.Proofs.WordConstruction.ConjugatedEndpoint
import Mathlib
set_option autoImplicit false

theorem RubikCompiler.conjugatedEndpoint :
    ∀ {G X : Type*} [Group G] [MulAction G X]
  (a : G) (Fs : List G) (x y : X)
  (hraw : Fs.reverse.prod • (a • x) = a • y), (Fs.map (fun F => a⁻¹ * F * a)).reverse.prod • x = y :=
  @proof_RubikCompiler_conjugatedEndpoint
