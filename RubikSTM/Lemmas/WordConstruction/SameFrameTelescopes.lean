import RubikSTM.Proofs.WordConstruction.SameFrameTelescopes
import Mathlib
set_option autoImplicit false

theorem RubikCompiler.sameFrameTelescopes :
    ∀ {G : Type*} [Group G] (a : G) (Fs : List G), (Fs.map (fun F => a⁻¹ * F * a)).reverse.prod =
    a⁻¹ * Fs.reverse.prod * a :=
  @proof_RubikCompiler_sameFrameTelescopes
