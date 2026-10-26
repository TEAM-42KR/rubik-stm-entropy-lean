import RubikSTM.Proofs.Payloads.BaselineAlphabet
import Mathlib
import RubikSTM.Definitions.Channel.DisjointFourCycleAlphabet
import RubikSTM.Definitions.Orbits.SwapPhi
set_option autoImplicit false

theorem RubikPayload.baselineAlphabet :
    (RubikGeometry.gen7, RubikOrbit.minusB) ∈ RubikChannel.disjointFourCycleAlphabet (Fin 24) :=
  @proof_RubikPayload_baselineAlphabet
