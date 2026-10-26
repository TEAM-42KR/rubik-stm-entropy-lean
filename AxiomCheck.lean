import RubikSTM.OBTMDiameter
import RubikSTM.Diameter
import Main
import Lean

open Lean Elab Command

elab "#check_axioms" : command => do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let expected : List Name := []

  let heads : List (Name × Bool) := [(``RubikSTM.rubik_stm_diameter_entropy, false),
    (``rubik_stm_diameter_entropy, false),
    (``RubikSTM.rubik_obtm_diameter_entropy, false),
    (``rubik_obtm_diameter_entropy, false)]
  for (h, allowSorry) in heads do
    let axs := (← liftCoreM <| Lean.collectAxioms h).toList
    logInfo m!"Axioms {h}: {axs}"
    for a in axs do
      unless std.contains a || (allowSorry && a == ``sorryAx) do
        logError m!"Unexpected axiom for {h}: {a}"
  let mods := env.header.moduleNames
  let direct := env.constants.map₁.fold (init := (#[] : Array Name)) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some idx =>
      if (mods[idx.toNat]!.getRoot == `RubikSTM || false) && ci.getUsedConstantsAsSet.contains ``sorryAx then
        acc.push n
      else acc
    | none => acc
  let found := (direct.qsort Name.lt).toList
  let want := (expected.toArray.qsort Name.lt).toList
  logInfo m!"Direct sorryAx users: {found}"
  unless found == want do
    logError m!"Unexpected sorryAx users: found {found}, expected {want}"

#check_axioms
