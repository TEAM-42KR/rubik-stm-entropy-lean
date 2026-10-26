# The asymptotic diameter of the n x n x n Rubik's Cube in the slice-turn and outer-block-turn metrics

Version 1.1.0.

Lean 4 formalization of the entropy-sharp asymptotic diameter of the n by n by n
six-colour reachable-sticker position graph in two metrics. In the slice-turn
metric a move turns one slice by 90, 180 or 270 degrees; the outer-block-turn
metric is described below. Same-coloured centres are indistinguishable and the
spatial frame is fixed; positions are not identified under whole-cube rotations.

## The theorem

```lean
theorem RubikSTM.rubik_stm_diameter_entropy :
    Filter.Tendsto Rubik.normalizedDiameter Filter.atTop (nhds Rubik.entropyConstant)
```

Here `Rubik.diameter n` is the arbitrary-pair graph diameter,
`Rubik.normalizedDiameter n = (Rubik.diameter n : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2`,
and the entropy constant is one quarter of the logarithm of `24! / (4!)^6`.
The definitions are in `RubikSTM/Definitions/Geometry/StmGraph.lean`.
The theorem is in `RubikSTM/Diameter.lean`; `Main.lean` also exports the alias
`rubik_stm_diameter_entropy`.

## Outer-block-turn theorem

```lean
theorem RubikSTM.rubik_obtm_diameter_entropy :
    Filter.Tendsto RubikOBTM.normalizedDiameter Filter.atTop (nhds Rubik.entropyConstant)
```

An outer-block turn turns the outermost w layers at one of the six faces, for
some w between 1 and n - 1, by 90, 180 or 270 degrees; whole-cube rotations are
not moves. The definitions are in `RubikSTM/Definitions/OBTM/ObtmGraph.lean`:
`RubikOBTM.obtmDiameter n` is the arbitrary-pair diameter of `RubikOBTM.obtmGraph n`
on the same positions `Rubik.Position n`, and `RubikOBTM.normalizedDiameter` is
normalized as above. The theorem is in `RubikSTM/OBTMDiameter.lean`; `Main.lean`
exports `rubik_obtm_diameter_entropy`. Version 1.1.0 adds this theorem; the
slice-turn declarations and proofs of version 1.0.0 are unchanged.

## Build

Install Lean through elan, then run from the repository root:

```sh
lake exe cache get && lake build && lake env lean Check.lean
```

Lean is pinned to `v4.33.1` and Mathlib to commit
`0df444a360eaa60ab8c11dca51a86af692955474`. The dependency manifest fixes the
remaining packages. Keep these pins when rebuilding.

`AxiomCheck.lean` is part of the default build. It checks that both theorems and their
two `Main.lean` aliases use only `propext`, `Classical.choice` and `Quot.sound`, and rejects any
declaration in the library that directly uses `sorryAx`. `Check.lean` prints the
theorem types and their axioms. The Lean kernel, the stated definitions and the
pinned dependencies are the trust boundary; downloading the Mathlib cache also
trusts those prebuilt files.

The library is organised into definitions, lemmas and proofs, with subdirectories
for geometry, permutation actions, probability, word construction, asymptotics,
and the outer-block-turn metric (`OBTM`).

Paper and supplementary material: https://doi.org/10.5281/zenodo.23658175

## Author and licence

Sungsoo Na, TEAM42 Inc., Seoul, Republic of Korea. ORCID: 0009-0005-5257-3374.

MIT licence; see `LICENSE`. Citation information is in `CITATION.cff`.

Assisted by AI.
