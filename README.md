# Rubik cube diameter in the slice-turn metric

Version 1.0.0.

Lean 4 formalization of the entropy-sharp asymptotic diameter of the n by n by n
six-colour reachable-sticker position graph. A move turns one slice by 90, 180 or
270 degrees. Same-coloured centres are indistinguishable and the spatial frame
is fixed; positions are not identified under whole-cube rotations.

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

## Build

Install Lean through elan, then run from the repository root:

```sh
lake exe cache get && lake build && lake env lean Check.lean
```

Lean is pinned to `v4.33.1` and Mathlib to commit
`0df444a360eaa60ab8c11dca51a86af692955474`. The dependency manifest fixes the
remaining packages. Keep these pins when rebuilding.

`AxiomCheck.lean` is part of the default build. It checks that both exported
theorems use only `propext`, `Classical.choice` and `Quot.sound`, and rejects any
declaration in the library that directly uses `sorryAx`. `Check.lean` prints the
theorem types and their axioms. The Lean kernel, the stated definitions and the
pinned dependencies are the trust boundary; downloading the Mathlib cache also
trusts those prebuilt files.

The library is organised into definitions, lemmas and proofs, with subdirectories
for geometry, permutation actions, probability, word construction and asymptotics.

Paper and supplementary material: https://doi.org/10.5281/zenodo.23655390

## Author and licence

Sungsoo Na, TEAM42 Inc., Seoul, Republic of Korea. ORCID: 0009-0005-5257-3374.

MIT licence; see `LICENSE`. Citation information is in `CITATION.cff`.

Assisted by AI.
