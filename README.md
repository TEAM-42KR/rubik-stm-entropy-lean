# Entropy-sharp diameters and solved-state worst cases of the n x n x n Rubik's Cube

Version 1.2.0.

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

## Scope of version 1.2.0

Version 1.2.0 adds four solved-state limit theorems. It preserves the two existing
arbitrary-pair diameter theorems and every definition already present in version
1.1.0.

For each metric on the **same** vertex type `Rubik.Position n`:

- `solvedRadius n` is the maximum graph distance from a reachable position to the
  fixed-frame solved colouring `Rubik.solved n` (its eccentricity, denoted R).
  It is **not** Mathlib's `SimpleGraph.radius`, which minimizes eccentricity over
  all vertices.
- `solvedLookingRadius n` is the maximum, over reachable positions, of the minimum
  distance to a reachable position with every spatial face monochromatic
  (denoted R*). No particular face-colour assignment is prescribed. This is the
  solved-looking convention, including whole-cube orientations of solved.

The STM functions are in `Rubik`; the proper-OBTM functions are in `RubikOBTM`.
Their `normalizedSolvedRadius` and `normalizedSolvedLookingRadius` multiply the
respective natural-valued quantity by `Real.log (n : ℝ) / (n : ℝ)^2`.
The additive definitions are in `RubikSTM/Definitions/Solved/`.

`RubikSTM/SolvedRadii.lean` exports these four unconditional heads:

```lean
theorem RubikSTM.rubik_stm_solved_radius_entropy :
    Filter.Tendsto Rubik.normalizedSolvedRadius Filter.atTop (nhds Rubik.entropyConstant)
theorem RubikSTM.rubik_stm_solved_looking_radius_entropy :
    Filter.Tendsto Rubik.normalizedSolvedLookingRadius Filter.atTop (nhds Rubik.entropyConstant)
theorem RubikSTM.rubik_obtm_solved_radius_entropy :
    Filter.Tendsto RubikOBTM.normalizedSolvedRadius Filter.atTop (nhds Rubik.entropyConstant)
theorem RubikSTM.rubik_obtm_solved_looking_radius_entropy :
    Filter.Tendsto RubikOBTM.normalizedSolvedLookingRadius Filter.atTop (nhds Rubik.entropyConstant)
```

`Main.lean` also exports the four names without the `RubikSTM.` prefix. The proof
counts balls around at most `6^6` face-monochromatic colourings; this constant
factor does not affect the entropy lower bound. The upper bound follows from
R* <= R <= the corresponding arbitrary-pair diameter. Positions are never
quotiented by rotations, and neither move metric is changed.

The paper and its Zenodo record remain **version 1.1**:
https://doi.org/10.5281/zenodo.23658175. That record includes code version 1.1.0;
**it does not archive code version 1.2.0**. Version 1.2.0 is this GitHub software
release only; no new Zenodo deposit accompanies it. The paper is unchanged.

## Build

Install Lean through elan, then run from the repository root:

```sh
lake exe cache get && lake build && lake env lean Check.lean
```

Lean is pinned to `v4.33.1` and Mathlib to commit
`0df444a360eaa60ab8c11dca51a86af692955474`. The dependency manifest fixes the
remaining packages. Keep these pins when rebuilding.

`AxiomCheck.lean` is part of the default build. It checks that all six theorems and their
six `Main.lean` aliases use only `propext`, `Classical.choice` and `Quot.sound`, and rejects any
declaration in the library that directly uses `sorryAx`. `Check.lean` prints the
theorem types and their axioms. The Lean kernel, the stated definitions and the
pinned dependencies are the trust boundary; downloading the Mathlib cache also
trusts those prebuilt files.

The library is organised into definitions, lemmas and proofs, with subdirectories
for geometry, permutation actions, probability, word construction, asymptotics,
and the outer-block-turn metric (`OBTM`).

Paper and supplementary material, version 1.1 (not the v1.2.0 code archive):
https://doi.org/10.5281/zenodo.23658175

## Author and licence

Sungsoo Na, TEAM42 Inc., Seoul, Republic of Korea. ORCID: 0009-0005-5257-3374.

MIT licence; see `LICENSE`. Citation information is in `CITATION.cff`.

Assisted by AI.
