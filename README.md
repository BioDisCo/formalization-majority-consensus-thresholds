# Formalization of Majority Consensus Thresholds

This repository contains the Lean 4 formalization accompanying the paper
“Majority Consensus Thresholds in Competitive Lotka–Volterra Populations”
by Matthias Függer, Thomas Nowak, and Joel Rybicki.

## Paper-facing results

Each verified badge in the paper links directly to one file in
[`LVConsensus/Paper`](LVConsensus/Paper). These files state the
paper-facing declarations and identify the proof declarations on which
they depend.

## Verification

The Lean and Mathlib versions are pinned by `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`. From the repository root, run:

```sh
lake build
./check_sorry.sh
```

The second command checks the source tree for `sorry` and custom axioms,
builds the project, and runs `AxiomProbe.lean`. The axiom probe checks the
complete dependency graph of every paper-facing verified declaration.

## Structure

- `LVConsensus/Paper/`: one public file for each paper-facing statement
- `LVConsensus/`: definitions, stochastic-process constructions, and proofs
- `AxiomProbe.lean`: transitive axiom audit for verified declarations
- `check_sorry.sh`: reproducible verification command
