# Scalar stochastic heat equation in Lean

This repository proves Theorems 1.1 and 1.2 of Yi Han's manuscript on weak well-posedness of the stochastic heat equation. The results concern weak mild solutions on the unit torus with normalized Haar measure and heat generator `∂ₓ²`. Each theorem proves existence and uniqueness of the law on the space of continuous real `L²` paths over a fixed finite horizon.

| Result | Lean declaration | Initial condition and coefficients |
| --- | --- | --- |
| Theorem 1.1 | `SHEStochastic.ScalarManuscriptTheorems.theorem_1_1` | Deterministic `L²` data and bounded, uniformly nondegenerate diffusion of any positive global Hölder order |
| Theorem 1.2(i) | `SHEStochastic.ScalarManuscriptTheorems.theorem_1_2_i` | Deterministic `L²` data, the same diffusion assumptions, and Borel drift with horizon-local linear growth |
| Theorem 1.2(ii) | `SHEStochastic.ScalarManuscriptTheorems.theorem_1_2_ii` | Deterministic `L∞` data, uniformly nondegenerate and possibly unbounded diffusion of global Hölder order `0 < β ≤ 1`, and the same drift class |
| Lipschitz endpoint | `SHEStochastic.ScalarManuscriptTheorems.theorem_1_2_ii_lipschitz` | The preceding drift and Lipschitz diffusion, with deterministic `L²` data |

The drifted results use the full Fourier mild equation. The proof formalizes the Girsanov changes of measure in both directions, along the physical state exits, and identifies the stopped formulation with the full equation.

## Build

Use Elan and run the following commands at the repository root. The first command is optional and downloads the prebuilt Mathlib cache.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The toolchain is Lean `v4.35.0`. The Lake manifest pins Mathlib to `56a005855ea17e0b0958f73ec801ae140b0a1679`. The repository includes the project-local import closure for the scalar proofs. Files with vector or matrix terminology provide shared infrastructure used by the scalar theorems.

Use `import ScalarSHE` to access the four entry points. The audit prints the axioms of these declarations and the equivalence to the stopped formulation. The results use `propext`, `Classical.choice`, and `Quot.sound`. The included `licenses/` directory contains the notices from the bundled foundational libraries.
