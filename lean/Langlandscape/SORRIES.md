# SORRIES — every `sorry` in `lean/Langlandscape/`

Edited by the stage master only (OVERVIEW §3.6, `agents/rules/lean.md`). `sorry` is allowed on `impl/*` branches for
declared stubs only; on `wip-implementation` every one is listed here; on `main` none in `Langlandscape/`.

| file:line | declaration | WP | owner | reason | planned discharge |
|---|---|---|---|---|---|

(none in `lean/Langlandscape/Langlandscape/`; S01-X1a, 2026-11-14)

## Import `sorry`s (not in `Langlandscape`'s import cone, not part of its audit)

The import `lean/trace-formula-project-import/lean/` contains two `sorry`s. They are outside the import cone of the library
`Langlandscape` (which imports only the narrow `AlgJL.*` modules it uses, e.g. `AlgJL.Hyp.EichlerMass`), so
`Audit/PrintAxioms.lean` over `Langlandscape` is unaffected. **But** the test library imports one of the two modules:
`LanglandscapeTests/S01/CentralSimple.lean` and `LanglandscapeTests/S01/LocalComponent.lean` import `AlgJL.VolIII.P2.Instances`,
so building `LanglandscapeTests` compiles a module that contains a `sorry` (a `declaration uses sorry` warning, only for the
import declaration; nothing in `LanglandscapeTests` depends on it).

| file:line (declaration at / `sorry` at) | declaration | owner | reason |
|---|---|---|---|
| `lean/trace-formula-project-import/lean/AlgJL/VolIII/P2/Instances.lean`: 1815 / 1832 | `GL2TF.Quat.eichler_mass_instances_small` | import | closed instances of the Eichler mass hypothesis for small `D`; not proved in the import; imported (indirectly) by two test files |
| `lean/trace-formula-project-import/lean/AlgJL/VolIII/Brandt/BrandtInstances.lean`: 783 / 794 | `GL2TF.Quat.hecke_d11_weight4` | import | `T_2` on `M_4(O_11)`: trace 2, determinant -2; "not yet formalized (Part 6 notes)"; not imported by `Langlandscape` or `LanglandscapeTests` |
