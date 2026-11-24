# A real-closed field in Tarski geometry (Lean 4)

One consolidated Lean source constructs an interpreted real-closed field on a geometric axis from Tarski's primitive betweenness and congruence axioms and the first-order continuity scheme A13.

## Result

The final theorem is `TarskiField.axis_isRealClosed_tarski` in [`TarskiUnified_v48_Sign.lean`](TarskiUnified_v48_Sign.lean). Its assumptions are `[Plane Point]`, `[ContinuousPlane Point]`, and a frame `f : Frame Point`. It derives `Field`, `LinearOrder`, and `IsStrictOrderedRing` instances internally and proves `IsRealClosed (AxisPoint f)`. The source also proves `frame_exists`.

This is the real-closed-field interpretation direction of the classical Tarski representation theorem, not a proof identifying the full original plane with `F²`.

## Verification

Use Lean `v4.37.0-rc1` and Mathlib (commit `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`). Run `lake update`, `lake exe cache get`, and `lake env lean TarskiUnified_v48_Sign.lean`. The checked source has zero errors and warnings; `#print axioms TarskiField.axis_isRealClosed_tarski` reports `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). The geometric assumptions are explicit parameters, not Lean kernel axioms.

## Historical context

The representation theorem goes back to Tarski (1959). Boutry, Braun and Narboux formalized the construction of an ordered field and Cartesian coordinates in Coq: [From Tarski to Descartes (SCSS 2016)](https://easychair.org/publications/paper/ZvfW); see [GeoCoq](https://geocoq.github.io/GeoCoq/). This Lean development focuses on reaching real-closedness from A13; no blanket priority claim is made.

Snapshot: 2026-11-24. One Lean source; supplementary environment files are for reproducibility.
