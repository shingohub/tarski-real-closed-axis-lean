import Mathlib

-- The proof deliberately declares local proposition-valued typeclass
-- evidence with `letI`; replacing those instances by `let` prevents
-- Lean's typeclass synthesis from finding them.
set_option linter.style.haveILetI false


/-! SOURCE: source/TarskiUnifiedRevised(1).lean -/


/-!
# Tarski geometry: a Lean 4 interpretation of a real-closed field

## Main result and scope

`TarskiField.axis_isRealClosed_tarski`, at the end of this file, constructs
the `Field`, `LinearOrder`, and `IsStrictOrderedRing` instances on the points
of an axis determined by a geometric frame, and proves
`IsRealClosed (AxisPoint f)`. Its geometric assumptions are `Plane Point`
(Tarski's betweenness/congruence axioms for a Euclidean plane) and
`ContinuousPlane Point` (the first-order continuity scheme A13).

The frame is an explicit parameter; the file also proves `frame_exists`.
This theorem is the real-closed-field interpretation direction. It does not
assert the complete representation of the original plane as `F × F`.

## Verification

Checked using Lean `v4.37.0-rc1` with Mathlib at commit
`31ce06eaadf4a200c0e1407c5f10953cf606b8f8` (2026-11-24).
The last `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorryAx`. The plane axioms and A13 remain explicit
typeclass parameters, rather than being counted as Lean kernel axioms.

## Historical context and prior formalization

Tarski's representation theorem is classical. Boutry, Braun and Narboux,
"From Tarski to Descartes: Formalization of the Arithmetization of Euclidean
Geometry" (SCSS 2016), formalized geometric arithmetic, an ordered field,
and Cartesian coordinates in Coq/GeoCoq:
https://easychair.org/publications/paper/ZvfW
GeoCoq project: https://geocoq.github.io/GeoCoq/
This Lean development focuses in particular on deriving real-closedness
internally from A13. No priority claim over other formalizations is made.

## Construction

Only the two geometric relations `Bet` (betweenness) and `Cong` (congruence)
are primitive.  No coordinate space, ordered field, angle measure, real number,
circle, or limiting curve occurs in the formalization below.

Parallelism is defined from betweenness.  An affine frame (O,I,J) gives an
interpreted carrier, the points on line OI.  Addition and multiplication are
defined as geometric construction *relations* (not assumed field operations).

The second part gives first-order formulas for collinearity, rays,
parallelism, addition, multiplication, and square-root cuts. The geometric
interpretations of these formulas are established explicitly. The development
also provides relational Horner evaluation, a compiler from algebraic
expression trees to first-order formulas, and an application of A13 producing
a boundary point of a cut on the axis under precisely stated geometric
hypotheses. No field laws, separation conditions, or root-existence claims
are smuggled in as assumptions of the plane.

This file deliberately does not introduce a class assuming the desired field
laws, `sorry`, real coordinates, or the circle/inscribed-angle theorem.
-/

universe u

namespace TarskiField

/-- The non-logical primitives are exactly betweenness and segment congruence. -/
class Plane (Point : Type u) where
  Bet : Point → Point → Point → Prop
  Cong : Point → Point → Point → Point → Prop
  cong_pseudo_reflexivity : ∀ A B, Cong A B B A
  cong_inner_transitivity : ∀ A B C D E F,
    Cong A B C D → Cong A B E F → Cong C D E F
  cong_identity : ∀ A B C, Cong A B C C → A = B
  segment_construction : ∀ A B C D,
    ∃ E, Bet A B E ∧ Cong B E C D
  five_segment : ∀ A A' B B' C C' D D',
    Cong A B A' B' → Cong B C B' C' →
    Cong A D A' D' → Cong B D B' D' →
    Bet A B C → Bet A' B' C' → A ≠ B →
    Cong C D C' D'
  between_identity : ∀ A B, Bet A B A → A = B
  inner_pasch : ∀ A B C P Q,
    Bet A P C → Bet B Q C →
    ∃ X, Bet P X B ∧ Bet Q X A
  lower_dim : ∃ A B C, ¬ (Bet A B C ∨ Bet B C A ∨ Bet C A B)
  upper_dim : ∀ A B C P Q,
    P ≠ Q → Cong A P A Q → Cong B P B Q → Cong C P C Q →
    (Bet A B C ∨ Bet B C A ∨ Bet C A B)
  euclid : ∀ A B C D T,
    Bet A D T → Bet B D C → A ≠ D →
    ∃ X Y, Bet A B X ∧ Bet A C Y ∧ Bet X T Y

variable {Point : Type u} [Plane Point]
open Plane

def Col (A B C : Point) : Prop :=
  Bet A B C ∨ Bet B C A ∨ Bet C A B

/-- First nontrivial Tarski deduction: self-congruence. -/
theorem congr_refl (A B : Point) : Cong A B A B := by
  have h : Cong B A A B := cong_pseudo_reflexivity B A
  exact cong_inner_transitivity B A A B A B h h

theorem cong_symm {A B C D : Point} (h : Cong A B C D) :
    Cong C D A B :=
  cong_inner_transitivity A B C D A B h (congr_refl A B)

theorem cong_trans {A B C D E F : Point}
    (h : Cong A B C D) (k : Cong C D E F) :
    Cong A B E F :=
  cong_inner_transitivity C D A B E F (cong_symm h) k

/-- Reversing only the first segment does not change its congruence class. -/
theorem cong_reverse_left {A B C D : Point} (h : Cong A B C D) :
    Cong B A C D :=
  cong_trans (cong_pseudo_reflexivity B A) h

/-- Reversing only the second segment does not change its congruence class. -/
theorem cong_reverse_right {A B C D : Point} (h : Cong A B C D) :
    Cong A B D C :=
  cong_trans h (cong_pseudo_reflexivity C D)

/-- Reversal of both oriented segments preserves congruence. -/
theorem cong_reverse_both {A B C D : Point} (h : Cong A B C D) :
    Cong B A D C := by
  exact cong_reverse_right (cong_reverse_left h)

/-- Degenerate segments are all congruent, as a theorem of Tarski's
segment-construction and congruence-identity axioms. -/
theorem cong_zero (A B : Point) : Cong A A B B := by
  obtain ⟨E, _, hcong⟩ := segment_construction A A B B
  have hAE : A = E := cong_identity A E B hcong
  subst E
  exact hcong

/-- Addition of adjacent congruent segments. This is the basic segment
arithmetic lemma used in comparing the order of points on a line. -/
theorem segment_cong_add {A B C A' B' C' : Point}
    (h : Bet A B C) (h' : Bet A' B' C')
    (hAB : Cong A B A' B') (hBC : Cong B C B' C') :
    Cong A C A' C' := by
  by_cases hneq : A = B
  · subst B
    have hA'B' : A' = B' := cong_identity A' B' A (cong_symm hAB)
    subst B'
    exact hBC
  · have hCA : Cong C A C' A' :=
      five_segment A A' B B' C C' A A'
        hAB hBC (cong_zero A A') (cong_reverse_both hAB) h h' hneq
    exact cong_reverse_both hCA

/-- An endpoint lies between the given point and itself. -/
theorem bet_end (A B : Point) : Bet A B B := by
  obtain ⟨E, hbet, hcong⟩ := segment_construction A B B B
  have heq : B = E := cong_identity B E B hcong
  simpa [← heq] using hbet

theorem bet_symm {A B C : Point} (h : Bet A B C) : Bet C B A := by
  obtain ⟨X, hbetween, hreverse⟩ :=
    inner_pasch A B C B C h (bet_end B C)
  have heq : B = X := between_identity B X hbetween
  simpa [← heq] using hreverse

theorem bet_start (A B : Point) : Bet A A B :=
  bet_symm (bet_end B A)

/-- Antisymmetry of non-strict betweenness, from inner Pasch. -/
theorem bet_swap_endpoint_eq {A B C : Point}
    (h₁ : Bet A B C) (h₂ : Bet B A C) : A = B := by
  obtain ⟨X, hBX, hAX⟩ := inner_pasch A B C B A h₁ h₂
  have hB : B = X := between_identity B X hBX
  have hA : A = X := between_identity A X hAX
  exact hA.trans hB.symm

/-- Antisymmetry of the segment order with a common starting point.
    This is a geometric order fact: no addition, multiplication, or
    ambient ordered field occurs in its proof. -/
theorem bet_same_origin_antisymm {A X Y : Point}
    (hXY : Bet A X Y) (hYX : Bet A Y X) : X = Y :=
  bet_swap_endpoint_eq (bet_symm hYX) (bet_symm hXY)

/-- One of the elementary betweenness transitivity laws. -/
theorem bet_inner_trans {A B C D : Point}
    (h₁ : Bet A B D) (h₂ : Bet B C D) : Bet A B C := by
  obtain ⟨X, hBX, hCXA⟩ := inner_pasch A B D B C h₁ h₂
  have hB : B = X := between_identity B X hBX
  exact bet_symm (hB ▸ hCXA)

/-- Exchange of an interior point along a nested pair of segments. -/
theorem bet_exchange {A B C D : Point}
    (h₁ : Bet A B C) (h₂ : Bet A C D) : Bet B C D := by
  obtain ⟨X, hCXC, hBXD⟩ :=
    inner_pasch D C A C B (bet_symm h₂) (bet_symm h₁)
  have hC : C = X := between_identity C X hCXC
  exact hC ▸ hBXD

/-- A point constructed at a prescribed distance along a ray is unique.
The proof uses the five-segment axiom rather than any coordinate law. -/
theorem segment_extension_unique {A B C D : Point}
    (hAB : A ≠ B) (hC : Bet A B C) (hD : Bet A B D)
    (hCD : Cong B C B D) : C = D := by
  have hCC : Cong C C D C :=
    five_segment A A B B C D C C
      (congr_refl A B) hCD (congr_refl A C) (congr_refl B C)
      hC hD hAB
  have hDC : Cong D C C C := cong_symm hCC
  exact (cong_identity D C C hDC).symm

/-- Outer transitivity, using segment construction and its uniqueness. -/
theorem bet_outer_trans {A B C D : Point}
    (hABC : Bet A B C) (hBCD : Bet B C D) (hBC : B ≠ C) :
    Bet A C D := by
  obtain ⟨X, hACX, hCX⟩ := segment_construction A C C D
  have hBCX : Bet B C X := bet_exchange hABC hACX
  have hXD : X = D := segment_extension_unique hBC hBCX hBCD hCX
  simpa [hXD] using hACX

/-- Compatibility of two nested betweenness relations. -/
theorem bet_nested {A B C D : Point}
    (hABD : Bet A B D) (hBCD : Bet B C D) : Bet A C D := by
  by_cases hBC : B = C
  · simpa [← hBC] using hABD
  · exact bet_outer_trans (bet_inner_trans hABD hBCD) hBCD hBC

/-- The remaining exchange rule used to order the affine axis. -/
theorem bet_extend {A B C D : Point}
    (hABC : Bet A B C) (hACD : Bet A C D) : Bet A B D := by
  by_cases hBC : B = C
  · simpa [hBC] using hACD
  · have hDCB : Bet D C B := bet_symm (bet_exchange hABC hACD)
    have hCBA : Bet C B A := bet_symm hABC
    exact bet_symm (bet_outer_trans hDCB hCBA (Ne.symm hBC))

/-- GeoCoq Ch03 `l3_17`: two Pasch applications intersect the segment BB'
with the segment PC. All four endpoints may coincide, as Tarski's primitive
`Bet` permits weak betweenness. This is the crossing lemma used by the
synthetic Krippen midpoint argument in Ch07. -/
theorem pasch_two_crossings_tarski
    {A B C A' B' P : Point}
    (hABC : Bet A B C) (hA'B'C : Bet A' B' C)
    (hAPA' : Bet A P A') :
    ∃ Q : Point, Bet P Q C ∧ Bet B Q B' := by
  obtain ⟨T, hB'TA, hPTC⟩ :=
    inner_pasch C A A' B' P (bet_symm hA'B'C) hAPA'
  obtain ⟨Q, hTQC, hBQB'⟩ :=
    inner_pasch B' C A T B hB'TA (bet_symm hABC)
  exact ⟨Q, bet_nested hPTC hTQC, hBQB'⟩

/-- Reflection of B across A is a unique point obtained by the segment
construction axiom. No additive inverse on a field is presumed. -/
theorem opposite_exists_unique (A B : Point) :
    ∃! C : Point, Bet B A C ∧ Cong A C A B := by
  obtain ⟨C, hbet, hcong⟩ := segment_construction B A A B
  refine ⟨C, ⟨hbet, hcong⟩, ?_⟩
  intro D ⟨hDbet, hDcong⟩
  by_cases hBA : B = A
  · subst B
    have hD : A = D := cong_identity A D A hDcong
    have hC : A = C := cong_identity A C A hcong
    exact hD.symm.trans hC
  · have hCD : Cong A C A D :=
      cong_trans hcong (cong_symm hDcong)
    exact (segment_extension_unique hBA hbet hDbet hCD).symm

theorem col_left (A B : Point) : Col A B A :=
  Or.inr (Or.inl (bet_end B A))

theorem col_right (A B : Point) : Col A B B :=
  Or.inl (bet_end A B)

theorem col_rotate {A B C : Point} (h : Col A B C) : Col B C A := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem col_swap {A B C : Point} (h : Col A B C) : Col B A C := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (bet_symm h))
  · exact Or.inr (Or.inl (bet_symm h))
  · exact Or.inl (bet_symm h)

/-- Two nondegenerate lines are parallel when they coincide or are disjoint.
This uses only betweenness; `Parallel` is not an additional axiom. -/
def Parallel (A B C D : Point) : Prop :=
  A ≠ B ∧ C ≠ D ∧
    ((∀ X : Point, Col A B X ↔ Col C D X) ∨
     (∀ X : Point, ¬ (Col A B X ∧ Col C D X)))

theorem parallel_refl {A B : Point} (hAB : A ≠ B) :
    Parallel A B A B :=
  ⟨hAB, hAB, Or.inl (fun _ => Iff.rfl)⟩

theorem parallel_symm {A B C D : Point}
    (h : Parallel A B C D) : Parallel C D A B := by
  rcases h with ⟨hAB, hCD, hsame | hdisjoint⟩
  · exact ⟨hCD, hAB, Or.inl (fun X => (hsame X).symm)⟩
  · exact ⟨hCD, hAB, Or.inr (fun X hX => hdisjoint X ⟨hX.2, hX.1⟩)⟩

/-- If two parallel lines share a point, they are the same line. -/
theorem parallel_same_of_intersection {A B C D X : Point}
    (h : Parallel A B C D) (hAB : Col A B X)
    (hCD : Col C D X) : ∀ Y, Col A B Y ↔ Col C D Y := by
  rcases h with ⟨_, _, hsame | hdisj⟩
  · exact hsame
  · exact False.elim (hdisj X ⟨hAB, hCD⟩)

/-- Reversing either or both defining lines preserves synthetic parallelism. -/
theorem parallel_reverse_left {A B C D : Point}
    (h : Parallel A B C D) : Parallel B A C D := by
  rcases h with ⟨hAB, hCD, hsame | hdisjoint⟩
  · refine ⟨hAB.symm, hCD, Or.inl ?_⟩
    intro X
    constructor
    · intro hX
      exact (hsame X).mp (col_swap hX)
    · intro hX
      exact col_swap ((hsame X).mpr hX)
  · refine ⟨hAB.symm, hCD, Or.inr ?_⟩
    intro X hX
    exact hdisjoint X ⟨col_swap hX.1, hX.2⟩

theorem parallel_reverse_right {A B C D : Point}
    (h : Parallel A B C D) : Parallel A B D C :=
  parallel_symm (parallel_reverse_left (parallel_symm h))

theorem parallel_reverse_both {A B C D : Point}
    (h : Parallel A B C D) : Parallel B A D C :=
  parallel_reverse_right (parallel_reverse_left h)

/-- In the chosen definition, two nondegenerate lines not parallel
    share a point. This is pure first-order logic, without coordinates. -/
theorem not_parallel_lines_intersect (A B C D : Point)
    (hAB : A ≠ B) (hCD : C ≠ D)
    (hnpar : ¬ Parallel A B C D) :
    ∃ X : Point, Col A B X ∧ Col C D X := by
  classical
  by_contra hnone
  apply hnpar
  refine ⟨hAB, hCD, Or.inr ?_⟩
  intro X hX
  exact hnone ⟨X, hX⟩

/-- An affine frame is obtained from the lower-dimension Tarski axiom. -/
structure Frame (Point : Type u) [Plane Point] where
  O : Point
  I : Point
  J : Point
  noncol : ¬ Col O I J

theorem frame_exists : Nonempty (Frame Point) := by
  obtain ⟨O, I, J, h⟩ := Plane.lower_dim (Point := Point)
  exact ⟨⟨O, I, J, h⟩⟩

theorem Frame.O_ne_I (f : Frame Point) : f.O ≠ f.I := by
  intro h
  apply f.noncol
  rw [← h]
  exact Or.inr (Or.inr (bet_end f.J f.O))

/-- Every ray extends properly beyond its endpoint. The nonzero length
is obtained from lower dimension, not from numerical coordinates. -/
theorem segment_extension_nontrivial (A B : Point) :
    ∃ C : Point, Bet A B C ∧ B ≠ C := by
  obtain ⟨f⟩ : Nonempty (Frame Point) := frame_exists
  obtain ⟨C, hbet, hcong⟩ := segment_construction A B f.O f.I
  refine ⟨C, hbet, ?_⟩
  intro hBC
  have hOI : f.O = f.I :=
    cong_identity f.O f.I B (by simpa [hBC] using (cong_symm hcong))
  exact f.O_ne_I hOI

/-- Tarski's five-segment axiom propagates equality of distances from
    two distinct stations to all points beyond one of the stations. -/
private theorem equidistant_extend_beyond
    {A B C P Q : Point}
    (hAB : A ≠ B) (hABC : Bet A B C)
    (hAP : Cong A P A Q) (hBP : Cong B P B Q) :
    Cong C P C Q := by
  exact five_segment A A B B C C P Q
    (congr_refl A B) (congr_refl B C)
    hAP hBP hABC hABC hAB

/-- For a point between the stations, first prolong AB and apply the
    preceding five-segment argument twice. -/
theorem equidistant_between_stations
    {A B C P Q : Point}
    (hAB : A ≠ B) (hACB : Bet A C B)
    (hAP : Cong A P A Q) (hBP : Cong B P B Q) :
    Cong C P C Q := by
  obtain ⟨D, hABD, hBD⟩ := segment_extension_nontrivial A B
  have hDP : Cong D P D Q :=
    equidistant_extend_beyond hAB hABD hAP hBP
  have hDBC : Bet D B C :=
    bet_symm (bet_exchange hACB hABD)
  exact equidistant_extend_beyond hBD.symm hDBC hDP hBP

/-- Tarski's two-station distance propagation along their whole line.
    This is the synthetic counterpart of GeoCoq's l4_17; it assumes no
    coordinate field, Euclidean inner product, or continuity principle. -/
theorem col_equidistant_of_two_stations
    {A B C P Q : Point}
    (hAB : A ≠ B) (hCol : Col A B C)
    (hAP : Cong A P A Q) (hBP : Cong B P B Q) :
    Cong C P C Q := by
  rcases hCol with hABC | hBCA | hCAB
  · exact equidistant_extend_beyond hAB hABC hAP hBP
  · exact equidistant_between_stations hAB.symm hBCA hBP hAP
  · exact equidistant_extend_beyond hAB.symm (bet_symm hCAB) hBP hAP

/-- An off-line station distinguishes two points that are equidistant
    from two distinct stations on the reference line. -/
theorem third_station_separates_distinct
    {A B C P Q : Point}
    (hC : ¬ Col A B C) (hPQ : P ≠ Q)
    (hAP : Cong A P A Q) (hBP : Cong B P B Q) :
    ¬ Cong C P C Q := by
  intro hCP
  exact hC (Plane.upper_dim A B C P Q hPQ hAP hBP hCP)

theorem Frame.O_ne_J (f : Frame Point) : f.O ≠ f.J := by
  intro h
  apply f.noncol
  rw [← h]
  exact col_left f.O f.I

theorem Frame.I_ne_J (f : Frame Point) : f.I ≠ f.J := by
  intro h
  apply f.noncol
  rw [← h]
  exact col_right f.O f.I

theorem Frame.J_ne_axis_point (f : Frame Point)
    (X : Point) (hX : Col f.O f.I X) : f.J ≠ X := by
  intro h
  apply f.noncol
  simpa [h] using hX

/-- The two axes of the frame, OI and OJ, are distinct nonparallel lines. -/
theorem frame_axes_not_parallel (f : Frame Point) :
    ¬ Parallel f.O f.I f.O f.J := by
  intro hparallel
  have hsame : ∀ Y : Point,
      Col f.O f.I Y ↔ Col f.O f.J Y :=
    parallel_same_of_intersection hparallel
      (col_left f.O f.I) (col_left f.O f.J)
  exact f.noncol ((hsame f.J).mpr (col_right f.O f.J))

/-- The line IJ and the auxiliary axis OJ are nonparallel. -/
theorem frame_IJ_not_parallel_OJ (f : Frame Point) :
    ¬ Parallel f.I f.J f.O f.J := by
  intro hpar
  have hsame : ∀ T : Point,
      Col f.I f.J T ↔ Col f.O f.J T :=
    parallel_same_of_intersection hpar
      (col_right f.I f.J) (col_right f.O f.J)
  have hIJO : Col f.I f.J f.O :=
    (hsame f.O).mpr (col_left f.O f.J)
  exact f.noncol (col_rotate (col_rotate hIJO))

/-- Three congruence constraints to a fixed noncollinear reference frame
determine a point uniquely. This is the direct nontrivial consequence of
Tarski's upper-dimensional axiom needed for coordinate injectivity. -/
theorem Frame.three_distances_unique (f : Frame Point) {P Q : Point}
    (hO : Cong f.O P f.O Q)
    (hI : Cong f.I P f.I Q)
    (hJ : Cong f.J P f.J Q) : P = Q := by
  by_contra hPQ
  exact f.noncol (Plane.upper_dim f.O f.I f.J P Q hPQ hO hI hJ)

/-- The interpreted scalars are points on the chosen axis OI. -/
def AxisPoint (f : Frame Point) : Type u :=
  { X : Point // Col f.O f.I X }

/-- Every line from J to an axis point crosses OI transversely. -/
theorem frame_axis_not_parallel_JY
    (f : Frame Point) (y : AxisPoint f) :
    ¬ Parallel f.O f.I f.J y.1 := by
  intro hparallel
  have hsame : ∀ Y : Point,
      Col f.O f.I Y ↔ Col f.J y.1 Y :=
    parallel_same_of_intersection hparallel y.2
      (col_right f.J y.1)
  exact f.noncol ((hsame f.J).mpr (col_left f.J y.1))

theorem frame_axis_JY_intersect
    (f : Frame Point) (y : AxisPoint f) :
    ∃ X : Point, Col f.O f.I X ∧ Col f.J y.1 X := by
  exact not_parallel_lines_intersect f.O f.I f.J y.1
    f.O_ne_I (f.J_ne_axis_point y.1 y.2)
    (frame_axis_not_parallel_JY f y)

/-- The oblique line JX through a scalar cannot be parallel to OI. -/
theorem frame_JX_not_parallel_OI (f : Frame Point)
    (x : AxisPoint f) :
    ¬ Parallel f.J x.1 f.O f.I := by
  intro hpar
  have hsame : ∀ T : Point,
      Col f.J x.1 T ↔ Col f.O f.I T :=
    parallel_same_of_intersection hpar
      (col_right f.J x.1) x.2
  have hOIJ : Col f.O f.I f.J :=
    (hsame f.J).mp (col_left f.J x.1)
  exact f.noncol hOIJ

def axisZero (f : Frame Point) : AxisPoint f :=
  ⟨f.O, col_left f.O f.I⟩

def axisOne (f : Frame Point) : AxisPoint f :=
  ⟨f.I, col_right f.O f.I⟩

theorem axisZero_ne_axisOne (f : Frame Point) :
    axisZero f ≠ axisOne f := by
  intro h
  exact f.O_ne_I (congrArg Subtype.val h)

/-- The interpreted axis has a point strictly beyond the unit. -/
theorem axis_beyond_one_exists (f : Frame Point) :
    ∃ z : AxisPoint f, Bet f.O f.I z.1 ∧ z ≠ axisOne f := by
  obtain ⟨N, hbet, hne⟩ := segment_extension_nontrivial f.O f.I
  refine ⟨⟨N, Or.inl hbet⟩, hbet, ?_⟩
  intro h
  exact hne (congrArg Subtype.val h).symm

/-- Geometric construction of the candidate negative unit on the axis.
The field law 1 + (-1) = 0 remains a separate theorem to be derived later. -/
theorem axis_opposite_one_exists_unique (f : Frame Point) :
    ∃! z : AxisPoint f,
      Bet f.I f.O z.1 ∧ Cong f.O z.1 f.O f.I := by
  obtain ⟨N, ⟨hb, hc⟩, hu⟩ := opposite_exists_unique f.O f.I
  let z : AxisPoint f := ⟨N, Or.inr (Or.inr (bet_symm hb))⟩
  refine ⟨z, ⟨hb, hc⟩, ?_⟩
  intro w hw
  apply Subtype.ext
  exact hu w.1 hw

/-- The positive ray of the prospective ordered field. -/
def Out (O A X : Point) : Prop :=
  A ≠ O ∧ X ≠ O ∧ (Bet O A X ∨ Bet O X A)

def Positive (f : Frame Point) (x : AxisPoint f) : Prop :=
  Out f.O f.I x.1

theorem axisOne_positive (f : Frame Point) :
    Positive f (axisOne f) := by
  exact ⟨f.O_ne_I.symm, f.O_ne_I.symm, Or.inl (bet_end f.O f.I)⟩

/-- There is a point on the axis opposite to the unit, and it is outside
the positive ray. This precedes all definitions of field inequalities. -/
theorem axis_negative_one_exists (f : Frame Point) :
    ∃ z : AxisPoint f,
      (Bet f.I f.O z.1 ∧ Cong f.O z.1 f.O f.I) ∧ ¬ Positive f z := by
  obtain ⟨z, hz, _⟩ := axis_opposite_one_exists_unique f
  refine ⟨z, hz, ?_⟩
  intro hpos
  rcases hpos with ⟨_, hne, hI | hN⟩
  · have h : f.I = f.O := bet_swap_endpoint_eq hz.1 hI
    exact f.O_ne_I h.symm
  · have h : z.1 = f.O := bet_swap_endpoint_eq (bet_symm hz.1) hN
    exact hne h

/-- Synthetic addition on the axis.
Transfer X vertically to T at height J, then project T along the direction
JY back to the axis at Z. In Cartesian notation, this gives z = x + y,
but this file does not assume any Cartesian coordinates. -/
def RawAddGraph (O I J X Y Z : Point) : Prop :=
  (X = O ∧ Z = Y) ∨
  (X ≠ O ∧ ∃ T : Point,
    Parallel O J X T ∧
    Parallel O I J T ∧
    Parallel J Y T Z)

def AddGraph (f : Frame Point)
    (x y z : AxisPoint f) : Prop :=
  (x.1 = f.O ∧ z = y) ∨
  (x.1 ≠ f.O ∧ ∃ T : Point,
    Parallel f.O f.J x.1 T ∧
    Parallel f.O f.I f.J T ∧
    Parallel f.J y.1 T z.1)

/-- Conversion between point-level and axis-level geometric addition. -/
theorem rawAddGraph_axis_iff (f : Frame Point)
    (x y z : AxisPoint f) :
    RawAddGraph f.O f.I f.J x.1 y.1 z.1 ↔ AddGraph f x y z := by
  constructor
  · rintro (⟨hx, hz⟩ | ⟨hx, T, hT⟩)
    · exact Or.inl ⟨hx, Subtype.ext hz⟩
    · exact Or.inr ⟨hx, T, hT⟩
  · rintro (⟨hx, hz⟩ | ⟨hx, T, hT⟩)
    · exact Or.inl ⟨hx, congrArg Subtype.val hz⟩
    · exact Or.inr ⟨hx, T, hT⟩

theorem add_zero_left (f : Frame Point) (y : AxisPoint f) :
    AddGraph f (axisZero f) y y :=
  Or.inl ⟨rfl, rfl⟩

theorem add_zero_left_unique (f : Frame Point)
    (y z : AxisPoint f) (h : AddGraph f (axisZero f) y z) :
    z = y := by
  rcases h with ⟨_, heq⟩ | ⟨hne, _⟩
  · exact heq
  · exact False.elim (hne rfl)

/-- Synthetic multiplication on the axis.
Project Y along IJ to the secondary axis OJ at W, then project W along
the direction JX back to OI at Z. This gives z = x*y in any Cartesian model;
existence and uniqueness will be proved synthetically from the axioms. -/
def MulGraph (f : Frame Point)
    (x y z : AxisPoint f) : Prop :=
  (y.1 = f.O ∧ z = axisZero f) ∨
  (y.1 ≠ f.O ∧ ∃ W : Point,
    Col f.O f.J W ∧
    Parallel f.I f.J y.1 W ∧
    Parallel f.J x.1 W z.1)

theorem mul_zero_right (f : Frame Point) (x : AxisPoint f) :
    MulGraph f x (axisZero f) (axisZero f) :=
  Or.inl ⟨rfl, rfl⟩

/-- A nontrivial fragment of the multiplicative identity law, proved from
the explicit parallel-line construction and the Tarski dimension axiom. -/
theorem mul_one_right (f : Frame Point) (x : AxisPoint f) :
    MulGraph f x (axisOne f) x := by
  refine Or.inr ⟨f.O_ne_I.symm, f.J, col_right f.O f.J, ?_, ?_⟩
  · exact parallel_refl f.I_ne_J
  · exact parallel_refl (f.J_ne_axis_point x.1 x.2)

/-- The first multiplicative projection cannot send a scalar point to O.
    Otherwise the lines IJ and yO would share I and coincide, forcing O
    onto IJ and contradicting the frame's noncollinearity. -/
theorem mul_first_projection_nonzero
    (f : Frame Point) (y : AxisPoint f) (W : Point)
    (hpar : Parallel f.I f.J y.1 W) : W ≠ f.O := by
  intro hW
  have hIO : Col y.1 W f.I := by
    simpa [hW] using (col_rotate (col_rotate y.2))
  have hsame : ∀ T : Point,
      Col f.I f.J T ↔ Col y.1 W T :=
    parallel_same_of_intersection hpar
      (col_left f.I f.J) hIO
  have hIJO : Col f.I f.J f.O :=
    (hsame f.O).mpr (by
      simpa [hW] using (col_right y.1 f.O))
  exact f.noncol (col_rotate (col_rotate hIJO))

theorem mul_zero_right_unique (f : Frame Point)
    (x z : AxisPoint f) (h : MulGraph f x (axisZero f) z) :
    z = axisZero f := by
  rcases h with ⟨_, heq⟩ | ⟨hne, _⟩
  · exact heq
  · exact False.elim (hne rfl)

/-- Formulas for the first-order continuity *scheme* (not Dedekind
completeness and not a quantifier over all arbitrary subsets of points). -/
inductive Formula : Nat → Type where
  | equal {n} (i j : Fin n) : Formula n
  | bet {n} (i j k : Fin n) : Formula n
  | cong {n} (i j k l : Fin n) : Formula n
  | neg {n} (p : Formula n) : Formula n
  | conj {n} (p q : Formula n) : Formula n
  | disj {n} (p q : Formula n) : Formula n
  | impl {n} (p q : Formula n) : Formula n
  | all {n} (p : Formula (n + 1)) : Formula n
  | ex {n} (p : Formula (n + 1)) : Formula n

def Formula.eval : {n : Nat} → Formula n → (Fin n → Point) → Prop
  | _, .equal i j, ρ => ρ i = ρ j
  | _, .bet i j k, ρ => Bet (ρ i) (ρ j) (ρ k)
  | _, .cong i j k l, ρ => Cong (ρ i) (ρ j) (ρ k) (ρ l)
  | _, .neg p, ρ => ¬ p.eval ρ
  | _, .conj p q, ρ => p.eval ρ ∧ q.eval ρ
  | _, .disj p q, ρ => p.eval ρ ∨ q.eval ρ
  | _, .impl p q, ρ => p.eval ρ → q.eval ρ
  | _, .all p, ρ => ∀ X, p.eval (Fin.cons X ρ)
  | _, .ex p, ρ => ∃ X, p.eval (Fin.cons X ρ)

/-- Tarski's A13 (elementary continuity) is an axiom scheme over formulas. -/
class ContinuousPlane (Point : Type u) [Plane Point] where
  first_order_continuity :
    ∀ (n : Nat) (Xi Upsilon : Formula (n + 1))
      (params : Fin n → Point),
      (∃ A, ∀ X Y,
        Xi.eval (Fin.cons X params) →
        Upsilon.eval (Fin.cons Y params) → Bet A X Y) →
      (∃ B, ∀ X Y,
        Xi.eval (Fin.cons X params) →
        Upsilon.eval (Fin.cons Y params) → Bet X B Y)

/-! ## First-order syntax for the coordinatization construction

All the following formulas use only equality, `Bet`, and `Cong` (and first-order
logical connectives).  Auxiliary indices denote *point variables*, not field
elements.  Each occurrence of `Fin.succ` crosses a quantifier binder.
-/

/-- Expresses `Col (ρ i) (ρ j) (ρ k)` without a new predicate symbol. -/
def colFormula {n : Nat} (i j k : Fin n) : Formula n :=
  .disj (.bet i j k) (.disj (.bet j k i) (.bet k i j))

theorem colFormula_eval {n : Nat} (i j k : Fin n) (ρ : Fin n → Point) :
    (colFormula i j k).eval ρ ↔ Col (ρ i) (ρ j) (ρ k) := by
  simp [colFormula, Formula.eval, Col]

/-- Expresses the open ray `Out (ρ o) (ρ a) (ρ x)`. -/
def outFormula {n : Nat} (o a x : Fin n) : Formula n :=
  .conj (.neg (.equal a o))
    (.conj (.neg (.equal x o))
      (.disj (.bet o a x) (.bet o x a)))

theorem outFormula_eval {n : Nat} (o a x : Fin n) (ρ : Fin n → Point) :
    (outFormula o a x).eval ρ ↔ Out (ρ o) (ρ a) (ρ x) := by
  simp [outFormula, Formula.eval, Out]

/-- Restrict an arbitrary formula `φ(x,params)` to the frame axis. -/
def onAxisFormula {n : Nat} (oIdx iIdx : Fin n) (φ : Formula (n + 1)) :
    Formula (n + 1) :=
  .conj (colFormula oIdx.succ iIdx.succ 0) φ

theorem onAxisFormula_eval {n : Nat} (oIdx iIdx : Fin n)
    (φ : Formula (n + 1)) (x : Point) (params : Fin n → Point) :
    (onAxisFormula oIdx iIdx φ).eval (Fin.cons x params) ↔
      Col (params oIdx) (params iIdx) x ∧ φ.eval (Fin.cons x params) := by
  simp [onAxisFormula, Formula.eval, colFormula_eval]

/-- The nonnegative closed ray, explicitly including its origin. -/
def nonnegAxisFormula {n : Nat} (oIdx iIdx : Fin n) : Formula (n + 1) :=
  .conj (colFormula oIdx.succ iIdx.succ 0)
    (.disj (.equal 0 oIdx.succ) (outFormula oIdx.succ iIdx.succ 0))

theorem nonnegAxisFormula_eval {n : Nat} (oIdx iIdx : Fin n)
    (x : Point) (params : Fin n → Point) :
    (nonnegAxisFormula oIdx iIdx).eval (Fin.cons x params) ↔
      Col (params oIdx) (params iIdx) x ∧
        (x = params oIdx ∨ Out (params oIdx) (params iIdx) x) := by
  simp [nonnegAxisFormula, Formula.eval, colFormula_eval, outFormula_eval]

/-- Closed nonnegative ray for a free point variable, not a binder. -/
def nonnegPointFormula {n : Nat} (o i a : Fin n) : Formula n :=
  .conj (colFormula o i a)
    (.disj (.equal a o) (outFormula o i a))

theorem nonnegPointFormula_eval {n : Nat} (o i a : Fin n)
    (ρ : Fin n → Point) :
    (nonnegPointFormula o i a).eval ρ ↔
      Col (ρ o) (ρ i) (ρ a) ∧
        (ρ a = ρ o ∨ Out (ρ o) (ρ i) (ρ a)) := by
  simp [nonnegPointFormula, Formula.eval, colFormula_eval, outFormula_eval]

/-- `Parallel (ρ a) (ρ b) (ρ c) (ρ d)` as a first-order formula.
`Parallel` itself was defined from coincident or disjoint nondegenerate lines. -/
def parallelFormula {n : Nat} (a b c d : Fin n) : Formula n :=
  .conj (.neg (.equal a b))
    (.conj (.neg (.equal c d))
      (.disj
        (.all
          (.conj
            (.impl (colFormula a.succ b.succ 0)
              (colFormula c.succ d.succ 0))
            (.impl (colFormula c.succ d.succ 0)
              (colFormula a.succ b.succ 0))))
        (.all
          (.neg (.conj (colFormula a.succ b.succ 0)
            (colFormula c.succ d.succ 0))))))

theorem parallelFormula_eval {n : Nat} (a b c d : Fin n)
    (ρ : Fin n → Point) :
    (parallelFormula a b c d).eval ρ ↔
      Parallel (ρ a) (ρ b) (ρ c) (ρ d) := by
  simp [parallelFormula, Formula.eval, Parallel, colFormula_eval, iff_def]

/-- Geometric addition on axis points, expressed as a first-order formula.
The `T` in the existential is variable 0; old variables are shifted by `succ`.
This syntactic formula assumes axis membership of the free operands separately. -/
def addGraphFormula {n : Nat} (o i j x y z : Fin n) : Formula n :=
  .disj
    (.conj (.equal x o) (.equal z y))
    (.conj (.neg (.equal x o))
      (.ex
        (.conj (parallelFormula o.succ j.succ x.succ 0)
          (.conj (parallelFormula o.succ i.succ j.succ 0)
            (parallelFormula j.succ y.succ 0 z.succ)))))

theorem addGraphFormula_eval {n : Nat} (o i j x y z : Fin n)
    (ρ : Fin n → Point) :
    (addGraphFormula o i j x y z).eval ρ ↔
      ((ρ x = ρ o ∧ ρ z = ρ y) ∨
       (ρ x ≠ ρ o ∧ ∃ T : Point,
         Parallel (ρ o) (ρ j) (ρ x) T ∧
         Parallel (ρ o) (ρ i) (ρ j) T ∧
         Parallel (ρ j) (ρ y) T (ρ z))) := by
  simp [addGraphFormula, Formula.eval, parallelFormula_eval]

/-- The first-order addition formula is extensionally equal to the raw
    construction on unrestricted point variables. -/
theorem addGraphFormula_raw_eval {n : Nat} (o i j x y z : Fin n)
    (ρ : Fin n → Point) :
    (addGraphFormula o i j x y z).eval ρ ↔
      RawAddGraph (ρ o) (ρ i) (ρ j) (ρ x) (ρ y) (ρ z) := by
  simpa [RawAddGraph] using addGraphFormula_eval o i j x y z ρ

/-- Geometric multiplication on axis points, expressed as a first-order formula.
The intermediate point `W` is variable 0 under the existential binder. -/
def mulGraphFormula {n : Nat} (o i j x y z : Fin n) : Formula n :=
  .disj
    (.conj (.equal y o) (.equal z o))
    (.conj (.neg (.equal y o))
      (.ex
        (.conj (colFormula o.succ j.succ 0)
          (.conj (parallelFormula i.succ j.succ y.succ 0)
            (parallelFormula j.succ x.succ 0 z.succ)))))

theorem mulGraphFormula_eval {n : Nat} (o i j x y z : Fin n)
    (ρ : Fin n → Point) :
    (mulGraphFormula o i j x y z).eval ρ ↔
      ((ρ y = ρ o ∧ ρ z = ρ o) ∨
       (ρ y ≠ ρ o ∧ ∃ W : Point,
         Col (ρ o) (ρ j) W ∧
         Parallel (ρ i) (ρ j) (ρ y) W ∧
         Parallel (ρ j) (ρ x) W (ρ z))) := by
  simp [mulGraphFormula, Formula.eval, colFormula_eval, parallelFormula_eval]

/-- Inside `∃ s`, `s` is variable 0 and the original point `x` is variable 1.
Crucially, `s` itself is constrained to the scalar axis: the geometric
multiplication construction is meaningful as a *field* operation only there. -/
def squareGraphFormula {n : Nat} (o i j : Fin n) : Formula (n + 2) :=
  .conj (colFormula o.succ.succ i.succ.succ 0)
    (mulGraphFormula o.succ.succ i.succ.succ j.succ.succ 1 1 0)

/-- Unrestricted point-level reading of the synthetic multiplication diagram.
It is useful before one has proved that its result lies on the axis. -/
def RawMulGraph (O I J X Y Z : Point) : Prop :=
  (Y = O ∧ Z = O) ∨
  (Y ≠ O ∧ ∃ W : Point,
    Col O J W ∧ Parallel I J Y W ∧ Parallel J X W Z)

/-- The syntactic multiplier has precisely the declared geometric meaning;
this theorem does not assume any ordered-field properties. -/
theorem mulGraphFormula_raw_eval {n : Nat} (o i j x y z : Fin n)
    (ρ : Fin n → Point) :
    (mulGraphFormula o i j x y z).eval ρ ↔
      RawMulGraph (ρ o) (ρ i) (ρ j) (ρ x) (ρ y) (ρ z) := by
  simpa [RawMulGraph] using mulGraphFormula_eval o i j x y z ρ

/-- The bound variable zero is the square result `s`; variable one is `x`.
In particular both multiplication inputs really denote the same point. -/
theorem squareGraphFormula_eval {n : Nat} (o i j : Fin n)
    (x s : Point) (params : Fin n → Point) :
    (squareGraphFormula o i j).eval (Fin.cons s (Fin.cons x params)) ↔
      Col (params o) (params i) s ∧
        RawMulGraph (params o) (params i) (params j) x x s := by
  simp [squareGraphFormula, Formula.eval, colFormula_eval,
    mulGraphFormula_raw_eval]

/-- Lower cut of √a for a nonnegative parameter a.
    The parameter guard is essential: Bet O O a holds even when a is on
    the *negative* ray, and hence is not an unrestricted encoding of 0 ≤ a. -/
def sqrtLowerFormula {n : Nat} (o i j a : Fin n) : Formula (n + 1) :=
  .conj (nonnegPointFormula o.succ i.succ a.succ)
    (.conj (nonnegAxisFormula o i)
      (.ex
        (.conj (squareGraphFormula o i j)
          (.disj (.equal 0 a.succ.succ)
            (.bet o.succ.succ 0 a.succ.succ)))))

/-- Upper cut, guarded by the same nonnegativity condition on a. -/
def sqrtUpperFormula {n : Nat} (o i j a : Fin n) : Formula (n + 1) :=
  .conj (nonnegPointFormula o.succ i.succ a.succ)
    (.conj (nonnegAxisFormula o i)
      (.ex
        (.conj (squareGraphFormula o i j)
          (.disj (.equal a.succ.succ 0)
            (.bet o.succ.succ a.succ.succ 0)))))

/-- Point-level semantics of the guarded lower cut. -/
theorem sqrtLowerFormula_eval {n : Nat} (o i j a : Fin n)
    (x : Point) (params : Fin n → Point) :
    (sqrtLowerFormula o i j a).eval (Fin.cons x params) ↔
      (Col (params o) (params i) (params a) ∧
        (params a = params o ∨ Out (params o) (params i) (params a))) ∧
      (Col (params o) (params i) x ∧
        (x = params o ∨ Out (params o) (params i) x)) ∧
      ∃ s : Point,
        Col (params o) (params i) s ∧
        RawMulGraph (params o) (params i) (params j) x x s ∧
        (s = params a ∨ Bet (params o) s (params a)) := by
  simp [sqrtLowerFormula, Formula.eval, nonnegPointFormula_eval,
    nonnegAxisFormula_eval, squareGraphFormula_eval, and_assoc]

/-- Point-level semantics of the guarded upper cut. -/
theorem sqrtUpperFormula_eval {n : Nat} (o i j a : Fin n)
    (x : Point) (params : Fin n → Point) :
    (sqrtUpperFormula o i j a).eval (Fin.cons x params) ↔
      (Col (params o) (params i) (params a) ∧
        (params a = params o ∨ Out (params o) (params i) (params a))) ∧
      (Col (params o) (params i) x ∧
        (x = params o ∨ Out (params o) (params i) x)) ∧
      ∃ s : Point,
        Col (params o) (params i) s ∧
        RawMulGraph (params o) (params i) (params j) x x s ∧
        (params a = s ∨ Bet (params o) (params a) s) := by
  simp [sqrtUpperFormula, Formula.eval, nonnegPointFormula_eval,
    nonnegAxisFormula_eval, squareGraphFormula_eval, and_assoc]

/-- Geometric multiplication at the raw point level is exactly multiplication
on `AxisPoint` once all three arguments are known to lie on the frame axis. -/
theorem rawMulGraph_axis_iff (f : Frame Point)
    (x y z : AxisPoint f) :
    RawMulGraph f.O f.I f.J x.1 y.1 z.1 ↔ MulGraph f x y z := by
  constructor
  · rintro (⟨hy, hz⟩ | ⟨hy, W, hW⟩)
    · exact Or.inl ⟨hy, Subtype.ext hz⟩
    · exact Or.inr ⟨hy, W, hW⟩
  · rintro (⟨hy, hz⟩ | ⟨hy, W, hW⟩)
    · exact Or.inl ⟨hy, congrArg Subtype.val hz⟩
    · exact Or.inr ⟨hy, W, hW⟩

/-- The closed square graph of the syntactic A13 cut is *the* geometrically
defined multiplication relation on the interpreted axis. -/
theorem squareGraphFormula_frame_eval (f : Frame Point)
    (x s : AxisPoint f) :
    (squareGraphFormula (0 : Fin 3) 1 2).eval
      (Fin.cons s.1 (Fin.cons x.1 ![f.O, f.I, f.J])) ↔
        MulGraph f x x s := by
  rw [squareGraphFormula_eval]
  constructor
  · rintro ⟨_, hraw⟩
    exact (rawMulGraph_axis_iff f x x s).mp hraw
  · intro hmul
    exact ⟨s.2, (rawMulGraph_axis_iff f x x s).mpr hmul⟩

/-! ## Proven elementary results, without assuming any field laws -/

/-- The prospective ordered axis: `y = x + z` for a positive `z`. -/
def SubGraph (f : Frame Point) (x y z : AxisPoint f) : Prop :=
  AddGraph f y z x

def AxisLt (f : Frame Point) (x y : AxisPoint f) : Prop :=
  ∃ z : AxisPoint f, SubGraph f y x z ∧ Positive f z

def AxisNonneg (f : Frame Point) (x : AxisPoint f) : Prop :=
  x = axisZero f ∨ AxisLt f (axisZero f) x

theorem axis_nonneg_iff_ray_or_origin (f : Frame Point) (x : AxisPoint f) :
    AxisNonneg f x ↔ (x.1 = f.O ∨ Out f.O f.I x.1) := by
  constructor
  · intro h
    rcases h with hzero | hpos
    · exact Or.inl (congrArg Subtype.val hzero)
    · obtain ⟨z, hsub, hz⟩ := hpos
      have heq : x = z := add_zero_left_unique f z x hsub
      exact Or.inr (heq.symm ▸ hz)
  · rintro (hzero | hpos)
    · exact Or.inl (Subtype.ext hzero)
    · exact Or.inr ⟨x, add_zero_left f x, hpos⟩

/-- A strictly positive axis point is also nonnegative, without any
    use of a field law or completeness. -/
theorem positive_implies_axis_nonneg (f : Frame Point)
    (a : AxisPoint f) (ha : Positive f a) : AxisNonneg f a := by
  exact (axis_nonneg_iff_ray_or_origin f a).mpr (Or.inr ha)

/-- The guarded lower-cut formula is a predicate on the interpreted axis. -/
theorem sqrtLowerFormula_axis_eval (f : Frame Point)
    (a x : AxisPoint f) :
    (sqrtLowerFormula (0 : Fin 4) 1 2 3).eval
      (Fin.cons x.1 ![f.O, f.I, f.J, a.1]) ↔
      AxisNonneg f a ∧ AxisNonneg f x ∧
        ∃ s : AxisPoint f,
          MulGraph f x x s ∧ (s = a ∨ Bet f.O s.1 a.1) := by
  have hsem :
      (sqrtLowerFormula (0 : Fin 4) 1 2 3).eval
        (Fin.cons x.1 ![f.O, f.I, f.J, a.1]) ↔
      (Col f.O f.I a.1 ∧ (a.1 = f.O ∨ Out f.O f.I a.1)) ∧
      (Col f.O f.I x.1 ∧ (x.1 = f.O ∨ Out f.O f.I x.1)) ∧
      ∃ s : Point, Col f.O f.I s ∧
        RawMulGraph f.O f.I f.J x.1 x.1 s ∧
        (s = a.1 ∨ Bet f.O s a.1) := by
    simpa using (sqrtLowerFormula_eval
      (0 : Fin 4) 1 2 3 x.1 ![f.O, f.I, f.J, a.1])
  rw [hsem]
  constructor
  · rintro ⟨⟨_, ha⟩, ⟨_, hx⟩, s, hscol, hsraw, hle⟩
    let sa : AxisPoint f := ⟨s, hscol⟩
    refine ⟨(axis_nonneg_iff_ray_or_origin f a).mpr ha,
      (axis_nonneg_iff_ray_or_origin f x).mpr hx,
      sa, (rawMulGraph_axis_iff f x x sa).mp hsraw, ?_⟩
    rcases hle with heq | hbet
    · exact Or.inl (Subtype.ext heq)
    · exact Or.inr hbet
  · rintro ⟨ha, hx, s, hmul, hle⟩
    refine ⟨⟨a.2, (axis_nonneg_iff_ray_or_origin f a).mp ha⟩,
      ⟨x.2, (axis_nonneg_iff_ray_or_origin f x).mp hx⟩,
      s.1, s.2, (rawMulGraph_axis_iff f x x s).mpr hmul, ?_⟩
    rcases hle with heq | hbet
    · exact Or.inl (congrArg Subtype.val heq)
    · exact Or.inr hbet

/-- The guarded upper-cut formula has reversed betweenness direction. -/
theorem sqrtUpperFormula_axis_eval (f : Frame Point)
    (a x : AxisPoint f) :
    (sqrtUpperFormula (0 : Fin 4) 1 2 3).eval
      (Fin.cons x.1 ![f.O, f.I, f.J, a.1]) ↔
      AxisNonneg f a ∧ AxisNonneg f x ∧
        ∃ s : AxisPoint f,
          MulGraph f x x s ∧ (a = s ∨ Bet f.O a.1 s.1) := by
  have hsem :
      (sqrtUpperFormula (0 : Fin 4) 1 2 3).eval
        (Fin.cons x.1 ![f.O, f.I, f.J, a.1]) ↔
      (Col f.O f.I a.1 ∧ (a.1 = f.O ∨ Out f.O f.I a.1)) ∧
      (Col f.O f.I x.1 ∧ (x.1 = f.O ∨ Out f.O f.I x.1)) ∧
      ∃ s : Point, Col f.O f.I s ∧
        RawMulGraph f.O f.I f.J x.1 x.1 s ∧
        (a.1 = s ∨ Bet f.O a.1 s) := by
    simpa using (sqrtUpperFormula_eval
      (0 : Fin 4) 1 2 3 x.1 ![f.O, f.I, f.J, a.1])
  rw [hsem]
  constructor
  · rintro ⟨⟨_, ha⟩, ⟨_, hx⟩, s, hscol, hsraw, hle⟩
    let sa : AxisPoint f := ⟨s, hscol⟩
    refine ⟨(axis_nonneg_iff_ray_or_origin f a).mpr ha,
      (axis_nonneg_iff_ray_or_origin f x).mpr hx,
      sa, (rawMulGraph_axis_iff f x x sa).mp hsraw, ?_⟩
    rcases hle with heq | hbet
    · exact Or.inl (Subtype.ext heq)
    · exact Or.inr hbet
  · rintro ⟨ha, hx, s, hmul, hle⟩
    refine ⟨⟨a.2, (axis_nonneg_iff_ray_or_origin f a).mp ha⟩,
      ⟨x.2, (axis_nonneg_iff_ray_or_origin f x).mp hx⟩,
      s.1, s.2, (rawMulGraph_axis_iff f x x s).mpr hmul, ?_⟩
    rcases hle with heq | hbet
    · exact Or.inl (congrArg Subtype.val heq)
    · exact Or.inr hbet

/-! ## Algebraic expression trees, without a pre-existing field

An expression is a finite formal tree. Its semantics is a relation in the
primitive Tarski language, not evaluation in some previously chosen field.
`scalarExprFormula` compiles the tree into a *single finite first-order formula*.
Each internal addition or multiplication node introduces two point witnesses.
The compiler never quantifies over functions or sets.
-/

inductive ScalarExpr (n : Nat) where
  | var : Fin n → ScalarExpr n
  | zero : ScalarExpr n
  | one : ScalarExpr n
  | add : ScalarExpr n → ScalarExpr n → ScalarExpr n
  | mul : ScalarExpr n → ScalarExpr n → ScalarExpr n
  deriving Repr

/-- Relational semantics of an algebraic expression in the point language.
    This is deliberately relational until totality and uniqueness of the
    parallel-line constructions have been established. -/
def ScalarExpr.geomValue (O I J : Point) {n : Nat}
    (ρ : Fin n → Point) : ScalarExpr n → Point → Prop
  | .var v, z => Col O I z ∧ z = ρ v
  | .zero, z => Col O I z ∧ z = O
  | .one, z => Col O I z ∧ z = I
  | .add p q, z =>
      Col O I z ∧ ∃ a b : Point,
        ScalarExpr.geomValue O I J ρ p a ∧
        ScalarExpr.geomValue O I J ρ q b ∧
        RawAddGraph O I J a b z
  | .mul p q, z =>
      Col O I z ∧ ∃ a b : Point,
        ScalarExpr.geomValue O I J ρ p a ∧
        ScalarExpr.geomValue O I J ρ q b ∧
        RawMulGraph O I J a b z

/-- Compilation into the language of Tarski's A13 scheme.
    `vars` gives the current de Bruijn indices of the free scalar variables.
    For binary nodes, the left witness is index 1 and right witness index 0;
    every existing free variable is shifted twice. -/
def scalarExprFormula {n m : Nat} (o i j z : Fin m)
    (vars : Fin n → Fin m) : ScalarExpr n → Formula m
  | .var v => .conj (colFormula o i z) (.equal z (vars v))
  | .zero => .conj (colFormula o i z) (.equal z o)
  | .one => .conj (colFormula o i z) (.equal z i)
  | .add p q =>
      .conj (colFormula o i z) (.ex (.ex
        (.conj
          (scalarExprFormula o.succ.succ i.succ.succ j.succ.succ 1
            (fun v => (vars v).succ.succ) p)
          (.conj
            (scalarExprFormula o.succ.succ i.succ.succ j.succ.succ 0
              (fun v => (vars v).succ.succ) q)
            (addGraphFormula o.succ.succ i.succ.succ j.succ.succ
              1 0 z.succ.succ)))))
  | .mul p q =>
      .conj (colFormula o i z) (.ex (.ex
        (.conj
          (scalarExprFormula o.succ.succ i.succ.succ j.succ.succ 1
            (fun v => (vars v).succ.succ) p)
          (.conj
            (scalarExprFormula o.succ.succ i.succ.succ j.succ.succ 0
              (fun v => (vars v).succ.succ) q)
            (mulGraphFormula o.succ.succ i.succ.succ j.succ.succ
              1 0 z.succ.succ)))))

/-- Generic syntax-to-semantics theorem for all expression trees, including
    those used to encode polynomials. This theorem requires no field laws. -/
theorem scalarExprFormula_eval {n : Nat} (e : ScalarExpr n) :
    ∀ (m : Nat) (o i j z : Fin m) (vars : Fin n → Fin m)
      (ρ : Fin m → Point),
      (scalarExprFormula o i j z vars e).eval ρ ↔
        e.geomValue (ρ o) (ρ i) (ρ j) (fun v => ρ (vars v)) (ρ z) := by
  induction e with
  | var v =>
      intro m o i j z vars ρ
      simp [scalarExprFormula, ScalarExpr.geomValue, Formula.eval,
        colFormula_eval]
  | zero =>
      intro m o i j z vars ρ
      simp [scalarExprFormula, ScalarExpr.geomValue, Formula.eval,
        colFormula_eval]
  | one =>
      intro m o i j z vars ρ
      simp [scalarExprFormula, ScalarExpr.geomValue, Formula.eval,
        colFormula_eval]
  | add p q ihp ihq =>
      intro m o i j z vars ρ
      simp [scalarExprFormula, ScalarExpr.geomValue, Formula.eval,
        colFormula_eval, ihp, ihq, addGraphFormula_raw_eval,
        Fin.cons_zero, Fin.cons_succ]
  | mul p q ihp ihq =>
      intro m o i j z vars ρ
      simp [scalarExprFormula, ScalarExpr.geomValue, Formula.eval,
        colFormula_eval, ihp, ihq, mulGraphFormula_raw_eval,
        Fin.cons_zero, Fin.cons_succ]

/-- Coefficients are ordered from constant term to highest degree;
    `foldr` is the finite Horner construction a₀ + x*(a₁ + x*(...)). -/
def hornerExpr {n : Nat} (x : ScalarExpr n)
    (coefficients : List (ScalarExpr n)) : ScalarExpr n :=
  coefficients.foldr (fun a rest => .add a (.mul x rest)) .zero

/-- A polynomial-root equation translated into one first-order formula.
    The input and every intermediate algebraic witness are constrained to OI.
    Coefficients are free points, not ambient field coefficients. -/
def polynomialRootFormula {n : Nat} (o i j x : Fin n)
    (coefficients : List (Fin n)) : Formula n :=
  .conj (colFormula o i x)
    (scalarExprFormula o i j o (fun v => v)
      (hornerExpr (.var x) (coefficients.map ScalarExpr.var)))

/-- The variable x is existentially quantified; coefficients remain parameters.
    It is the first-order claim that a particular polynomial has a root. -/
def polynomialHasRootFormula {n : Nat} (o i j : Fin n)
    (coefficients : List (Fin n)) : Formula n :=
  .ex (polynomialRootFormula o.succ i.succ j.succ 0
    (coefficients.map Fin.succ))

/-- The formula describes a root of the relational Horner expression;
    no pre-existing field interpretation is used. -/
theorem polynomialRootFormula_eval {n : Nat} (o i j x : Fin n)
    (coefficients : List (Fin n)) (ρ : Fin n → Point) :
    (polynomialRootFormula o i j x coefficients).eval ρ ↔
      Col (ρ o) (ρ i) (ρ x) ∧
      (hornerExpr (.var x) (coefficients.map ScalarExpr.var)).geomValue
        (ρ o) (ρ i) (ρ j) ρ (ρ o) := by
  simp [polynomialRootFormula, Formula.eval, colFormula_eval,
    scalarExprFormula_eval]

/-- A point on the negative ray is strictly opposite to the positive unit. -/
def negativePointFormula {n : Nat} (o i x : Fin n) : Formula n :=
  .conj (colFormula o i x)
    (.conj (.neg (.equal x o)) (.bet x o i))

/-- A first-order polynomial sign predicate; the value is a fresh point
    variable, and positivity is defined by betweenness. -/
def polynomialPositiveFormula {n : Nat} (o i j x : Fin n)
    (coefficients : List (Fin n)) : Formula n :=
  .conj (colFormula o i x)
    (.ex (.conj
      (scalarExprFormula o.succ i.succ j.succ 0 (fun v => v.succ)
        (hornerExpr (.var x) (coefficients.map ScalarExpr.var)))
      (outFormula o.succ i.succ 0)))

/-- The negative-value predicate needed for the polynomial IVT cut. -/
def polynomialNegativeFormula {n : Nat} (o i j x : Fin n)
    (coefficients : List (Fin n)) : Formula n :=
  .conj (colFormula o i x)
    (.ex (.conj
      (scalarExprFormula o.succ i.succ j.succ 0 (fun v => v.succ)
        (hornerExpr (.var x) (coefficients.map ScalarExpr.var)))
      (negativePointFormula o.succ i.succ 0)))

/-! ### Ordered cuts for arbitrary polynomial sign changes

For an odd-degree polynomial, the negative and positive value sets need not
be separated: signs can alternate at several roots. We therefore specify
an interval [l,r] with a negative value at l and a positive value at r,
and build the *initial all-negative prefix* of that interval. Its complement
inside [l,r] is an upper set. This avoids any false monotonicity assumption
about the polynomial itself. Root existence then requires the elementary
order-field argument that the polynomial cannot jump across zero.
-/

/-- On [l,r], every point t between l and x has negative polynomial value.
    This is a finite first-order formula; the universal point quantifier
    comes only from `Formula.all`. -/
def polynomialNegativePrefixFormula {n : Nat}
    (o i j l r x : Fin n) (coefficients : List (Fin n)) : Formula n :=
  .conj (colFormula o i x)
    (.conj (.bet l x r)
      (.all
        (.impl (.bet l.succ 0 x.succ)
          (polynomialNegativeFormula o.succ i.succ j.succ 0
            (coefficients.map Fin.succ)))))

/-- The lower cut consists of points in the negative prefix. -/
def polynomialLowerCutFormula {n : Nat}
    (o i j l r : Fin n) (coefficients : List (Fin n)) :
    Formula (n + 1) :=
  polynomialNegativePrefixFormula o.succ i.succ j.succ
    l.succ r.succ 0 (coefficients.map Fin.succ)

/-- The upper cut is the complement of the prefix *within the interval*;
    in particular it is not simply the set where the polynomial is positive. -/
def polynomialUpperCutFormula {n : Nat}
    (o i j l r : Fin n) (coefficients : List (Fin n)) :
    Formula (n + 1) :=
  .conj (colFormula o.succ i.succ 0)
    (.conj (.bet l.succ 0 r.succ)
      (.neg (polynomialLowerCutFormula o i j l r coefficients)))

/-- The two bounded polynomial cuts cannot overlap, purely by syntax.
    Ordered separation remains a separate geometrical proof obligation. -/
theorem polynomial_cuts_disjoint {n : Nat}
    (o i j l r : Fin n) (coefficients : List (Fin n))
    (params : Fin n → Point) (x : Point) :
    ¬ ((polynomialLowerCutFormula o i j l r coefficients).eval
        (Fin.cons x params) ∧
       (polynomialUpperCutFormula o i j l r coefficients).eval
        (Fin.cons x params)) := by
  rintro ⟨hL, hU⟩
  exact hU.2.2 hL

/-- The negative initial segment of an interval. -/
def IntervalNegativePrefix
    (L R : Point) (negative : Point → Prop)
    (X : Point) : Prop :=
  Bet L X R ∧
  ∀ T : Point, Bet L T X → negative T

/-- The initial negative interval contains its left endpoint whenever
    the polynomial sign predicate holds there. This is a direct consequence
    of Tarski's between-identity axiom and needs no field arithmetic. -/
theorem intervalNegativePrefix_contains_left
    (L R : Point) (negative : Point → Prop)
    (hnegL : negative L) :
    IntervalNegativePrefix L R negative L := by
  refine ⟨bet_start L R, ?_⟩
  intro T hTL
  have hT : L = T := between_identity L T hTL
  simpa [← hT] using hnegL

/-- The negative prefix is downward closed.
    This requires only betweenness transitivity. -/
theorem intervalNegativePrefix_downward
    {L R X Y : Point} {negative : Point → Prop}
    (hX : IntervalNegativePrefix L R negative X)
    (hYX : Bet L Y X) :
    IntervalNegativePrefix L R negative Y := by
  refine ⟨bet_extend hYX hX.1, ?_⟩
  intro T hTY
  exact hX.2 T (bet_extend hTY hYX)

/-- A point in the complement cannot precede
    a point in the negative prefix. -/
theorem intervalNegativePrefix_not_reverse
    {L R X Y : Point} {negative : Point → Prop}
    (hX : IntervalNegativePrefix L R negative X)
    (hY : ¬ IntervalNegativePrefix L R negative Y) :
    ¬ Bet L Y X := by
  intro hYX
  exact hY (intervalNegativePrefix_downward hX hYX)

/-- Inner connectivity converts downward closure into
    the ordered-separation condition. -/
theorem intervalNegativePrefix_ordered
    (L R : Point) (negative : Point → Prop)
    (hconn : ∀ X Y : Point,
      Bet L X R →
      Bet L Y R →
      Bet L X Y ∨ Bet L Y X)
    {X Y : Point}
    (hX : IntervalNegativePrefix L R negative X)
    (hY : Bet L Y R ∧
      ¬ IntervalNegativePrefix L R negative Y) :
    Bet L X Y := by
  rcases hconn X Y hX.1 hY.1 with hXY | hYX
  · exact hXY
  · exact False.elim
      (intervalNegativePrefix_not_reverse hX hY.2 hYX)

/-- Ordered separation for the actual first-order
    polynomial cuts, reduced to downward closure and
    inner connectivity. -/
theorem polynomial_cut_ordered_of_downward
    {n : Nat}
    (o i j l r : Fin n)
    (coefficients : List (Fin n))
    (params : Fin n → Point)
    (hdown : ∀ X Y : Point,
      (polynomialLowerCutFormula
        o i j l r coefficients).eval
          (Fin.cons X params) →
      Bet (params l) Y X →
      (polynomialLowerCutFormula
        o i j l r coefficients).eval
          (Fin.cons Y params))
    (hconn : ∀ X Y : Point,
      Bet (params l) X (params r) →
      Bet (params l) Y (params r) →
      Bet (params l) X Y ∨ Bet (params l) Y X) :
    ∃ A : Point, ∀ X Y : Point,
      (polynomialLowerCutFormula
        o i j l r coefficients).eval
          (Fin.cons X params) →
      (polynomialUpperCutFormula
        o i j l r coefficients).eval
          (Fin.cons Y params) →
      Bet A X Y := by
  refine ⟨params l, ?_⟩
  intro X Y hX hY

  have hXinterval :
      Bet (params l) X (params r) :=
    hX.2.1

  have hYinterval :
      Bet (params l) Y (params r) :=
    hY.2.1

  rcases hconn X Y hXinterval hYinterval with
    hXY | hYX
  · exact hXY
  · exact False.elim
      (hY.2.2 (hdown X Y hX hYX))

/-- A13 can be instantiated for each finite polynomial coefficient list,
    once the actual ordered-separation antecedent has been proved. -/
theorem polynomial_cut_has_separator [ContinuousPlane Point]
    {n : Nat} (o i j l r : Fin n)
    (coefficients : List (Fin n)) (params : Fin n → Point)
    (hsep : ∃ A : Point, ∀ X Y : Point,
      (polynomialLowerCutFormula o i j l r coefficients).eval
        (Fin.cons X params) →
      (polynomialUpperCutFormula o i j l r coefficients).eval
        (Fin.cons Y params) → Bet A X Y) :
    ∃ B : Point, ∀ X Y : Point,
      (polynomialLowerCutFormula o i j l r coefficients).eval
        (Fin.cons X params) →
      (polynomialUpperCutFormula o i j l r coefficients).eval
        (Fin.cons Y params) → Bet X B Y := by
  exact ContinuousPlane.first_order_continuity n
    (polynomialLowerCutFormula o i j l r coefficients)
    (polynomialUpperCutFormula o i j l r coefficients)
    params hsep

/-- Once downward closure and line-segment connectivity are established,
    the first-order continuity axiom A13 supplies a separating cut point.
    No field operations occur in this deduction. -/
theorem polynomial_cut_A13_of_downward_and_connectivity
    [ContinuousPlane Point]
    {n : Nat} (o i j l r : Fin n)
    (coefficients : List (Fin n)) (params : Fin n → Point)
    (hdown : ∀ X Y : Point,
      (polynomialLowerCutFormula o i j l r coefficients).eval
        (Fin.cons X params) →
      Bet (params l) Y X →
      (polynomialLowerCutFormula o i j l r coefficients).eval
        (Fin.cons Y params))
    (hconn : ∀ X Y : Point,
      Bet (params l) X (params r) →
      Bet (params l) Y (params r) →
      Bet (params l) X Y ∨ Bet (params l) Y X) :
    ∃ B : Point, ∀ X Y : Point,
      (polynomialLowerCutFormula o i j l r coefficients).eval
        (Fin.cons X params) →
      (polynomialUpperCutFormula o i j l r coefficients).eval
        (Fin.cons Y params) → Bet X B Y := by
  exact polynomial_cut_has_separator o i j l r coefficients params
    (polynomial_cut_ordered_of_downward o i j l r coefficients
      params hdown hconn)

/-- Horner evaluation does not depend on the extra variable between the
    evaluation argument and the coefficient parameters. -/
theorem hornerExpr_ignore_middle {n : Nat}
    (O I J t X Y : Point)
    (params : Fin n → Point)
    (coefficients : List (Fin n)) (z : Point) :
    (hornerExpr (.var (0 : Fin (n + 2)))
      (coefficients.map
        (fun c => ScalarExpr.var c.succ.succ))).geomValue
        O I J (Fin.cons t (Fin.cons X params)) z ↔
    (hornerExpr (.var (0 : Fin (n + 2)))
      (coefficients.map
        (fun c => ScalarExpr.var c.succ.succ))).geomValue
        O I J (Fin.cons t (Fin.cons Y params)) z := by
  induction coefficients generalizing z with
  | nil =>
      rfl
  | cons c cs ih =>
      change
        (ScalarExpr.add (.var c.succ.succ)
          (.mul (.var 0)
            (hornerExpr (.var (0 : Fin (n + 2)))
              (cs.map
                (fun v => ScalarExpr.var v.succ.succ))))).geomValue
            O I J (Fin.cons t (Fin.cons X params)) z ↔
        (ScalarExpr.add (.var c.succ.succ)
          (.mul (.var 0)
            (hornerExpr (.var (0 : Fin (n + 2)))
              (cs.map
                (fun v => ScalarExpr.var v.succ.succ))))).geomValue
            O I J (Fin.cons t (Fin.cons Y params)) z
      simp only [ScalarExpr.geomValue,
        Fin.cons_zero, Fin.cons_succ, ih]

/-- Meaning of a negative polynomial value in the one-sorted plane. -/
theorem polynomialNegativeFormula_semantics {n : Nat}
    (o i j x : Fin n)
    (coefficients : List (Fin n))
    (ρ : Fin n → Point) :
    (polynomialNegativeFormula o i j x coefficients).eval ρ ↔
      Col (ρ o) (ρ i) (ρ x) ∧
      ∃ v : Point,
        (hornerExpr (.var x)
          (coefficients.map ScalarExpr.var)).geomValue
            (ρ o) (ρ i) (ρ j) ρ v ∧
        Col (ρ o) (ρ i) v ∧
        v ≠ ρ o ∧ Bet v (ρ o) (ρ i) := by
  simp [polynomialNegativeFormula, Formula.eval,
    scalarExprFormula_eval, negativePointFormula,
    colFormula_eval, Fin.cons_zero, Fin.cons_succ]

theorem polynomialNegativeFormula_ignore_middle {n : Nat}
    (o i j : Fin n)
    (coefficients : List (Fin n))
    (params : Fin n → Point)
    (t X Y : Point) :
    (polynomialNegativeFormula
      o.succ.succ i.succ.succ j.succ.succ 0
      ((coefficients.map Fin.succ).map Fin.succ)).eval
        (Fin.cons t (Fin.cons X params)) ↔
    (polynomialNegativeFormula
      o.succ.succ i.succ.succ j.succ.succ 0
      ((coefficients.map Fin.succ).map Fin.succ)).eval
        (Fin.cons t (Fin.cons Y params)) := by
  simp only [polynomialNegativeFormula_semantics,
    Fin.cons_zero, Fin.cons_succ,
    List.map_map, Function.comp_def]
  constructor
  · rintro ⟨hcol, v, hv, hn⟩
    refine ⟨hcol, v, ?_, hn⟩
    exact (hornerExpr_ignore_middle
      (params o) (params i) (params j)
      t X Y params coefficients v).mp hv
  · rintro ⟨hcol, v, hv, hn⟩
    refine ⟨hcol, v, ?_, hn⟩
    exact (hornerExpr_ignore_middle
      (params o) (params i) (params j)
      t X Y params coefficients v).mpr hv

theorem polynomialLowerCutFormula_prefix_eval {n : Nat}
    (o i j l r : Fin n)
    (coefficients : List (Fin n))
    (params : Fin n → Point)
    (X : Point) :
    (polynomialLowerCutFormula
      o i j l r coefficients).eval
        (Fin.cons X params) ↔
      Col (params o) (params i) X ∧
      Bet (params l) X (params r) ∧
      ∀ T : Point,
        Bet (params l) T X →
        (polynomialNegativeFormula
          o.succ.succ i.succ.succ j.succ.succ 0
          ((coefficients.map Fin.succ).map Fin.succ)).eval
            (Fin.cons T (Fin.cons X params)) := by
  rfl

theorem polynomialLowerCutFormula_downward {n : Nat}
    (o i j l r : Fin n)
    (coefficients : List (Fin n))
    (params : Fin n → Point)
    (X Y : Point)
    (hX : (polynomialLowerCutFormula
      o i j l r coefficients).eval
        (Fin.cons X params))
    (hYX : Bet (params l) Y X) :
    (polynomialLowerCutFormula
      o i j l r coefficients).eval
        (Fin.cons Y params) := by

  obtain ⟨_, hXR, hprefix⟩ :=
    (polynomialLowerCutFormula_prefix_eval
      o i j l r coefficients params X).mp hX

  have hnegativeY := hprefix Y hYX

  have hYaxis : Col (params o) (params i) Y :=
    ((polynomialNegativeFormula_semantics
      o.succ.succ i.succ.succ j.succ.succ 0
      ((coefficients.map Fin.succ).map Fin.succ)
      (Fin.cons Y (Fin.cons X params))).mp
        hnegativeY).1

  apply (polynomialLowerCutFormula_prefix_eval
    o i j l r coefficients params Y).mpr

  refine ⟨hYaxis, bet_extend hYX hXR, ?_⟩

  intro T hTY
  have hTX : Bet (params l) T X :=
    bet_extend hTY hYX

  exact (polynomialNegativeFormula_ignore_middle
    o i j coefficients params T X Y).mp
      (hprefix T hTX)

/-- A13's polynomial cut condition reduced to inner connectivity alone. -/
theorem polynomial_cut_A13_of_connectivity
    [ContinuousPlane Point]
    {n : Nat}
    (o i j l r : Fin n)
    (coefficients : List (Fin n))
    (params : Fin n → Point)
    (hconn : ∀ X Y : Point,
      Bet (params l) X (params r) →
      Bet (params l) Y (params r) →
      Bet (params l) X Y ∨
      Bet (params l) Y X) :
    ∃ B : Point, ∀ X Y : Point,
      (polynomialLowerCutFormula
        o i j l r coefficients).eval
          (Fin.cons X params) →
      (polynomialUpperCutFormula
        o i j l r coefficients).eval
          (Fin.cons Y params) →
      Bet X B Y := by
  exact polynomial_cut_A13_of_downward_and_connectivity
    o i j l r coefficients params
    (fun X Y hX hYX =>
      polynomialLowerCutFormula_downward
        o i j l r coefficients params X Y hX hYX)
    hconn

/-! ## Direct A13 application via the definable upper-bound set

An upper cut can be defined as all upper bounds of the lower prefix.
This makes the separation premise of A13 hold by definition; inner
connectivity is not needed merely to invoke the continuity scheme.
-/

/-- Renaming of free point variables, including beneath quantifiers. -/
def Formula.rename {n m : Nat}
    (σ : Fin n → Fin m) : Formula n → Formula m
  | .equal a b => .equal (σ a) (σ b)
  | .bet a b c => .bet (σ a) (σ b) (σ c)
  | .cong a b c d => .cong (σ a) (σ b) (σ c) (σ d)
  | .neg p => .neg (p.rename σ)
  | .conj p q => .conj (p.rename σ) (q.rename σ)
  | .disj p q => .disj (p.rename σ) (q.rename σ)
  | .impl p q => .impl (p.rename σ) (q.rename σ)
  | .all p =>
      .all (p.rename (Fin.cons 0 (fun v => (σ v).succ)))
  | .ex p =>
      .ex (p.rename (Fin.cons 0 (fun v => (σ v).succ)))

omit [Plane Point] in
private theorem formula_rename_binder_env {n m : Nat}
    (σ : Fin n → Fin m) (ρ : Fin m → Point) (X : Point) :
    ∀ v : Fin (n + 1),
      (Fin.cons (α := fun _ => Point) X ρ)
        ((Fin.cons (α := fun _ => Fin (m + 1)) (0 : Fin (m + 1))
          (fun k : Fin n => (σ k).succ)) v) =
      (Fin.cons (α := fun _ => Point) X (ρ ∘ σ)) v := by
  intro v
  cases v using Fin.cases with
  | zero => rfl
  | succ k => rfl

omit [Plane Point] in
private theorem formula_rename_binder_env_eq {n m : Nat}
    (σ : Fin n → Fin m) (ρ : Fin m → Point) (X : Point) :
    (fun v : Fin (n + 1) =>
      (Fin.cons (α := fun _ => Point) X ρ)
        ((Fin.cons (α := fun _ => Fin (m + 1)) (0 : Fin (m + 1))
          (fun k : Fin n => (σ k).succ)) v)) =
    (Fin.cons (α := fun _ => Point) X (ρ ∘ σ)) := by
  funext v
  exact formula_rename_binder_env σ ρ X v

theorem Formula.rename_eval {n : Nat}
    (p : Formula n) :
    ∀ {m : Nat} (σ : Fin n → Fin m) (ρ : Fin m → Point),
      (p.rename σ).eval ρ ↔ p.eval (fun v => ρ (σ v)) := by
  induction p with
  | equal a b =>
      intro m σ ρ
      rfl
  | bet a b c =>
      intro m σ ρ
      rfl
  | cong a b c d =>
      intro m σ ρ
      rfl
  | neg p ih =>
      intro m σ ρ
      simpa only [Formula.rename, Formula.eval] using not_congr (ih σ ρ)
  | conj p q ihp ihq =>
      intro m σ ρ
      simp only [Formula.rename, Formula.eval, ihp σ ρ, ihq σ ρ]
  | disj p q ihp ihq =>
      intro m σ ρ
      simp only [Formula.rename, Formula.eval, ihp σ ρ, ihq σ ρ]
  | impl p q ihp ihq =>
      intro m σ ρ
      simp only [Formula.rename, Formula.eval, ihp σ ρ, ihq σ ρ]
  | all p ih =>
      intro m σ ρ
      change
        (∀ X : Point,
          (p.rename
            (Fin.cons (0 : Fin (m + 1))
              (fun v => (σ v).succ))).eval
                (Fin.cons X ρ)) ↔
        (∀ X : Point, p.eval (Fin.cons X (fun v => ρ (σ v))))
      apply forall_congr'
      intro X
      simpa only [formula_rename_binder_env_eq, Function.comp_def] using
        (ih (Fin.cons (0 : Fin (m + 1))
          (fun v => (σ v).succ)) (Fin.cons X ρ))
  | ex p ih =>
      intro m σ ρ
      change
        (∃ X : Point,
          (p.rename
            (Fin.cons (0 : Fin (m + 1))
              (fun v => (σ v).succ))).eval
                (Fin.cons X ρ)) ↔
        (∃ X : Point, p.eval (Fin.cons X (fun v => ρ (σ v))))
      constructor
      · rintro ⟨X, hX⟩
        refine ⟨X, ?_⟩
        simpa only [formula_rename_binder_env_eq, Function.comp_def] using
          ((ih (Fin.cons (0 : Fin (m + 1))
            (fun v => (σ v).succ)) (Fin.cons X ρ)).mp hX)
      · rintro ⟨X, hX⟩
        refine ⟨X, ?_⟩
        apply (ih (Fin.cons (0 : Fin (m + 1))
          (fun v => (σ v).succ)) (Fin.cons X ρ)).mpr
        simpa only [formula_rename_binder_env_eq, Function.comp_def] using hX

/-- The first-order definable set of upper bounds of `lower`. -/
def upperBoundsFormula {n : Nat}
    (l : Fin n) (lower : Formula (n + 1)) : Formula (n + 1) :=
  .all (.impl
    (lower.rename
      (Fin.cons (0 : Fin (n + 2))
        (fun v : Fin n => v.succ.succ)))
    (.bet l.succ.succ 0 1))

theorem upperBoundsFormula_eval {n : Nat}
    (l : Fin n) (lower : Formula (n + 1))
    (params : Fin n → Point) (Y : Point) :
    (upperBoundsFormula l lower).eval (Fin.cons Y params) ↔
    ∀ X : Point, lower.eval (Fin.cons X params) → Bet (params l) X Y := by
  have hrename (X : Point) :
      (lower.rename
        (Fin.cons (0 : Fin (n + 2))
          (fun v : Fin n => v.succ.succ))).eval
          (Fin.cons X (Fin.cons Y params)) ↔
      lower.eval (Fin.cons X params) := by
    have henv : ∀ v : Fin (n + 1),
        (Fin.cons (α := fun _ => Point) X
          (Fin.cons (α := fun _ => Point) Y params))
          ((Fin.cons (α := fun _ => Fin (n + 2)) (0 : Fin (n + 2))
            (fun k : Fin n => k.succ.succ)) v) =
        (Fin.cons (α := fun _ => Point) X params) v := by
      intro v
      cases v using Fin.cases with
      | zero => rfl
      | succ k => rfl
    have hrew := (Formula.rename_eval lower
        (Fin.cons (0 : Fin (n + 2))
          (fun v : Fin n => v.succ.succ))
        (Fin.cons X (Fin.cons Y params)))
    simpa only [henv] using hrew
  change
    (∀ X : Point,
      (lower.rename
        (Fin.cons (0 : Fin (n + 2))
          (fun v : Fin n => v.succ.succ))).eval
            (Fin.cons X (Fin.cons Y params)) →
      Bet (params l) X Y) ↔
    (∀ X : Point,
      lower.eval (Fin.cons X params) → Bet (params l) X Y)
  simp only [hrename]

/-- A13 applies to the lower set and its *definable upper bounds*. -/
theorem upperBounds_cut_A13
    [ContinuousPlane Point] {n : Nat}
    (l : Fin n) (lower : Formula (n + 1))
    (params : Fin n → Point) :
    ∃ B : Point, ∀ X Y : Point,
      lower.eval (Fin.cons X params) →
      (upperBoundsFormula l lower).eval (Fin.cons Y params) →
      Bet X B Y := by
  apply ContinuousPlane.first_order_continuity
    n lower (upperBoundsFormula l lower) params
  refine ⟨params l, ?_⟩
  intro X Y hX hY
  exact ((upperBoundsFormula_eval l lower params Y).mp hY) X hX

/-- A13 produces the *least* definable upper bound, not merely a point
    between a member of the lower set and one of its upper bounds.
    The decisive step is the Tarski-derived betweenness rule
    `bet_inner_trans`: from `Bet L X R` and `Bet X B R` infer `Bet L X B`.
    No ambient field, numerical coordinate, or topological limit is used. -/
theorem upperBounds_cut_A13_least_upper_bound
    [ContinuousPlane Point] {n : Nat}
    (l : Fin n) (lower : Formula (n + 1))
    (params : Fin n → Point) (R : Point)
    (hL : lower.eval (Fin.cons (params l) params))
    (hR : (upperBoundsFormula l lower).eval (Fin.cons R params)) :
    ∃ B : Point,
      Bet (params l) B R ∧
      (upperBoundsFormula l lower).eval (Fin.cons B params) ∧
      ∀ Y : Point,
        (upperBoundsFormula l lower).eval (Fin.cons Y params) →
        Bet (params l) B Y := by
  obtain ⟨B, hsep⟩ := upperBounds_cut_A13 l lower params
  have hbetween : Bet (params l) B R :=
    hsep (params l) R hL hR
  have hupper :
      (upperBoundsFormula l lower).eval (Fin.cons B params) := by
    apply (upperBoundsFormula_eval l lower params B).mpr
    intro X hX
    have hLXR : Bet (params l) X R :=
      ((upperBoundsFormula_eval l lower params R).mp hR) X hX
    have hXBR : Bet X B R := hsep X R hX hR
    exact bet_inner_trans hLXR hXBR
  refine ⟨B, hbetween, hupper, ?_⟩
  intro Y hY
  exact hsep (params l) Y hL hY

/-- Uniqueness of the supremum produced by first-order continuity.
    Unlike an arbitrary separating point, a least upper bound cannot be
    chosen in two different ways.  This is proved from Tarski betweenness
    antisymmetry, without an ambient linear order or coordinate field. -/
theorem upperBounds_cut_A13_existsUnique
    [ContinuousPlane Point] {n : Nat}
    (l : Fin n) (lower : Formula (n + 1))
    (params : Fin n → Point) (R : Point)
    (hL : lower.eval (Fin.cons (params l) params))
    (hR : (upperBoundsFormula l lower).eval (Fin.cons R params)) :
    ∃! B : Point,
      Bet (params l) B R ∧
      (upperBoundsFormula l lower).eval (Fin.cons B params) ∧
      ∀ Y : Point,
        (upperBoundsFormula l lower).eval (Fin.cons Y params) →
        Bet (params l) B Y := by
  obtain ⟨B, hBR, hBupper, hBleast⟩ :=
    upperBounds_cut_A13_least_upper_bound l lower params R hL hR
  refine ⟨B, ⟨hBR, hBupper, hBleast⟩, ?_⟩
  intro B' ⟨_, hB'upper, hB'least⟩
  have hBB' : Bet (params l) B B' := hBleast B' hB'upper
  have hB'B : Bet (params l) B' B := hB'least B hBupper
  exact (bet_same_origin_antisymm hBB' hB'B).symm

/-- The right endpoint belongs to the set of upper bounds. -/
theorem polynomialUpperBounds_contains_right
    {n : Nat} (o i j l r : Fin n)
    (coefficients : List (Fin n)) (params : Fin n → Point) :
    (upperBoundsFormula l
      (polynomialLowerCutFormula o i j l r coefficients)).eval
        (Fin.cons (params r) params) := by
  apply (upperBoundsFormula_eval l
    (polynomialLowerCutFormula o i j l r coefficients)
    params (params r)).mpr
  intro X hX
  exact ((polynomialLowerCutFormula_prefix_eval
    o i j l r coefficients params X).mp hX).2.1

/-- Direct polynomial A13 cut, with neither `hdown` nor `hconn`. -/
theorem polynomial_cut_A13_direct
    [ContinuousPlane Point] {n : Nat}
    (o i j l r : Fin n)
    (coefficients : List (Fin n)) (params : Fin n → Point) :
    ∃ B : Point, ∀ X Y : Point,
      (polynomialLowerCutFormula o i j l r coefficients).eval
        (Fin.cons X params) →
      (upperBoundsFormula l
        (polynomialLowerCutFormula o i j l r coefficients)).eval
          (Fin.cons Y params) → Bet X B Y := by
  exact upperBounds_cut_A13 l
    (polynomialLowerCutFormula o i j l r coefficients) params

/-- If the left endpoint is in the lower set, the A13 cut point lies on
    the closed segment `LR` as well as separating every pair of cuts. -/
theorem polynomial_cut_A13_in_interval
    [ContinuousPlane Point] {n : Nat}
    (o i j l r : Fin n)
    (coefficients : List (Fin n)) (params : Fin n → Point)
    (hL : (polynomialLowerCutFormula o i j l r coefficients).eval
      (Fin.cons (params l) params)) :
    ∃ B : Point, Bet (params l) B (params r) ∧
      ∀ X Y : Point,
        (polynomialLowerCutFormula o i j l r coefficients).eval
          (Fin.cons X params) →
        (upperBoundsFormula l
          (polynomialLowerCutFormula o i j l r coefficients)).eval
            (Fin.cons Y params) → Bet X B Y := by
  obtain ⟨B, hB⟩ := polynomial_cut_A13_direct o i j l r coefficients params
  have hR := polynomialUpperBounds_contains_right o i j l r coefficients params
  exact ⟨B, hB (params l) (params r) hL hR, hB⟩

/-- For a polynomial's negative initial interval, A13 yields its least
    upper bound as a plane point in the closed segment `LR`. Proving that
    the point lies on axis `OI`, and then that its polynomial value is zero,
    requires subsequent Tarski-geometric and internal ordered-field lemmas. -/
theorem polynomial_cut_A13_least_upper_bound
    [ContinuousPlane Point] {n : Nat}
    (o i j l r : Fin n)
    (coefficients : List (Fin n)) (params : Fin n → Point)
    (hL : (polynomialLowerCutFormula o i j l r coefficients).eval
      (Fin.cons (params l) params)) :
    ∃ B : Point,
      Bet (params l) B (params r) ∧
      (upperBoundsFormula l
        (polynomialLowerCutFormula o i j l r coefficients)).eval
          (Fin.cons B params) ∧
      ∀ Y : Point,
        (upperBoundsFormula l
          (polynomialLowerCutFormula o i j l r coefficients)).eval
            (Fin.cons Y params) →
        Bet (params l) B Y := by
  exact upperBounds_cut_A13_least_upper_bound l
    (polynomialLowerCutFormula o i j l r coefficients) params
    (params r) hL
    (polynomialUpperBounds_contains_right o i j l r coefficients params)

/-- With a genuine left witness, the polynomial cut has a *unique* least
    upper bound on the segment LR. This fact will be used when the geometric
    field interpretation supplies the intermediate-value argument. -/
theorem polynomial_cut_A13_existsUnique
    [ContinuousPlane Point] {n : Nat}
    (o i j l r : Fin n)
    (coefficients : List (Fin n)) (params : Fin n → Point)
    (hL : (polynomialLowerCutFormula o i j l r coefficients).eval
      (Fin.cons (params l) params)) :
    ∃! B : Point,
      Bet (params l) B (params r) ∧
      (upperBoundsFormula l
        (polynomialLowerCutFormula o i j l r coefficients)).eval
          (Fin.cons B params) ∧
      ∀ Y : Point,
        (upperBoundsFormula l
          (polynomialLowerCutFormula o i j l r coefficients)).eval
            (Fin.cons Y params) →
        Bet (params l) B Y := by
  exact upperBounds_cut_A13_existsUnique l
    (polynomialLowerCutFormula o i j l r coefficients) params
    (params r) hL
    (polynomialUpperBounds_contains_right o i j l r coefficients params)

/-- A purely synthetic Horner graph on the interpreted axis. -/
def HornerGraph (f : Frame Point) (x : AxisPoint f) :
    List (AxisPoint f) → AxisPoint f → Prop
  | [], z => z = axisZero f
  | a :: rest, z =>
      ∃ t u : AxisPoint f,
        HornerGraph f x rest t ∧
        MulGraph f x t u ∧
        AddGraph f a u z

/-- Every geometric value of an expression lies on the scalar axis. -/
theorem ScalarExpr.geomValue_axis {n : Nat}
    (e : ScalarExpr n) (O I J : Point)
    (ρ : Fin n → Point) (z : Point)
    (h : e.geomValue O I J ρ z) :
    Col O I z := by
  cases e <;> exact h.1

/-- Relational Horner evaluation agrees with the geometric semantics
of the corresponding expression tree, without field axioms or totality. -/
theorem hornerExpr_geomValue_iff_HornerGraph
    (f : Frame Point) {n : Nat}
    (σ : Fin n → AxisPoint f)
    (x : Fin n) (coefficients : List (Fin n))
    (z : AxisPoint f) :
    (hornerExpr (.var x)
      (coefficients.map ScalarExpr.var)).geomValue
        f.O f.I f.J (fun v => (σ v).1) z.1 ↔
    HornerGraph f (σ x) (coefficients.map σ) z := by
  induction coefficients generalizing z with
  | nil =>
      change
        (Col f.O f.I z.1 ∧ z.1 = f.O) ↔
          z = axisZero f
      constructor
      · intro h
        exact Subtype.ext h.2
      · intro hz
        exact ⟨z.2, congrArg Subtype.val hz⟩

  | cons c cs ih =>
      change
        (Col f.O f.I z.1 ∧
          ∃ a b : Point,
            (Col f.O f.I a ∧ a = (σ c).1) ∧
            (Col f.O f.I b ∧
              ∃ p q : Point,
                (Col f.O f.I p ∧ p = (σ x).1) ∧
                (hornerExpr (.var x)
                  (cs.map ScalarExpr.var)).geomValue
                    f.O f.I f.J
                    (fun v => (σ v).1) q ∧
                RawMulGraph f.O f.I f.J p q b) ∧
            RawAddGraph f.O f.I f.J a b z.1)
        ↔
        ∃ t u : AxisPoint f,
          HornerGraph f (σ x) (cs.map σ) t ∧
          MulGraph f (σ x) t u ∧
          AddGraph f (σ c) u z

      constructor
      · rintro ⟨_, a, b, ⟨_, ha⟩,
          ⟨hb, p, q, ⟨_, hp⟩, hq, hmul⟩, hadd⟩

        have hqaxis : Col f.O f.I q :=
          ScalarExpr.geomValue_axis
            (hornerExpr (.var x)
              (cs.map ScalarExpr.var))
            f.O f.I f.J
            (fun v => (σ v).1) q hq

        let t : AxisPoint f := ⟨q, hqaxis⟩
        let u : AxisPoint f := ⟨b, hb⟩

        refine ⟨t, u, (ih t).mp hq, ?_, ?_⟩

        · apply (rawMulGraph_axis_iff f (σ x) t u).mp
          simpa [hp] using hmul

        · apply (rawAddGraph_axis_iff f (σ c) u z).mp
          simpa [ha] using hadd

      · rintro ⟨t, u, ht, hmul, hadd⟩

        refine ⟨z.2, (σ c).1, u.1,
          ⟨(σ c).2, rfl⟩, ?_, ?_⟩

        · refine ⟨u.2, (σ x).1, t.1,
            ⟨(σ x).2, rfl⟩,
            (ih t).mpr ht, ?_⟩

          exact
            (rawMulGraph_axis_iff f (σ x) t u).mpr hmul

        · exact
            (rawAddGraph_axis_iff f (σ c) u z).mpr hadd

/-- Horner evaluation depends only on the variable x
    and the coefficients occurring in the polynomial. -/
theorem hornerExpr_geomValue_of_agreement
    (f : Frame Point) {n : Nat}
    (ρ : Fin n → Point)
    (σ : Fin n → AxisPoint f)
    (x : Fin n)
    (hx : ρ x = (σ x).1) :
    ∀ (coefficients : List (Fin n)),
      (∀ c, c ∈ coefficients → ρ c = (σ c).1) →
      ∀ z : AxisPoint f,
        (hornerExpr (.var x)
          (coefficients.map ScalarExpr.var)).geomValue
            f.O f.I f.J ρ z.1 ↔
        HornerGraph f (σ x) (coefficients.map σ) z := by
  intro coefficients
  induction coefficients with
  | nil =>
      intro _ z
      change
        (Col f.O f.I z.1 ∧ z.1 = f.O) ↔
          z = axisZero f
      constructor
      · intro h
        exact Subtype.ext h.2
      · intro hz
        exact ⟨z.2, congrArg Subtype.val hz⟩

  | cons c cs ih =>
      intro hcoeff z

      have hc : ρ c = (σ c).1 :=
        hcoeff c (by simp)

      have htail :
          ∀ v, v ∈ cs → ρ v = (σ v).1 := by
        intro v hv
        exact hcoeff v (List.mem_cons_of_mem c hv)

      change
        (Col f.O f.I z.1 ∧
          ∃ a b : Point,
            (Col f.O f.I a ∧ a = ρ c) ∧
            (Col f.O f.I b ∧
              ∃ p q : Point,
                (Col f.O f.I p ∧ p = ρ x) ∧
                (hornerExpr (.var x)
                  (cs.map ScalarExpr.var)).geomValue
                    f.O f.I f.J ρ q ∧
                RawMulGraph f.O f.I f.J p q b) ∧
            RawAddGraph f.O f.I f.J a b z.1)
        ↔
        ∃ t u : AxisPoint f,
          HornerGraph f (σ x) (cs.map σ) t ∧
          MulGraph f (σ x) t u ∧
          AddGraph f (σ c) u z

      constructor
      · rintro ⟨_, a, b, ⟨_, ha⟩,
          ⟨hb, p, q, ⟨_, hp⟩, hq, hmul⟩, hadd⟩

        have hqaxis : Col f.O f.I q :=
          ScalarExpr.geomValue_axis
            (hornerExpr (.var x)
              (cs.map ScalarExpr.var))
            f.O f.I f.J ρ q hq

        let t : AxisPoint f := ⟨q, hqaxis⟩
        let u : AxisPoint f := ⟨b, hb⟩

        refine ⟨t, u, (ih htail t).mp hq, ?_, ?_⟩

        · apply (rawMulGraph_axis_iff f (σ x) t u).mp
          simpa [hp, hx] using hmul

        · apply (rawAddGraph_axis_iff f (σ c) u z).mp
          simpa [ha, hc] using hadd

      · rintro ⟨t, u, ht, hmul, hadd⟩

        refine ⟨z.2, (σ c).1, u.1,
          ⟨(σ c).2, hc.symm⟩, ?_, ?_⟩

        · refine ⟨u.2, (σ x).1, t.1,
            ⟨(σ x).2, hx.symm⟩,
            (ih htail t).mpr ht, ?_⟩

          exact
            (rawMulGraph_axis_iff f (σ x) t u).mpr hmul

        · exact
            (rawAddGraph_axis_iff f (σ c) u z).mpr hadd

/-- Satisfaction of the root formula is equivalent to
    relational Horner evaluation at zero. -/
theorem polynomialRootFormula_horner_iff
    (f : Frame Point) {n : Nat}
    (o i j x : Fin n)
    (coefficients : List (Fin n))
    (ρ : Fin n → Point)
    (σ : Fin n → AxisPoint f)
    (hO : ρ o = f.O)
    (hI : ρ i = f.I)
    (hJ : ρ j = f.J)
    (hx : ρ x = (σ x).1)
    (hcoeff : ∀ c, c ∈ coefficients →
      ρ c = (σ c).1) :
    (polynomialRootFormula o i j x coefficients).eval ρ ↔
      HornerGraph f (σ x)
        (coefficients.map σ) (axisZero f) := by

  have hgeom :=
    hornerExpr_geomValue_of_agreement
      f ρ σ x hx coefficients hcoeff (axisZero f)

  rw [polynomialRootFormula_eval]

  constructor
  · rintro ⟨_, hpoly⟩
    apply hgeom.mp
    simpa [hO, hI, hJ, axisZero] using hpoly

  · intro hroot
    constructor
    · simpa [hO, hI, hx] using (σ x).2
    · have hpoly := hgeom.mpr hroot
      simpa [hO, hI, hJ, axisZero] using hpoly

/-- Existential root formulas and geometric root existence
    agree, without totality, uniqueness, or field laws. -/
theorem polynomialHasRootFormula_horner_iff
    (f : Frame Point) {n : Nat}
    (o i j : Fin n)
    (coefficients : List (Fin n))
    (ρ : Fin n → Point)
    (σ : Fin n → AxisPoint f)
    (hO : ρ o = f.O)
    (hI : ρ i = f.I)
    (hJ : ρ j = f.J)
    (hcoeff : ∀ c, c ∈ coefficients →
      ρ c = (σ c).1) :
    (polynomialHasRootFormula o i j coefficients).eval ρ ↔
      ∃ x : AxisPoint f,
        HornerGraph f x (coefficients.map σ) (axisZero f) := by

  have hcoeff' (x : AxisPoint f) :
      ∀ c, c ∈ coefficients.map Fin.succ →
        (Fin.cons x.1 ρ : Fin (n + 1) → Point) c =
          ((Fin.cons x σ : Fin (n + 1) → AxisPoint f) c).1 := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨v, hv, rfl⟩
    simpa using hcoeff v hv

  have root_iff (x : AxisPoint f) :
      (polynomialRootFormula
        o.succ i.succ j.succ 0
        (coefficients.map Fin.succ)).eval
          (Fin.cons x.1 ρ) ↔
      HornerGraph f x
        (coefficients.map σ) (axisZero f) := by

    have h :=
      polynomialRootFormula_horner_iff
        f o.succ i.succ j.succ 0
        (coefficients.map Fin.succ)
        (Fin.cons x.1 ρ) (Fin.cons x σ)
        (by simpa using hO)
        (by simpa using hI)
        (by simpa using hJ)
        (by rfl)
        (hcoeff' x)

    simpa [List.map_map] using h

  change
    (∃ X : Point,
      (polynomialRootFormula
        o.succ i.succ j.succ 0
        (coefficients.map Fin.succ)).eval
          (Fin.cons X ρ)) ↔
      ∃ x : AxisPoint f,
        HornerGraph f x
          (coefficients.map σ) (axisZero f)

  constructor
  · rintro ⟨X, hX⟩

    have hcol : Col f.O f.I X := by
      have h :=
        ((polynomialRootFormula_eval
          o.succ i.succ j.succ 0
          (coefficients.map Fin.succ)
          (Fin.cons X ρ)).mp hX).1
      simpa [hO, hI] using h

    let x : AxisPoint f := ⟨X, hcol⟩

    exact ⟨x, (root_iff x).mp hX⟩

  · rintro ⟨x, hx⟩
    exact ⟨x.1, (root_iff x).mpr hx⟩

/-- Odd degree = an even number of coefficients with a nonzero last one.
    The leading coefficient condition is essential: the length condition alone
    would also admit lower-degree and zero polynomials. -/
def HasOddDegree (f : Frame Point)
    (coefficients : List (AxisPoint f)) : Prop :=
  (∃ k : Nat, coefficients.length = 2 * k + 2) ∧
  coefficients.getLast? ≠ some (axisZero f)

/-- Target statement of the odd-degree-root part of real closedness.
    It is intentionally a proposition, not an additional plane axiom. -/
def OddPolynomialRootProperty (f : Frame Point) : Prop :=
  ∀ coefficients : List (AxisPoint f),
    HasOddDegree f coefficients →
      ∃ x : AxisPoint f,
        HornerGraph f x coefficients (axisZero f)

/-- Target statement of the positive-square-root part of real closedness.
    It uses only the geometric multiplication and ray predicates. -/
def PositiveSquareRootProperty (f : Frame Point) : Prop :=
  ∀ a : AxisPoint f, Positive f a →
    ∃ x : AxisPoint f,
      AxisNonneg f x ∧ MulGraph f x x a

/-! ## A13 applied to the geometric square-root cut

This is the actual use of the continuity *scheme*. The hypotheses still to
be proved are precisely the geometric ordering of the two sets, existence of
members of both sets, and the fact that segments with endpoints on a fixed
line remain on that line. Nothing is assumed about arbitrary subsets.
-/

/-- Line closure is itself a Tarski theorem to be derived from the axioms;
    writing it as a proposition makes the remaining dependency explicit. -/
def AxisSegmentClosed (f : Frame Point) : Prop :=
  ∀ (X B Y : Point),
    Col f.O f.I X → Col f.O f.I Y →
    Bet X B Y → Col f.O f.I B

/-- When the line-segment closure lemma has been established from the
    primitive Tarski axioms, the unique A13 cut point is an *internal scalar*
    on OI. The theorem retains that exact outstanding dependency explicitly;
    no real-coordinate field or external order is used. -/
theorem upperBounds_cut_A13_internal_scalar
    [ContinuousPlane Point]
    (f : Frame Point) {n : Nat}
    (l : Fin n) (lower : Formula (n + 1))
    (params : Fin n → Point) (R : Point)
    (hLaxis : Col f.O f.I (params l))
    (hRaxis : Col f.O f.I R)
    (hclosed : AxisSegmentClosed f)
    (hL : lower.eval (Fin.cons (params l) params))
    (hR : (upperBoundsFormula l lower).eval (Fin.cons R params)) :
    ∃! b : AxisPoint f,
      Bet (params l) b.1 R ∧
      (upperBoundsFormula l lower).eval (Fin.cons b.1 params) ∧
      ∀ Y : Point,
        (upperBoundsFormula l lower).eval (Fin.cons Y params) →
        Bet (params l) b.1 Y := by
  obtain ⟨B, ⟨hBR, hBupper, hBleast⟩, hunique⟩ :=
    upperBounds_cut_A13_existsUnique l lower params R hL hR
  let b : AxisPoint f := ⟨B, hclosed (params l) B R hLaxis hRaxis hBR⟩
  refine ⟨b, ⟨hBR, hBupper, hBleast⟩, ?_⟩
  intro b' hb'
  apply Subtype.ext
  exact hunique b'.1 hb'

/-- The definable polynomial cut is a specific instance of the internal
    least-upper-bound theorem. In particular, the point on the axis is unique
    *before* any derivative, limit, or numerical evaluation is introduced. -/
theorem polynomial_cut_A13_internal_scalar
    [ContinuousPlane Point]
    (f : Frame Point) {n : Nat}
    (o i j l r : Fin n)
    (coefficients : List (Fin n)) (params : Fin n → Point)
    (hlAxis : Col f.O f.I (params l))
    (hrAxis : Col f.O f.I (params r))
    (hclosed : AxisSegmentClosed f)
    (hL : (polynomialLowerCutFormula o i j l r coefficients).eval
      (Fin.cons (params l) params)) :
    ∃! b : AxisPoint f,
      Bet (params l) b.1 (params r) ∧
      (upperBoundsFormula l
        (polynomialLowerCutFormula o i j l r coefficients)).eval
          (Fin.cons b.1 params) ∧
      ∀ Y : Point,
        (upperBoundsFormula l
          (polynomialLowerCutFormula o i j l r coefficients)).eval
            (Fin.cons Y params) →
        Bet (params l) b.1 Y := by
  exact upperBounds_cut_A13_internal_scalar f l
    (polynomialLowerCutFormula o i j l r coefficients)
    params (params r) hlAxis hrAxis hclosed hL
    (polynomialUpperBounds_contains_right o i j l r coefficients params)

/-- Lower square-root cut, now as a predicate on axis points. -/
def SqrtLowerCut (f : Frame Point) (a x : AxisPoint f) : Prop :=
  AxisNonneg f a ∧ AxisNonneg f x ∧
    ∃ s : AxisPoint f,
      MulGraph f x x s ∧ (s = a ∨ Bet f.O s.1 a.1)

/-- Upper square-root cut as a predicate on axis points. -/
def SqrtUpperCut (f : Frame Point) (a x : AxisPoint f) : Prop :=
  AxisNonneg f a ∧ AxisNonneg f x ∧
    ∃ s : AxisPoint f,
      MulGraph f x x s ∧ (a = s ∨ Bet f.O a.1 s.1)

theorem sqrtLowerFormula_cut_iff (f : Frame Point)
    (a x : AxisPoint f) :
    (sqrtLowerFormula (0 : Fin 4) 1 2 3).eval
      (Fin.cons x.1 ![f.O, f.I, f.J, a.1]) ↔
      SqrtLowerCut f a x := by
  exact sqrtLowerFormula_axis_eval f a x

theorem sqrtUpperFormula_cut_iff (f : Frame Point)
    (a x : AxisPoint f) :
    (sqrtUpperFormula (0 : Fin 4) 1 2 3).eval
      (Fin.cons x.1 ![f.O, f.I, f.J, a.1]) ↔
      SqrtUpperCut f a x := by
  exact sqrtUpperFormula_axis_eval f a x

/-- The lower square-root cut contains zero whenever a is nonnegative.
    This discharges one of the nonemptiness premises for A13. -/
theorem sqrt_lower_contains_zero (f : Frame Point) (a : AxisPoint f)
    (ha : AxisNonneg f a) :
    SqrtLowerCut f a (axisZero f) := by
  refine ⟨ha, Or.inl rfl, axisZero f,
    mul_zero_right f (axisZero f), Or.inr ?_⟩
  exact bet_start f.O a.1

/-- For `0 ≤ a ≤ 1`, the upper square-root cut contains the unit point.
This uses the already proved geometric identity `1 * 1 = 1`, not field axioms. -/
theorem sqrt_upper_contains_one_of_bet (f : Frame Point) (a : AxisPoint f)
    (ha : AxisNonneg f a) (hbound : Bet f.O a.1 f.I) :
    SqrtUpperCut f a (axisOne f) := by
  exact ⟨ha,
    positive_implies_axis_nonneg f (axisOne f) (axisOne_positive f),
    axisOne f, mul_one_right f (axisOne f), Or.inr hbound⟩

/-- A13 yields an axis point separating the square-root cuts, once their
    geometric separation, nonemptiness, and line closure are available.
    Importantly, neither the boundary's square nor the field laws are
    asserted by this theorem. -/
theorem sqrt_cut_has_axis_separator [ContinuousPlane Point]
    (f : Frame Point) (a : AxisPoint f)
    (hclosed : AxisSegmentClosed f)
    (horder : ∀ x y : AxisPoint f,
      SqrtLowerCut f a x → SqrtUpperCut f a y → Bet f.O x.1 y.1)
    (hleft : ∃ x : AxisPoint f, SqrtLowerCut f a x)
    (hright : ∃ y : AxisPoint f, SqrtUpperCut f a y) :
    ∃ b : AxisPoint f,
      ∀ x y : AxisPoint f,
        SqrtLowerCut f a x →
        SqrtUpperCut f a y → Bet x.1 b.1 y.1 := by
  let params : Fin 4 → Point := ![f.O, f.I, f.J, a.1]
  let L : Formula 5 := sqrtLowerFormula (0 : Fin 4) 1 2 3
  let U : Formula 5 := sqrtUpperFormula (0 : Fin 4) 1 2 3
  have hantecedent :
      ∃ A : Point, ∀ X Y : Point,
        L.eval (Fin.cons X params) →
        U.eval (Fin.cons Y params) → Bet A X Y := by
    refine ⟨f.O, ?_⟩
    intro X Y hX hY
    have hxAxis : Col f.O f.I X :=
      ((sqrtLowerFormula_eval (0 : Fin 4) 1 2 3 X params).mp hX).2.1.1
    have hyAxis : Col f.O f.I Y :=
      ((sqrtUpperFormula_eval (0 : Fin 4) 1 2 3 Y params).mp hY).2.1.1
    let x : AxisPoint f := ⟨X, hxAxis⟩
    let y : AxisPoint f := ⟨Y, hyAxis⟩
    have hxl : SqrtLowerCut f a x :=
      (sqrtLowerFormula_cut_iff f a x).mp hX
    have hyu : SqrtUpperCut f a y :=
      (sqrtUpperFormula_cut_iff f a y).mp hY
    exact horder x y hxl hyu
  obtain ⟨B, hB⟩ :=
    ContinuousPlane.first_order_continuity 4 L U params hantecedent
  obtain ⟨x₀, hx₀⟩ := hleft
  obtain ⟨y₀, hy₀⟩ := hright
  have hbetween : Bet x₀.1 B y₀.1 :=
    hB x₀.1 y₀.1
      ((sqrtLowerFormula_cut_iff f a x₀).mpr hx₀)
      ((sqrtUpperFormula_cut_iff f a y₀).mpr hy₀)
  let b : AxisPoint f :=
    ⟨B, hclosed x₀.1 B y₀.1 x₀.2 y₀.2 hbetween⟩
  refine ⟨b, ?_⟩
  intro x y hx hy
  exact hB x.1 y.1
    ((sqrtLowerFormula_cut_iff f a x).mpr hx)
    ((sqrtUpperFormula_cut_iff f a y).mpr hy)

/-- In the nonnegative case, left nonemptiness is already proved,
    so A13 requires only a member of the upper cut and the remaining
    incidence/order lemmas. -/
theorem sqrt_cut_has_axis_separator_of_nonneg [ContinuousPlane Point]
    (f : Frame Point) (a : AxisPoint f)
    (ha : AxisNonneg f a)
    (hclosed : AxisSegmentClosed f)
    (horder : ∀ x y : AxisPoint f,
      SqrtLowerCut f a x → SqrtUpperCut f a y → Bet f.O x.1 y.1)
    (hright : ∃ y : AxisPoint f, SqrtUpperCut f a y) :
    ∃ b : AxisPoint f,
      ∀ x y : AxisPoint f,
        SqrtLowerCut f a x →
        SqrtUpperCut f a y → Bet x.1 b.1 y.1 := by
  exact sqrt_cut_has_axis_separator f a hclosed horder
    ⟨axisZero f, sqrt_lower_contains_zero f a ha⟩ hright

/-! ## Outstanding mathematical obligations (statements, not new axioms)

A: prove `AddTotal` and `MulTotal` from `Plane` and the affine frame.
B: derive additive, multiplicative, distributive, and order laws *from* A and
   Tarski's axioms; do not add them as a typeclass premise.
C: derive line closure (`AxisSegmentClosed`) and the order/separation
   conditions needed by `sqrt_cut_has_axis_separator_of_nonneg` from `Plane`.
   Establish upper-cut nonemptiness and show that the separator's square is a.
D: prove `PositiveSquareRootProperty` and `OddPolynomialRootProperty` from
   the axioms. Polynomial evaluation, root, and bounded-cut formulas are now
   finite Tarski-language formulas. The algebraic IVT argument and proofs
   that the bounded cuts satisfy A13's hypothesis are not yet established.

The following declarations are propositions only. No evidence of them is
assumed or manufactured by this draft.
-/

def AddTotal (f : Frame Point) : Prop :=
  ∀ x y : AxisPoint f, ∃! z : AxisPoint f, AddGraph f x y z

def MulTotal (f : Frame Point) : Prop :=
  ∀ x y : AxisPoint f, ∃! z : AxisPoint f, MulGraph f x y z

/-- Horner evaluation is total and single-valued once
    the geometric addition and multiplication are total
    and single-valued. -/
theorem hornerGraph_exists_unique
    (f : Frame Point)
    (hAdd : AddTotal f)
    (hMul : MulTotal f)
    (x : AxisPoint f)
    (coefficients : List (AxisPoint f)) :
    ∃! z : AxisPoint f,
      HornerGraph f x coefficients z := by
  induction coefficients with
  | nil =>
      refine ⟨axisZero f, rfl, ?_⟩
      intro z hz
      exact hz

  | cons a rest ih =>
      obtain ⟨t, ht, htuniq⟩ := ih
      obtain ⟨u, hu, huuniq⟩ := hMul x t
      obtain ⟨z, hz, hzuniq⟩ := hAdd a u

      refine ⟨z, ⟨t, u, ht, hu, hz⟩, ?_⟩

      intro w hw
      change ∃ t' u' : AxisPoint f,
        HornerGraph f x rest t' ∧
        MulGraph f x t' u' ∧
        AddGraph f a u' w at hw

      obtain ⟨t', u', ht', hu', hw⟩ := hw

      have hteq : t' = t := htuniq t' ht'
      subst t'

      have hueq : u' = u := huuniq u' hu'
      subst u'

      exact hzuniq w hw

/-- A point on the positive ray cannot also lie on
    the negative ray. This uses only betweenness laws. -/
theorem positive_not_negative
    (f : Frame Point) (v : AxisPoint f)
    (hp : Positive f v) :
    ¬ Bet v.1 f.O f.I := by
  intro hn
  rcases hp with ⟨_, hzero, hleft | hright⟩

  · have heq : f.O = f.I :=
      bet_swap_endpoint_eq hleft (bet_symm hn)
    exact f.O_ne_I heq

  · have heq : v.1 = f.O :=
      bet_swap_endpoint_eq hn hright
    exact hzero heq

/-- A geometrically evaluated polynomial cannot have
    both positive and negative values at the same input,
    provided its arithmetic graphs are functional. -/
theorem horner_signs_disjoint
    (f : Frame Point)
    (hAdd : AddTotal f)
    (hMul : MulTotal f)
    (x : AxisPoint f)
    (coefficients : List (AxisPoint f)) :
    ¬ (
      (∃ p : AxisPoint f,
        HornerGraph f x coefficients p ∧
        Positive f p) ∧
      (∃ q : AxisPoint f,
        HornerGraph f x coefficients q ∧
        q.1 ≠ f.O ∧
        Bet q.1 f.O f.I)
    ) := by
  rintro ⟨⟨p, hp, hpos⟩,
    ⟨q, hq, _, hneg⟩⟩

  obtain ⟨v, _, huniq⟩ :=
    hornerGraph_exists_unique
      f hAdd hMul x coefficients

  have hpv : p = v := huniq p hp
  have hqv : q = v := huniq q hq
  have hpq : p = q := hpv.trans hqv.symm

  rw [← hpq] at hneg
  exact positive_not_negative f p hpos hneg

/-- A single-valued addition graph, without assuming it is defined
    for every pair of axis points. -/
def AddFunctional (f : Frame Point) : Prop :=
  ∀ a b z w : AxisPoint f,
    AddGraph f a b z → AddGraph f a b w → z = w

/-- A single-valued multiplication graph, without totality. -/
def MulFunctional (f : Frame Point) : Prop :=
  ∀ a b z w : AxisPoint f,
    MulGraph f a b z → MulGraph f a b w → z = w

/-- Horner evaluation is single-valued even if some operations are partial. -/
theorem hornerGraph_unique_of_functional
    (f : Frame Point)
    (hAdd : AddFunctional f) (hMul : MulFunctional f)
    (x : AxisPoint f) (coefficients : List (AxisPoint f))
    (z w : AxisPoint f)
    (hz : HornerGraph f x coefficients z)
    (hw : HornerGraph f x coefficients w) : z = w := by
  induction coefficients generalizing z w with
  | nil =>
      change z = axisZero f at hz
      change w = axisZero f at hw
      exact hz.trans hw.symm
  | cons a rest ih =>
      change ∃ t u : AxisPoint f,
        HornerGraph f x rest t ∧ MulGraph f x t u ∧ AddGraph f a u z at hz
      change ∃ t u : AxisPoint f,
        HornerGraph f x rest t ∧ MulGraph f x t u ∧ AddGraph f a u w at hw
      obtain ⟨t, u, ht, hu, hzu⟩ := hz
      obtain ⟨t', u', ht', hu', hwu⟩ := hw
      have hteq : t = t' := ih t t' ht ht'
      subst t'
      have hueq : u = u' := hMul x t u u' hu hu'
      subst u'
      exact hAdd a u z w hzu hwu

/-- Positivity and negativity of a Horner value are disjoint using
    graph uniqueness alone; existence of evaluation is not assumed. -/
theorem horner_signs_disjoint_of_functional
    (f : Frame Point)
    (hAdd : AddFunctional f) (hMul : MulFunctional f)
    (x : AxisPoint f) (coefficients : List (AxisPoint f)) :
    ¬ ((∃ p : AxisPoint f,
          HornerGraph f x coefficients p ∧ Positive f p) ∧
       (∃ q : AxisPoint f,
          HornerGraph f x coefficients q ∧ Bet q.1 f.O f.I)) := by
  rintro ⟨⟨p, hp, hpos⟩, ⟨q, hq, hneg⟩⟩
  have hpq : p = q := hornerGraph_unique_of_functional f hAdd hMul x
    coefficients p q hp hq
  rw [← hpq] at hneg
  exact positive_not_negative f p hpos hneg

def AddCommLaw (f : Frame Point) : Prop :=
  ∀ x y z : AxisPoint f, AddGraph f x y z → AddGraph f y x z

def MulCommLaw (f : Frame Point) : Prop :=
  ∀ x y z : AxisPoint f, MulGraph f x y z → MulGraph f y x z

def ColSegmentClosed : Prop :=
  ∀ (O I X B Y : Point), Col O I X → Col O I Y → Bet X B Y → Col O I B

/-! ### Exact relational field-law targets

All the following are propositions defined using the point constructions.
They are not additional assumptions on `Plane`. Existence and uniqueness
(`AddTotal`, `MulTotal`) are separate because neither follows from writing
a graph in first-order logic.
-/

def AddAssocLaw (f : Frame Point) : Prop :=
  ∀ a b c ab bc lhs rhs : AxisPoint f,
    AddGraph f a b ab → AddGraph f ab c lhs →
    AddGraph f b c bc → AddGraph f a bc rhs → lhs = rhs

def AddRightZeroLaw (f : Frame Point) : Prop :=
  ∀ a : AxisPoint f, AddGraph f a (axisZero f) a

def AddInverseLaw (f : Frame Point) : Prop :=
  ∀ a : AxisPoint f,
    ∃ b : AxisPoint f, AddGraph f a b (axisZero f)

def MulAssocLaw (f : Frame Point) : Prop :=
  ∀ a b c ab bc lhs rhs : AxisPoint f,
    MulGraph f a b ab → MulGraph f ab c lhs →
    MulGraph f b c bc → MulGraph f a bc rhs → lhs = rhs

def MulLeftOneLaw (f : Frame Point) : Prop :=
  ∀ a : AxisPoint f, MulGraph f (axisOne f) a a

def MulInverseLaw (f : Frame Point) : Prop :=
  ∀ a : AxisPoint f, a ≠ axisZero f →
    ∃ b : AxisPoint f, MulGraph f a b (axisOne f)

def LeftDistributiveLaw (f : Frame Point) : Prop :=
  ∀ a b c bc ab ac lhs rhs : AxisPoint f,
    AddGraph f b c bc → MulGraph f a bc lhs →
    MulGraph f a b ab → MulGraph f a c ac →
    AddGraph f ab ac rhs → lhs = rhs

def PositiveAddClosed (f : Frame Point) : Prop :=
  ∀ a b c : AxisPoint f,
    Positive f a → Positive f b → AddGraph f a b c → Positive f c

def PositiveMulClosed (f : Frame Point) : Prop :=
  ∀ a b c : AxisPoint f,
    Positive f a → Positive f b → MulGraph f a b c → Positive f c

def PositiveTrichotomy (f : Frame Point) : Prop :=
  ∀ a : AxisPoint f,
    a = axisZero f ∨ Positive f a ∨
      ∃ b : AxisPoint f,
        Positive f b ∧ AddGraph f a b (axisZero f)

/-- The positive cone has no additive inverse pair. Alongside trichotomy
    and closure, this supplies the strict-order compatibility condition. -/
def PositiveProper (f : Frame Point) : Prop :=
  ∀ a b : AxisPoint f,
    Positive f a → Positive f b →
    AddGraph f a b (axisZero f) → False

/-- Complete statement of the intended coordinatization result. It is a
    *goal*, not a theorem or a new axiom. All clauses are relational.
    The complete proof from the Tarski axioms is not in this draft. -/
def RealClosedAxisGoal (f : Frame Point) : Prop :=
  AddTotal f ∧ MulTotal f ∧
  AddCommLaw f ∧ AddAssocLaw f ∧ AddRightZeroLaw f ∧ AddInverseLaw f ∧
  MulCommLaw f ∧ MulAssocLaw f ∧ MulLeftOneLaw f ∧ MulInverseLaw f ∧
  LeftDistributiveLaw f ∧
  PositiveAddClosed f ∧ PositiveMulClosed f ∧
  PositiveTrichotomy f ∧ PositiveProper f ∧
  PositiveSquareRootProperty f ∧ OddPolynomialRootProperty f

#print axioms parallel_symm
#print axioms frame_exists
#print axioms axisZero_ne_axisOne
#print axioms add_zero_left_unique
#print axioms mul_zero_right_unique
#print axioms mul_one_right
#print axioms segment_extension_unique
#print axioms bet_swap_endpoint_eq
#print axioms bet_same_origin_antisymm
#print axioms bet_inner_trans
#print axioms bet_exchange
#print axioms parallel_same_of_intersection
#print axioms bet_outer_trans
#print axioms bet_nested
#print axioms bet_extend
#print axioms opposite_exists_unique
#print axioms axis_opposite_one_exists_unique
#print axioms segment_extension_nontrivial
#print axioms axis_beyond_one_exists
#print axioms axis_negative_one_exists
#print axioms Frame.three_distances_unique
#print axioms cong_zero
#print axioms cong_reverse_both
#print axioms segment_cong_add
#print axioms colFormula_eval
#print axioms parallelFormula_eval
#print axioms addGraphFormula_eval
#print axioms mulGraphFormula_eval
#print axioms addGraphFormula_raw_eval
#print axioms scalarExprFormula_eval
#print axioms hornerExpr_geomValue_iff_HornerGraph
#print axioms hornerExpr_geomValue_of_agreement
#print axioms polynomialRootFormula_horner_iff
#print axioms polynomialHasRootFormula_horner_iff
#print axioms hornerGraph_exists_unique
#print axioms positive_not_negative
#print axioms horner_signs_disjoint
#print axioms hornerGraph_unique_of_functional
#print axioms horner_signs_disjoint_of_functional
#print axioms intervalNegativePrefix_downward
#print axioms intervalNegativePrefix_contains_left
#print axioms intervalNegativePrefix_not_reverse
#print axioms intervalNegativePrefix_ordered
#print axioms polynomial_cut_ordered_of_downward
#print axioms polynomial_cut_A13_of_downward_and_connectivity
#print axioms hornerExpr_ignore_middle
#print axioms polynomialNegativeFormula_semantics
#print axioms polynomialNegativeFormula_ignore_middle
#print axioms polynomialLowerCutFormula_prefix_eval
#print axioms polynomialLowerCutFormula_downward
#print axioms polynomial_cut_A13_of_connectivity
#print axioms Formula.rename_eval
#print axioms upperBoundsFormula_eval
#print axioms upperBounds_cut_A13
#print axioms polynomialUpperBounds_contains_right
#print axioms polynomial_cut_A13_direct
#print axioms polynomial_cut_A13_in_interval
#print axioms upperBounds_cut_A13_least_upper_bound
#print axioms polynomial_cut_A13_least_upper_bound
#print axioms upperBounds_cut_A13_existsUnique
#print axioms polynomial_cut_A13_existsUnique
#print axioms upperBounds_cut_A13_internal_scalar
#print axioms polynomial_cut_A13_internal_scalar
#print axioms polynomialRootFormula_eval
#print axioms sqrt_lower_contains_zero
#print axioms sqrt_upper_contains_one_of_bet
#print axioms sqrt_cut_has_axis_separator_of_nonneg
#print axioms axis_nonneg_iff_ray_or_origin
#print axioms squareGraphFormula_frame_eval
#print axioms sqrtLowerFormula_axis_eval
#print axioms sqrtUpperFormula_axis_eval

end TarskiField



/-! SOURCE: workstreams/Incidence.lean -/


/-!
TarskiField incidence workstream.

This module imports the normalized `TarskiUnifiedRevised` source, then proves
additional synthetic geometry consequences inside the `TarskiField` namespace.
It does not duplicate or strengthen the `Plane` axioms.

All proofs below use only the original Tarski `Plane` assumptions.
No `sorry`, additional axiom, ℝ, or prebuilt Euclidean field is used.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Every noncollinear triple has pairwise distinct members. -/
theorem noncol_ne_first_second {A B C : Point}
    (h : ¬ Col A B C) : A ≠ B := by
  intro hAB
  apply h
  subst B
  exact Or.inr (Or.inr (bet_end C A))

theorem noncol_ne_first_third {A B C : Point}
    (h : ¬ Col A B C) : A ≠ C := by
  intro hAC
  apply h
  subst C
  exact col_left A B

theorem noncol_ne_second_third {A B C : Point}
    (h : ¬ Col A B C) : B ≠ C := by
  intro hBC
  apply h
  subst C
  exact col_right A B

/-- Collinearity is invariant under all permutations of three points. -/
theorem col_swap_last {A B C : Point}
    (h : Col A B C) : Col A C B :=
  col_rotate (col_swap h)

theorem col_reverse {A B C : Point}
    (h : Col A B C) : Col C B A :=
  col_rotate (col_rotate (col_swap h))

theorem col_reverse_cycle {A B C : Point}
    (h : Col A B C) : Col C A B :=
  col_rotate (col_rotate h)

/-- The ray relation implies collinearity, with no order-field arithmetic. -/
theorem out_implies_col {O A X : Point}
    (h : Out O A X) : Col O A X := by
  rcases h with ⟨_, _, hOAX | hOXA⟩
  · exact Or.inl hOAX
  · exact Or.inr (Or.inl (bet_symm hOXA))

/-- A point between the origin and the unit belongs to that unit line. -/
theorem col_of_bet_on_unit_segment {O I T : Point}
    (h : Bet O T I) : Col O I T :=
  Or.inr (Or.inl (bet_symm h))

/-- A point lying beyond the origin in the negative direction is collinear
    with the fixed unit line. -/
theorem col_of_bet_behind_origin {O I T : Point}
    (h : Bet I O T) : Col O I T :=
  Or.inr (Or.inr (bet_symm h))

/-- Line-segment closure in the nontrivial but directly accessible case
    when the moving endpoint lies between O and I. -/
theorem col_of_bet_within_unit_segment {O I T B : Point}
    (hOTI : Bet O T I) (hOBT : Bet O B T) :
    Col O I B := by
  have hOBI : Bet O B I := bet_extend hOBT hOTI
  exact col_of_bet_on_unit_segment hOBI

/-- Line-segment closure when the moving endpoint lies on the negative
    extension of the origin. -/
theorem col_of_bet_negative_segment {O I T B : Point}
    (hIOT : Bet I O T) (hOBT : Bet O B T) :
    Col O I B := by
  have hIOB : Bet I O B := bet_inner_trans hIOT hOBT
  exact col_of_bet_behind_origin hIOB

/-- If a segment degenerates to one endpoint, its only intermediate point
    is that endpoint. This is a direct Tarski between-identity consequence. -/
theorem col_of_degenerate_segment {O I X B : Point}
    (hX : Col O I X) (hB : Bet X B X) : Col O I B := by
  have hXB : X = B := between_identity X B hB
  simpa [← hXB] using hX

/-! The five-segment distance-propagation proof (`equidistant_extend_beyond`,
`equidistant_between_stations`, `col_equidistant_of_two_stations`) is now in
the unified source. This module contains only additional declarations. -/

/-! ### Interior five-segment propagation

The primitive five-segment axiom applies when B lies between A and C. We
derive the variant for C between A and B using two extensions beyond B and
two applications of the primitive five-segment axiom. This gives a building
block used by GeoCoq's `l4_2` / `l4_16` before the betweenness-order theorem.
-/

/-- Interior variant of five-segment: a point C between A and B is rigidly
    determined by its distance to B, so the four listed congruences propagate
    the distance from C to D. The usual extra hypothesis `Cong A C A' C'`
    is unnecessary here. -/
theorem five_segment_inner_order
    {A A' B B' C C' D D' : Point}
    (hAB : Cong A B A' B')
    (hBC : Cong B C B' C')
    (hAD : Cong A D A' D')
    (hBD : Cong B D B' D')
    (hACB : Bet A C B)
    (hA'C'B' : Bet A' C' B')
    (hABne : A ≠ B) : Cong C D C' D' := by
  obtain ⟨E, hABE, hBE⟩ := segment_construction A B A' B'
  obtain ⟨E', hA'B'E', hB'E'⟩ := segment_construction A' B' A B
  have hBEboth : Cong B E B' E' :=
    cong_trans hBE (cong_trans (cong_symm hAB) (cong_symm hB'E'))
  have hED : Cong E D E' D' :=
    five_segment A A' B B' E E' D D'
      hAB hBEboth hAD hBD hABE hA'B'E' hABne
  have hEBC : Bet E B C := bet_symm (bet_exchange hACB hABE)
  have hE'B'C' : Bet E' B' C' :=
    bet_symm (bet_exchange hA'C'B' hA'B'E')
  have hA'B'ne : A' ≠ B' := by
    intro heq
    have hzero : A = B :=
      cong_identity A B A' (by simpa [heq] using hAB)
    exact hABne hzero
  have hEBne : E ≠ B := by
    intro hEB
    have heq : A' = B' :=
      cong_identity A' B' B (by
        simpa [hEB] using (cong_symm hBE))
    exact hA'B'ne heq
  exact five_segment E E' B B' C C' D D'
    (cong_reverse_both hBEboth) hBC hED hBD
    hEBC hE'B'C' hEBne

/-- Segment subtraction in Tarski geometry: equal long segments with equal
    terminal subsegments have equal initial subsegments.  This is not a field
    subtraction law: the proof is one application of the inner five-segment
    theorem to the degenerate comparison points A and A'. -/
theorem segment_cong_sub_inner
    {A A' B B' C C' : Point}
    (hAB : Cong A B A' B')
    (hBC : Cong B C B' C')
    (hACB : Bet A C B)
    (hA'C'B' : Bet A' C' B') :
    Cong A C A' C' := by
  by_cases hABne : A = B
  · subst B
    have hA'B' : A' = B' :=
      cong_identity A' B' A (cong_symm hAB)
    have hAC : A = C := between_identity A C hACB
    have hA'C' : A' = C' := by
      have hbet : Bet A' C' A' := by simpa [hA'B'] using hA'C'B'
      exact between_identity A' C' hbet
    simpa [hAC, hA'C'] using cong_zero A A'
  · have hCA : Cong C A C' A' :=
      five_segment_inner_order
        hAB hBC (cong_zero A A')
        (cong_reverse_both hAB)
        hACB hA'C'B' hABne
    exact cong_reverse_both hCA

/-- Metric uniqueness of the interior point at prescribed distance from B.
    Unlike ray-extension uniqueness, this deals with points between A and B. -/
theorem segment_inner_unique
    {A B C D : Point}
    (hAB : A ≠ B)
    (hC : Bet A C B) (hD : Bet A D B)
    (hCD : Cong B C B D) : C = D := by
  have hCC : Cong C C D C :=
    five_segment_inner_order
      (congr_refl A B) hCD (congr_refl A C)
      (congr_refl B C) hC hD hAB
  have hDC : Cong D C C C := cong_symm hCC
  exact (cong_identity D C C hDC).symm

/-- GeoCoq Ch04 `l4_2`: the actual inner five-segment theorem (IFSC).
    Compare triangles whose station B lies *inside* AC.  It follows from
    the previous two-application construction by swapping the B/C roles.
    This is the central fifth-segment variant used in the original proof
    of Ch05 `l5_1`. -/
theorem inner_five_segment
    {A A' B B' C C' D D' : Point}
    (hABC : Bet A B C) (hA'B'C' : Bet A' B' C')
    (hAC : Cong A C A' C') (hBC : Cong B C B' C')
    (hAD : Cong A D A' D') (hCD : Cong C D C' D') :
    Cong B D B' D' := by
  by_cases hACne : A = C
  · subst C
    have hAB : A = B := between_identity A B hABC
    have hA'C' : A' = C' :=
      cong_identity A' C' A (cong_symm hAC)
    have hA'B' : A' = B' := by
      have hbet : Bet A' B' A' := by simpa [hA'C'] using hA'B'C'
      exact between_identity A' B' hbet
    simpa only [← hAB, ← hA'B', ← hA'C'] using hCD
  · exact five_segment_inner_order
      hAC (cong_reverse_both hBC) hAD hCD
      hABC hA'B'C' hACne

/-- GeoCoq Ch04 `l4_5`, ordered three-point copy. A point B between A,C
    can be copied to the matching position between A',C' whenever the two
    whole segments are congruent. The proof uses three primitive segment
    constructions, segment congruence addition, and extension uniqueness;
    it does not use Ch05 ray comparability. -/
theorem copy_point_inside_congruent_segment
    {A B C A' C' : Point}
    (hABC : Bet A B C)
    (hAC : Cong A C A' C') :
    ∃ B' : Point, Bet A' B' C' ∧
      Cong A B A' B' ∧ Cong B C B' C' := by
  by_cases hACne : A = C
  · subst C
    have hAB : A = B := between_identity A B hABC
    have hA'C' : A' = C' :=
      cong_identity A' C' A (cong_symm hAC)
    refine ⟨A', ?_, ?_, ?_⟩
    · simpa [hA'C'] using bet_end A' A'
    · simpa [hAB] using cong_zero A A'
    · simpa [hAB, hA'C'] using cong_zero A A'
  · obtain ⟨E, hC'A'E, hA'E⟩ :=
      segment_construction C' A' A C
    have hEne : E ≠ A' := by
      intro hEA'
      have hzero : A = C :=
        cong_identity A C A' (by
          simpa [hEA'] using (cong_symm hA'E))
      exact hACne hzero
    obtain ⟨B', hEA'B', hA'B'⟩ :=
      segment_construction E A' A B
    obtain ⟨C'', hEB'C'', hB'C''⟩ :=
      segment_construction E B' B C
    have hA'B'C'' : Bet A' B' C'' :=
      bet_exchange hEA'B' hEB'C''
    have hEA'C'' : Bet E A' C'' :=
      bet_extend hEA'B' hEB'C''
    have hEA'C' : Bet E A' C' := bet_symm hC'A'E
    have hAC'' : Cong A C A' C'' :=
      segment_cong_add hABC hA'B'C'' (cong_symm hA'B') (cong_symm hB'C'')
    have hC''C' : C'' = C' :=
      segment_extension_unique hEne hEA'C'' hEA'C'
        (cong_trans (cong_symm hAC'') hAC)
    subst C''
    exact ⟨B', hA'B'C'', cong_symm hA'B', cong_symm hB'C''⟩

/-- GeoCoq Ch04 `l4_6`: three pairwise segment congruences transport
    betweenness. The corresponding interior point X is constructed by
    `copy_point_inside_congruent_segment`, then identified with B' using
    `col_equidistant_of_two_stations` (itself derived from five-segment).
    Neither distances nor lines are interpreted in an external field. -/
theorem bet_of_three_segment_congruences
    {A B C A' B' C' : Point}
    (hABC : Bet A B C)
    (hAB : Cong A B A' B')
    (hBC : Cong B C B' C')
    (hAC : Cong A C A' C') :
    Bet A' B' C' := by
  obtain ⟨X, hA'XC', hABX, hBCX⟩ :=
    copy_point_inside_congruent_segment hABC hAC
  by_cases hACne : A = C
  · subst C
    have hABeq : A = B := between_identity A B hABC
    have hA'B'eq : A' = B' :=
      cong_identity A' B' A (by
        simpa [hABeq] using (cong_symm hAB))
    have hA'C'eq : A' = C' :=
      cong_identity A' C' A (cong_symm hAC)
    simpa only [← hA'B'eq, ← hA'C'eq] using bet_end A' A'
  · have hA'C'ne : A' ≠ C' := by
      intro heq
      have hzero : A = C :=
        cong_identity A C A' (by simpa [heq] using hAC)
      exact hACne hzero
    have hA'B'X : Cong A' B' A' X :=
      cong_trans (cong_symm hAB) hABX
    have hC'B'X : Cong C' B' C' X := by
      have h : Cong B' C' X C' :=
        cong_trans (cong_symm hBC) hBCX
      exact cong_reverse_both h
    have hCol : Col A' C' X :=
      col_of_bet_on_unit_segment hA'XC'
    have hX : Cong X B' X X :=
      col_equidistant_of_two_stations hA'C'ne hCol
        hA'B'X hC'B'X
    have hXB' : X = B' := cong_identity X B' X hX
    simpa [hXB'] using hA'XC'

/-- Complementary segment-subtraction law (outer interval).  If two whole
    segments AC and A'C' and their respective initial parts AB and A'B'
    are congruent, their terminal parts BC and B'C' are congruent.
    This is proved by copying B to A'C' and using inner-point uniqueness. -/
theorem segment_cong_sub_outer
    {A B C A' B' C' : Point}
    (hABC : Bet A B C) (hA'B'C' : Bet A' B' C')
    (hAB : Cong A B A' B')
    (hAC : Cong A C A' C') :
    Cong B C B' C' := by
  obtain ⟨X, hA'XC', hABX, hBCX⟩ :=
    copy_point_inside_congruent_segment hABC hAC
  by_cases hA'C' : A' = C'
  · have hACeq : A = C :=
      cong_identity A C A' (by simpa [hA'C'] using hAC)
    have hABeq : A = B := by
      have hbet : Bet A B A := by simpa [hACeq] using hABC
      exact between_identity A B hbet
    have hA'B'eq : A' = B' := by
      have hbet : Bet A' B' A' := by simpa [hA'C'] using hA'B'C'
      exact between_identity A' B' hbet
    simpa only [← hACeq, ← hABeq, ← hA'C', ← hA'B'eq] using cong_zero A A'
  · have hA'BX : Cong A' B' A' X :=
      cong_trans (cong_symm hAB) hABX
    have hXeq : X = B' :=
      segment_inner_unique (Ne.symm hA'C')
        (bet_symm hA'XC') (bet_symm hA'B'C')
        (cong_symm hA'BX)
    simpa [hXeq] using hBCX

/-- First constructive stage of GeoCoq's Ch05 `eq_dec_implies_l5_1`.
    Without presuming which of C,D is farther from A on their common ray,
    extend D by CD and C by CD; then extend the resulting C₁,D₁ by CB,DB.
    The two resulting endpoints coincide.  This supplies the symmetric
    auxiliary configuration for the Pasch/five-segment part of l5_1. -/
theorem coincident_outer_extension_bridge
    {A B C D : Point}
    (hAB : A ≠ B)
    (hABC : Bet A B C)
    (hABD : Bet A B D) :
    ∃ C₁ D₁ E : Point,
      Bet A D C₁ ∧ Bet A C D₁ ∧
      Bet A C₁ E ∧ Bet A D₁ E ∧
      Cong D C₁ C D ∧ Cong C D₁ C D ∧
      Cong C₁ E C B ∧ Cong D₁ E D B ∧
      Cong B C₁ E C := by
  obtain ⟨C₁, hADC₁, hDC₁⟩ :=
    segment_construction A D C D
  obtain ⟨D₁, hACD₁, hCD₁⟩ :=
    segment_construction A C C D
  obtain ⟨E, hAC₁E, hC₁E⟩ :=
    segment_construction A C₁ C B
  obtain ⟨E', hAD₁E', hD₁E'⟩ :=
    segment_construction A D₁ D B
  have hBDC₁ : Bet B D C₁ := bet_exchange hABD hADC₁
  have hE'D₁C : Bet E' D₁ C :=
    bet_symm (bet_exchange hACD₁ hAD₁E')
  have hBDcong : Cong B D E' D₁ :=
    cong_symm (cong_reverse_both hD₁E')
  have hDCcong : Cong D C₁ D₁ C :=
    cong_reverse_right
      (cong_trans hDC₁ (cong_symm hCD₁))
  have hBC₁ : Cong B C₁ E' C :=
    segment_cong_add hBDC₁ hE'D₁C hBDcong hDCcong
  have hABC₁ : Bet A B C₁ := bet_extend hABD hADC₁
  have hBC₁E : Bet B C₁ E := bet_exchange hABC₁ hAC₁E
  have hACE' : Bet A C E' := bet_extend hACD₁ hAD₁E'
  have hE'CB : Bet E' C B :=
    bet_symm (bet_exchange hABC hACE')
  have hBE : Cong B E E' B :=
    segment_cong_add hBC₁E hE'CB hBC₁ hC₁E
  have hABE : Bet A B E := bet_extend hABC₁ hAC₁E
  have hABD₁ : Bet A B D₁ := bet_extend hABC hACD₁
  have hABE' : Bet A B E' := bet_extend hABD₁ hAD₁E'
  have hEE' : E = E' :=
    segment_extension_unique hAB hABE hABE'
      (cong_reverse_right hBE)
  refine ⟨C₁, D₁, E, hADC₁, hACD₁, hAC₁E, ?_,
    hDC₁, hCD₁, hC₁E, ?_, ?_⟩
  · simpa [← hEE'] using hAD₁E'
  · simpa [← hEE'] using hD₁E'
  · simpa [← hEE'] using hBC₁

/-- Second stage of GeoCoq `eq_dec_implies_l5_1` (its application of FSC):
    the two auxiliary points C₁,D₁ have separation congruent to CD,
    regardless of their unknown order. Uses only the ordinary five-segment
    five-segment premise once, after constructing the common outer endpoint. -/
theorem coincident_bridge_inner_span_congruent
    {A B C D : Point}
    (hAB : A ≠ B) (hABC : Bet A B C) (hABD : Bet A B D) :
    ∃ C₁ D₁ E : Point,
      Bet A D C₁ ∧ Bet A C D₁ ∧
      Bet A C₁ E ∧ Bet A D₁ E ∧
      Cong D C₁ C D ∧ Cong C D₁ C D ∧
      Cong C₁ E C B ∧ Cong D₁ E D B ∧
      Cong B C₁ E C ∧
      Cong D₁ C₁ D C := by
  obtain ⟨C₁, D₁, E,
      hADC₁, hACD₁, hAC₁E, hAD₁E,
      hDC₁, hCD₁, hC₁E, hD₁E, hBC₁⟩ :=
    coincident_outer_extension_bridge hAB hABC hABD
  have hspan : Cong D₁ C₁ D C := by
    by_cases hBCne : B = C
    · have hC₁E : C₁ = E :=
        cong_identity C₁ E C (by simpa [hBCne] using hC₁E)
      simpa [hC₁E, hBCne] using hD₁E
    · have hBCD₁ : Bet B C D₁ := bet_exchange hABC hACD₁
      have hEC₁D : Bet E C₁ D :=
        bet_symm (bet_exchange hADC₁ hAC₁E)
      have hBC_EC₁ : Cong B C E C₁ :=
        cong_symm (cong_reverse_both hC₁E)
      have hCD₁_C₁D : Cong C D₁ C₁ D :=
        cong_trans hCD₁
          (cong_reverse_right (cong_symm hDC₁))
      exact five_segment B E C C₁ D₁ D C₁ C
        hBC_EC₁ hCD₁_C₁D hBC₁
        (cong_pseudo_reflexivity C C₁)
        hBCD₁ hEC₁D hBCne
  exact ⟨C₁, D₁, E, hADC₁, hACD₁, hAC₁E, hAD₁E,
    hDC₁, hCD₁, hC₁E, hD₁E, hBC₁, hspan⟩

/-- GeoCoq's middle Pasch step in Ch05 `l5_1`: the auxiliary opposite
    extensions cut across at F, and their two endpoint pairs (C,C₁) and
    (D,D₁) have equal distance to F.  Each equality follows from the
    synthetic inner five-segment lemma, with no metric coordinates. -/
theorem coincident_bridge_pasch_equidistance
    {A B C D : Point}
    (hAB : A ≠ B) (hABC : Bet A B C) (hABD : Bet A B D) :
    ∃ C₁ D₁ E F : Point,
      Bet A D C₁ ∧ Bet A C D₁ ∧
      Bet A C₁ E ∧ Bet A D₁ E ∧
      Bet C F C₁ ∧ Bet D F D₁ ∧
      Cong D C₁ C D ∧ Cong C D₁ C D ∧
      Cong D₁ C₁ D C ∧
      Cong C₁ E C B ∧ Cong D₁ E D B ∧ Cong B C₁ E C ∧
      Cong F C F C₁ ∧ Cong F D F D₁ := by
  obtain ⟨C₁, D₁, E,
      hADC₁, hACD₁, hAC₁E, hAD₁E,
      hDC₁, hCD₁, hC₁E, hD₁E, hBC₁, hspan⟩ :=
    coincident_bridge_inner_span_congruent hAB hABC hABD
  obtain ⟨F, hCFC₁, hDFD₁⟩ :=
    inner_pasch D₁ C₁ A C D
      (bet_symm hACD₁) (bet_symm hADC₁)
  have hDC_DC₁ : Cong D C D C₁ :=
    cong_reverse_left (cong_symm hDC₁)
  have hD₁C_D₁C₁ : Cong D₁ C D₁ C₁ :=
    cong_trans (cong_reverse_left hCD₁)
      (cong_symm (cong_reverse_right hspan))
  have hFC_FC₁ : Cong F C F C₁ :=
    inner_five_segment hDFD₁ hDFD₁
      (congr_refl D D₁) (congr_refl F D₁)
      hDC_DC₁ hD₁C_D₁C₁
  have hCD_CD₁ : Cong C D C D₁ := cong_symm hCD₁
  have hC₁D_C₁D₁ : Cong C₁ D C₁ D₁ :=
    cong_trans (cong_reverse_left hDC₁)
      (cong_symm (cong_reverse_both hspan))
  have hFD_FD₁ : Cong F D F D₁ :=
    inner_five_segment hCFC₁ hCFC₁
      (congr_refl C C₁) (congr_refl F C₁)
      hCD_CD₁ hC₁D_C₁D₁
  exact ⟨C₁, D₁, E, F, hADC₁, hACD₁, hAC₁E, hAD₁E,
    hCFC₁, hDFD₁, hDC₁, hCD₁, hspan,
    hC₁E, hD₁E, hBC₁, hFC_FC₁, hFD_FD₁⟩

/-- GeoCoq Ch05 `l5_1`, next extension-and-five-segment calculation.
    The point P is constructed beyond C from C₁, and R similarly from D₁.
    Here the required constructed incidences/congruences are explicit input,
    and the output is the nontrivial congruence RP ≡ FD₁. -/
theorem mirror_extension_congruence
    {C C₁ D₁ F P R : Point}
    (hCFC₁ : Bet C F C₁)
    (hC₁CP : Bet C₁ C P)
    (hD₁CR : Bet D₁ C R)
    (hCP : Cong C P C D₁)
    (hCR : Cong C R C F)
    (hD₁C : D₁ ≠ C) : Cong R P F D₁ := by
  have hPCF : Bet P C F :=
    bet_symm (bet_exchange (bet_symm hCFC₁) hC₁CP)
  have hD₁C_PC : Cong D₁ C P C :=
    cong_symm (cong_reverse_both hCP)
  exact five_segment D₁ P C C R F P D₁
    hD₁C_PC hCR (cong_pseudo_reflexivity D₁ P)
    hCP hD₁CR hPCF hD₁C

/-- In the symmetric Ch05 bridge, C₁ ≠ C forces D₁ ≠ C.  Otherwise
    congruence identity would collapse C,D,C₁ to one point. -/
theorem mirror_extension_separated
    {C C₁ D D₁ : Point}
    (hDC₁ : Cong D C₁ C D)
    (hCD₁ : Cong C D₁ C D)
    (hCC₁ : C ≠ C₁) : D₁ ≠ C := by
  intro hD₁C
  have hCD : C = D :=
    cong_identity C D C (by
      simpa [hD₁C] using (cong_symm hCD₁))
  have hDC₁eq : D = C₁ :=
    cong_identity D C₁ D (by simpa [hCD] using hDC₁)
  exact hCC₁ (hCD.trans hDC₁eq)

/-- Complete next two prolongations of the nontrivial branch of Ch05 l5_1.
    All outputs are built from the primitive segment-construction axiom. -/
theorem mirror_extension_construct
    {C C₁ D D₁ F : Point}
    (hCFC₁ : Bet C F C₁)
    (hDC₁ : Cong D C₁ C D)
    (hCD₁ : Cong C D₁ C D)
    (hCC₁ : C ≠ C₁) :
    ∃ P R : Point,
      Bet C₁ C P ∧ Bet D₁ C R ∧
      Cong C P C D₁ ∧ Cong C R C F ∧
      Cong R P F D₁ := by
  obtain ⟨P, hC₁CP, hCP⟩ :=
    segment_construction C₁ C C D₁
  obtain ⟨R, hD₁CR, hCR⟩ :=
    segment_construction D₁ C C F
  have hD₁C : D₁ ≠ C :=
    mirror_extension_separated hDC₁ hCD₁ hCC₁
  have hRP : Cong R P F D₁ :=
    mirror_extension_congruence hCFC₁ hC₁CP hD₁CR hCP hCR hD₁C
  exact ⟨P, R, hC₁CP, hD₁CR, hCP, hCR, hRP⟩

/-- GeoCoq Ch05 `l5_1`, its second FSC step: extend P-R to Q with
    RQ ≡ RP. Congruences from the Pasch midpoint and the previous bridge
    force DC ≡ QC. The station coincidence D₁=F is handled directly by
    congruence identity; otherwise use the primitive five-segment axiom. -/
theorem mirror_second_extension_congruence
    {C D D₁ F P R Q : Point}
    (hDFD₁ : Bet D F D₁)
    (hFD : Cong F D F D₁)
    (hRP : Cong R P F D₁)
    (hCP : Cong C P C D₁)
    (hCR : Cong C R C F)
    (hPRQ : Bet P R Q)
    (hRQ : Cong R Q R P) : Cong D C Q C := by
  have hD₁C_PC : Cong D₁ C P C :=
    cong_symm (cong_reverse_both hCP)
  by_cases hD₁F : D₁ = F
  · have hFD_eq : F = D :=
      cong_identity F D F (by simpa [hD₁F] using hFD)
    have hRP_eq : R = P :=
      cong_identity R P F (by simpa [hD₁F] using hRP)
    have hRQ_eq : R = Q :=
      cong_identity R Q R (by simpa [hRP_eq] using hRQ)
    have hD₁D : D₁ = D := hD₁F.trans hFD_eq
    have hPQ : P = Q := hRP_eq.symm.trans hRQ_eq
    simpa [hD₁D, hPQ] using hD₁C_PC
  · have hD₁F_PR : Cong D₁ F P R :=
      cong_symm (cong_reverse_both hRP)
    have hRQ_FD : Cong R Q F D :=
      cong_trans hRQ (cong_trans hRP (cong_symm hFD))
    have hFD_RQ : Cong F D R Q := cong_symm hRQ_FD
    have hFC_RC : Cong F C R C :=
      cong_symm (cong_reverse_both hCR)
    exact five_segment D₁ P F R D Q C C
      hD₁F_PR hFD_RQ hD₁C_PC hFC_RC
      (bet_symm hDFD₁) hPRQ hD₁F

/-- GeoCoq Ch05 `l5_1` (Tarski's Satz 5.1): two points on the same ray
    beyond B are comparable in betweenness.  This is derived solely from
    Tarski's Bet/Cong axioms.  In particular, no line-order axiom,
    ColSegmentClosed, coordinate field, or analytic geometry is imported. -/
theorem ray_bet_comparable_tarski
    {A B C D : Point}
    (hAB : A ≠ B)
    (hABC : Bet A B C)
    (hABD : Bet A B D) :
    Bet A C D ∨ Bet A D C := by
  obtain ⟨C₁, D₁, E, F,
      hADC₁, hACD₁, hAC₁E, hAD₁E,
      hCFC₁, hDFD₁, hDC₁, hCD₁, hspan,
      hC₁E, _, _, hFC_FC₁, hFD_FD₁⟩ :=
    coincident_bridge_pasch_equidistance hAB hABC hABD
  by_cases hCC₁ : C = C₁
  · right
    simpa [← hCC₁] using hADC₁
  · obtain ⟨P, R, hC₁CP, hD₁CR, hCP, hCR, hRP⟩ :=
      mirror_extension_construct hCFC₁ hDC₁ hCD₁ hCC₁
    obtain ⟨Q, hPRQ, hRQ⟩ :=
      segment_construction P R R P
    have hDC_QC : Cong D C Q C :=
      mirror_second_extension_congruence
        hDFD₁ hFD_FD₁ hRP hCP hCR hPRQ hRQ
    have hCP_CQ : Cong C P C Q :=
      cong_trans hCP (cong_trans hCD₁
        (cong_reverse_both hDC_QC))
    have hFCne : F ≠ C := by
      intro hFC
      have hzero : C = C₁ :=
        cong_identity C C₁ C (by
          simpa [hFC] using (cong_symm hFC_FC₁))
      exact hCC₁ hzero
    have hRCne : R ≠ C := by
      intro hRC
      have hzero : C = F :=
        cong_identity C F C (by
          simpa [hRC] using (cong_symm hCR))
      exact hFCne hzero.symm
    have hD₁P_D₁Q : Cong D₁ P D₁ Q :=
      col_equidistant_of_two_stations hRCne
        (Or.inl (bet_symm hD₁CR))
        (cong_symm hRQ) hCP_CQ
    have hCD₁ne : C ≠ D₁ :=
      (mirror_extension_separated hDC₁ hCD₁ hCC₁).symm
    have hBCD₁ : Bet B C D₁ := bet_exchange hABC hACD₁
    have hCD₁E : Bet C D₁ E := bet_exchange hACD₁ hAD₁E
    have hBP_BQ : Cong B P B Q :=
      col_equidistant_of_two_stations hCD₁ne
        (Or.inr (Or.inr hBCD₁)) hCP_CQ hD₁P_D₁Q
    have hEP_EQ : Cong E P E Q :=
      col_equidistant_of_two_stations hCD₁ne
        (Or.inl hCD₁E) hCP_CQ hD₁P_D₁Q
    have hABC₁ : Bet A B C₁ := bet_extend hABD hADC₁
    have hBC₁E : Bet B C₁ E := bet_exchange hABC₁ hAC₁E
    have hBEne : B ≠ E := by
      intro hBE
      have hBC₁eq : B = C₁ :=
        between_identity B C₁ (by
          simpa [← hBE] using hBC₁E)
      have hCB : C = B :=
        cong_identity C B B (by
          have h : Cong B B C B := by
            simpa [← hBC₁eq, ← hBE] using hC₁E
          exact cong_symm h)
      exact hCC₁ (hCB.trans hBC₁eq)
    have hC₁P_C₁Q : Cong C₁ P C₁ Q :=
      col_equidistant_of_two_stations hBEne
        (Or.inr (Or.inl (bet_symm hBC₁E)))
        hBP_BQ hEP_EQ
    have hPP_PQ : Cong P P P Q :=
      col_equidistant_of_two_stations hCC₁
        (Or.inr (Or.inr (bet_symm hC₁CP)))
        hCP_CQ hC₁P_C₁Q
    have hPQ : P = Q := cong_identity P Q P (cong_symm hPP_PQ)
    have hPR : P = R :=
      between_identity P R (by simpa [← hPQ] using hPRQ)
    have hFD₁eq : F = D₁ :=
      cong_identity F D₁ P (by
        have hzero : Cong P P F D₁ := by
          simpa [← hPR] using hRP
        exact cong_symm hzero)
    have hFD_eq : F = D :=
      cong_identity F D F (by
        simpa [← hFD₁eq] using hFD_FD₁)
    have hD₁D_eq : D₁ = D := hFD₁eq.symm.trans hFD_eq
    left
    simpa [hD₁D_eq] using hACD₁

/-! ### Full line-order consequences of GeoCoq Ch05 l5_1 -/

/-- GeoCoq Ch05 `l5_2`: compare the portions beyond a common station. -/
theorem ray_bet_comparable_after_station
    {A B C D : Point}
    (hAB : A ≠ B) (hABC : Bet A B C) (hABD : Bet A B D) :
    Bet B C D ∨ Bet B D C := by
  rcases ray_bet_comparable_tarski hAB hABC hABD with hACD | hADC
  · exact Or.inl (bet_exchange hABC hACD)
  · exact Or.inr (bet_exchange hABD hADC)

/-- GeoCoq Ch05 `l5_3`: two points inside one segment are linearly ordered. -/
theorem bet_internal_totality {A B C D : Point}
    (hABD : Bet A B D) (hACD : Bet A C D) :
    Bet A B C ∨ Bet A C B := by
  obtain ⟨P, hDAP, hAP⟩ := segment_extension_nontrivial D A
  have hPAB : Bet P A B := bet_inner_trans (bet_symm hDAP) hABD
  have hPAC : Bet P A C := bet_inner_trans (bet_symm hDAP) hACD
  rcases ray_bet_comparable_tarski (Ne.symm hAP) hPAB hPAC with
    hPBC | hPCB
  · exact Or.inl (bet_exchange hPAB hPBC)
  · exact Or.inr (bet_exchange hPAC hPCB)

/-- GeoCoq Ch06 `l6_16_1` in a symmetric form.  When S and X lie
    on the line through P,Q (P≠Q), then X,P,S are collinear.  Each of the
    nine order configurations is handled by the proven Ch05 comparisons
    and the primitive Pasch-derived betweenness rules. -/
theorem col_transfer_on_line {P Q S X : Point}
    (hPQ : P ≠ Q)
    (hS : Col S P Q) (hX : Col X P Q) :
    Col X P S := by
  rcases hS with hSPQ | hPQS | hQSP
  · rcases hX with hXPQ | hPQX | hQXP
    · have hQPS : Bet Q P S := bet_symm hSPQ
      have hQPX : Bet Q P X := bet_symm hXPQ
      rcases ray_bet_comparable_tarski (Ne.symm hPQ) hQPS hQPX with
        hQSX | hQXS
      · exact Or.inr (Or.inl (bet_exchange hQPS hQSX))
      · exact Or.inr (Or.inr (bet_symm (bet_exchange hQPX hQXS)))
    · have hSQX : Bet S Q X := bet_outer_trans hSPQ hPQX hPQ
      exact Or.inl (bet_symm (bet_extend hSPQ hSQX))
    · exact Or.inl (bet_symm (bet_inner_trans hSPQ (bet_symm hQXP)))
  · rcases hX with hXPQ | hPQX | hQXP
    · have hXQS : Bet X Q S := bet_outer_trans hXPQ hPQS hPQ
      exact Or.inl (bet_extend hXPQ hXQS)
    · rcases ray_bet_comparable_tarski hPQ hPQS hPQX with hPSX | hPXS
      · exact Or.inr (Or.inl hPSX)
      · exact Or.inr (Or.inr (bet_symm hPXS))
    · exact Or.inr (Or.inr (bet_symm (bet_extend (bet_symm hQXP) hPQS)))
  · rcases hX with hXPQ | hPQX | hQXP
    · exact Or.inl (bet_inner_trans hXPQ (bet_symm hQSP))
    · exact Or.inr (Or.inl (bet_extend (bet_symm hQSP) hPQX))
    · rcases bet_internal_totality (bet_symm hQSP) (bet_symm hQXP) with
        hPSX | hPXS
      · exact Or.inr (Or.inl hPSX)
      · exact Or.inr (Or.inr (bet_symm hPXS))

/-- GeoCoq Ch06 `col_transitivity_1`, with no independent collinearity
    axiom: three distinct collinear stations fix their complete line. -/
theorem col_transitivity_tarski {P Q A B : Point}
    (hPQ : P ≠ Q) (hA : Col P Q A) (hB : Col P Q B) :
    Col P A B := by
  have hAPQ : Col A P Q := col_rotate (col_rotate hA)
  have hBPQ : Col B P Q := col_rotate (col_rotate hB)
  exact col_rotate (col_transfer_on_line hPQ hAPQ hBPQ)

/-- A segment whose endpoints lie on a fixed nondegenerate line remains
    on that line. This is the desired `ColSegmentClosed` theorem. -/
theorem col_segment_closed_tarski {O I X Y B : Point}
    (hOI : O ≠ I)
    (hX : Col O I X) (hY : Col O I Y)
    (hXYB : Bet X B Y) : Col O I B := by
  by_cases hXY : X = Y
  · have hXB : X = B := by
      apply between_identity X B
      simpa [← hXY] using hXYB
    simpa [← hXB] using hX
  · by_cases hOX : O = X
    · subst X
      have hBOY : Col B O Y := Or.inr (Or.inr (bet_symm hXYB))
      have hIOY : Col I O Y := col_swap hY
      exact col_rotate (col_transfer_on_line hXY hIOY hBOY)
    · have hOXY : Col O X Y := col_transitivity_tarski hOI hX hY
      have hBXY : Col B X Y := Or.inr (Or.inr (bet_symm hXYB))
      have hBXO : Col B X O :=
        col_transfer_on_line hXY hOXY hBXY
      have hBOX : Col B O X := col_swap_last hBXO
      have hIOX : Col I O X := col_swap hX
      exact col_rotate (col_transfer_on_line hOX hIOX hBOX)

/-- Every point of the line AB also lies on the (possibly degenerate)
    line CD whenever C,D lie on AB.  The nondegeneracy A≠B suffices;
    this is the synthetic line-incidence transfer rule. -/
theorem col_line_inclusion_tarski {A B C D S : Point}
    (hAB : A ≠ B)
    (hC : Col A B C) (hD : Col A B D)
    (hS : Col A B S) : Col C D S := by
  by_cases hCA : C = A
  · subst C
    have hDAB : Col D A B := col_rotate (col_rotate hD)
    have hSAB : Col S A B := col_rotate (col_rotate hS)
    exact col_rotate (col_transfer_on_line hAB hDAB hSAB)
  · have hCAB : Col C A B := col_rotate (col_rotate hC)
    have hDAB : Col D A B := col_rotate (col_rotate hD)
    have hSAB : Col S A B := col_rotate (col_rotate hS)
    have hDAC : Col D A C := col_transfer_on_line hAB hCAB hDAB
    have hSAC : Col S A C := col_transfer_on_line hAB hCAB hSAB
    exact col_rotate (col_transfer_on_line hCA
      (col_swap_last hDAC) (col_swap_last hSAC))

/-- Two distinct points C,D on AB give a complete equality of lines. -/
theorem col_line_extensionality_tarski {A B C D : Point}
    (hAB : A ≠ B) (hCD : C ≠ D)
    (hC : Col A B C) (hD : Col A B D) :
    ∀ S : Point, Col A B S ↔ Col C D S := by
  have hA : Col C D A :=
    col_line_inclusion_tarski hAB hC hD (col_left A B)
  have hB : Col C D B :=
    col_line_inclusion_tarski hAB hC hD (col_right A B)
  intro S
  exact ⟨col_line_inclusion_tarski hAB hC hD,
    col_line_inclusion_tarski hCD hA hB⟩

/-- GeoCoq Ch06 `l6_21`: two distinct noncoincident lines have
    at most one intersection. This needs no parallel axiom or coordinates. -/
theorem line_intersection_unique_tarski {A B C D P Q : Point}
    (hABC : ¬ Col A B C) (hCD : C ≠ D)
    (hPAB : Col A B P) (hQAB : Col A B Q)
    (hPCD : Col C D P) (hQCD : Col C D Q) : P = Q := by
  by_contra hPQ
  have hAB : A ≠ B := noncol_ne_first_second hABC
  have hlineAB : ∀ S, Col A B S ↔ Col P Q S :=
    col_line_extensionality_tarski hAB hPQ hPAB hQAB
  have hlineCD : ∀ S, Col C D S ↔ Col P Q S :=
    col_line_extensionality_tarski hCD hPQ hPCD hQCD
  have hC_AB : Col A B C :=
    (hlineAB C).mpr ((hlineCD C).mp (col_left C D))
  exact hABC hC_AB

/-- In a Tarski frame, the axes OI and OJ intersect only at O. -/
theorem frame_axes_intersection_only_origin_tarski
    (f : Frame Point) (W : Point)
    (hOI : Col f.O f.I W) (hOJ : Col f.O f.J W) :
    W = f.O := by
  exact line_intersection_unique_tarski f.noncol (Ne.symm f.O_ne_J)
    hOI (col_left f.O f.I) (col_swap hOJ) (col_right f.J f.O)

end TarskiField


/-! SOURCE: workstreams/Addition.lean -/


namespace TarskiField

/-!
Addition workstream for TarskiUnifiedRevised(1).lean.

This is a standalone extension module importing the unified base library.
The source file has not yet been typechecked.
All proofs use only the existing synthetic AddGraph definitions and the
previously derived zero-addition lemmas. No added axioms or sorry.
-/

section AdditionNondegenerate

variable {Point : Type u} [Plane Point]

/-- The zero-first-operand case of AddTotal is already proved synthetically. -/
theorem add_zero_left_existsUnique (f : Frame Point) (y : AxisPoint f) :
    ∃! z : AxisPoint f, AddGraph f (axisZero f) y z := by
  refine ⟨y, add_zero_left f y, ?_⟩
  intro z hz
  exact add_zero_left_unique f y z hz

/-- All unsolved existence/uniqueness for addition is in the nonzero branch. -/
theorem addTotal_iff_nonzero_first (f : Frame Point) :
    AddTotal f ↔
      ∀ x y : AxisPoint f, x ≠ axisZero f →
        ∃! z : AxisPoint f, AddGraph f x y z := by
  constructor
  · intro htotal x y _
    exact htotal x y
  · intro hnonzero x y
    by_cases hx : x = axisZero f
    · subst x
      exact add_zero_left_existsUnique f y
    · exact hnonzero x y hx

/-- A nonzero first operand removes the artificial degenerate disjunct.
    The remaining obligation is precisely the two-step parallel projection
    (first construct T, then its intersection with the scalar axis). -/
theorem addGraph_nonzero_iff (f : Frame Point)
    (x y z : AxisPoint f) (hx : x ≠ axisZero f) :
    AddGraph f x y z ↔
      ∃ T : Point,
        Parallel f.O f.J x.1 T ∧
        Parallel f.O f.I f.J T ∧
        Parallel f.J y.1 T z.1 := by
  constructor
  · rintro (⟨hzero, _⟩ | ⟨_, T, hfirst, hsecond, hthird⟩)
    · exact False.elim (hx (Subtype.ext hzero))
    · exact ⟨T, hfirst, hsecond, hthird⟩
  · intro hprojection
    refine Or.inr ⟨?_, hprojection⟩
    intro hzero
    exact hx (Subtype.ext hzero)

/-- Addition's functionality is also automatic in the degenerate case. -/
theorem addFunctional_iff_nonzero_first (f : Frame Point) :
    AddFunctional f ↔
      ∀ x y z w : AxisPoint f,
        x ≠ axisZero f →
        AddGraph f x y z → AddGraph f x y w → z = w := by
  constructor
  · intro hfunctional x y z w _ hz hw
    exact hfunctional x y z w hz hw
  · intro hnonzero x y z w hz hw
    by_cases hx : x = axisZero f
    · subst x
      have hz' : z = y := add_zero_left_unique f y z hz
      have hw' : w = y := add_zero_left_unique f y w hw
      exact hz'.trans hw'.symm
    · exact hnonzero x y z w hx hz hw

/-- In the purely synthetic language, a directional projection is the
    intersection of the target line AB with some line through P parallel
    to the given direction UV.  Recording the auxiliary endpoint W avoids
    a premature appeal to the uniqueness of the line through two points. -/
def WeakDirectionalProjection
    (A B U V P Q : Point) : Prop :=
  Col A B Q ∧ ∃ W : Point, Parallel U V P W ∧ Col P W Q

/-- The coincident-lines branch of transitivity is only propositional
    composition; no parallel postulate is used. -/
theorem parallel_trans_of_first_coincident
    {A B C D E F : Point}
    (hAC : Parallel A B C D)
    (hsame : ∀ P : Point, Col A B P ↔ Col C D P)
    (hCE : Parallel C D E F) :
    Parallel A B E F := by
  rcases hAC with ⟨hAB, _, _⟩
  rcases hCE with ⟨_, hEF, hsame' | hdisjoint⟩
  · exact ⟨hAB, hEF, Or.inl
      (fun P => (hsame P).trans (hsame' P))⟩
  · refine ⟨hAB, hEF, Or.inr ?_⟩
    intro P hp
    exact hdisjoint P ⟨(hsame P).mp hp.1, hp.2⟩

/-- Likewise when the second pair of parallel lines coincides. -/
theorem parallel_trans_of_second_coincident
    {A B C D E F : Point}
    (hAC : Parallel A B C D)
    (hCE : Parallel C D E F)
    (hsame : ∀ P : Point, Col C D P ↔ Col E F P) :
    Parallel A B E F := by
  rcases hAC with ⟨hAB, _, hsame' | hdisjoint⟩
  · exact ⟨hAB, hCE.2.1,
      Or.inl (fun P => (hsame' P).trans (hsame P))⟩
  · refine ⟨hAB, hCE.2.1, Or.inr ?_⟩
    intro P hp
    exact hdisjoint P ⟨hp.1, (hsame P).mpr hp.2⟩

/-- Full transitivity is a short consequence of Playfair's uniqueness
    principle: if the two outer lines meet, they are the two lines through
    their intersection parallel to the middle line and must coincide;
    otherwise they are disjoint.  Deriving Playfair itself from `Plane.euclid`
    is the separate Euclidean-geometry proof obligation in GeoCoq Ch12. -/
theorem parallel_trans_of_playfair
    (hPlayfair : ∀ A B C D E F P : Point,
      Parallel A B C D →
      Parallel A B E F →
      Col C D P → Col E F P →
      ∀ Q : Point, Col C D Q ↔ Col E F Q)
    {A B C D E F : Point}
    (hABCD : Parallel A B C D)
    (hCDEF : Parallel C D E F) :
    Parallel A B E F := by
  classical
  by_cases hint : ∃ P : Point, Col A B P ∧ Col E F P
  · obtain ⟨P, hPAB, hPEF⟩ := hint
    have hsame : ∀ Q : Point,
        Col A B Q ↔ Col E F Q :=
      hPlayfair C D A B E F P
        (parallel_symm hABCD) hCDEF hPAB hPEF
    exact ⟨hABCD.1, hCDEF.2.1, Or.inl hsame⟩
  · refine ⟨hABCD.1, hCDEF.2.1, Or.inr ?_⟩
    intro P hp
    exact hint ⟨P, hp⟩

/-- Retargeting one defining endpoint of a parallel line is purely logical
    once the *neutral incidence* lemma equating the two line predicates has
    been supplied.  GeoCoq names the corresponding normalization
    `par_col_par`. -/
theorem parallel_retarget_right_of_line_eq
    {A B C D E : Point}
    (hparallel : Parallel A B C D)
    (hCE : C ≠ E)
    (hline : ∀ P : Point, Col C D P ↔ Col C E P) :
    Parallel A B C E := by
  rcases hparallel with ⟨hAB, _, hsame | hdisjoint⟩
  · exact ⟨hAB, hCE,
      Or.inl (fun P => (hsame P).trans (hline P))⟩
  · refine ⟨hAB, hCE, Or.inr ?_⟩
    intro P hp
    exact hdisjoint P ⟨hp.1, (hline P).mpr hp.2⟩

/-- Parallel-through-a-point has an elementary incidence proof when the
    chosen point already lies on the line: choose the same line, but use P
    as one of its defining points. -/
theorem parallel_through_point_on_line
    (hline_two_points : ∀ A B C D : Point,
      A ≠ B → C ≠ D →
      Col A B C → Col A B D →
      ∀ S : Point, Col A B S ↔ Col C D S)
    (A B P : Point) (hAB : A ≠ B) (hP : Col A B P) :
    ∃ Q : Point, Parallel A B P Q := by
  by_cases hPA : P = A
  · subst P
    exact ⟨B, parallel_refl hAB⟩
  · have hsame : ∀ S : Point, Col A B S ↔ Col P A S :=
      hline_two_points A B P A hAB hPA hP (col_left A B)
    exact ⟨A, hAB, hPA, Or.inl hsame⟩

/-- With ordinary line-incidence uniqueness available, the neutral
    parallel-through-point theorem reduces completely to points *outside*
    the given line.  This is precisely the case handled via two
    perpendicular constructions in GeoCoq Ch12 `parallel_existence`. -/
theorem parallel_through_iff_off_line
    (hline_two_points : ∀ A B C D : Point,
      A ≠ B → C ≠ D →
      Col A B C → Col A B D →
      ∀ S : Point, Col A B S ↔ Col C D S) :
    (∀ A B P : Point, A ≠ B →
      ∃ Q : Point, Parallel A B P Q) ↔
    (∀ A B P : Point, A ≠ B → ¬ Col A B P →
      ∃ Q : Point, Parallel A B P Q) := by
  constructor
  · intro h A B P hAB _
    exact h A B P hAB
  · intro hOff A B P hAB
    by_cases hcol : Col A B P
    · exact parallel_through_point_on_line
        hline_two_points A B P hAB hcol
    · exact hOff A B P hAB hcol

/-- An unconditional Tarski derivation: if P belongs to AB, the same
    nondegenerate line can be named with endpoint P.  Neutral incidence
    is supplied by the already proved Ch06 theorem, not an assumption. -/
theorem parallel_through_point_on_line_tarski
    {A B P : Point} (hAB : A ≠ B) (hP : Col A B P) :
    ∃ Q : Point, Parallel A B P Q := by
  exact parallel_through_point_on_line
    (fun A B C D hAB hCD hC hD =>
      col_line_extensionality_tarski hAB hCD hC hD)
    A B P hAB hP

/-- Exact remaining case of the full parallel construction theorem,
    with no external incidence assumptions. -/
theorem parallel_through_iff_off_line_tarski :
    (∀ A B P : Point, A ≠ B →
      ∃ Q : Point, Parallel A B P Q) ↔
    (∀ A B P : Point, A ≠ B → ¬ Col A B P →
      ∃ Q : Point, Parallel A B P Q) := by
  exact parallel_through_iff_off_line
    (fun A B C D hAB hCD hC hD =>
      col_line_extensionality_tarski hAB hCD hC hD)

/-- The on-reference-line case of Playfair's uniqueness theorem is already
    a theorem of the *definition* of Parallel: both candidate lines pass
    through P on the reference line, so both coincide with that line. -/
theorem playfair_on_reference_line_tarski
    {A B C D E F P : Point}
    (hCD : Parallel A B C D)
    (hEF : Parallel A B E F)
    (hPbase : Col A B P)
    (hPCD : Col C D P)
    (hPEF : Col E F P) :
    ∀ Q : Point, Col C D Q ↔ Col E F Q := by
  have hsameCD : ∀ Q : Point, Col A B Q ↔ Col C D Q :=
    parallel_same_of_intersection hCD hPbase hPCD
  have hsameEF : ∀ Q : Point, Col A B Q ↔ Col E F Q :=
    parallel_same_of_intersection hEF hPbase hPEF
  intro Q
  exact (hsameCD Q).symm.trans (hsameEF Q)

/-- Like parallel existence, proving full Playfair amounts precisely to
    proving its genuinely Euclidean case with P off the reference line. -/
theorem playfair_iff_off_reference_line_tarski :
    (∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ Q : Point, Col C D Q ↔ Col E F Q) ↔
    (∀ A B C D E F P : Point,
      ¬ Col A B P →
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ Q : Point, Col C D Q ↔ Col E F Q) := by
  constructor
  · intro h A B C D E F P _ hCD hEF hPCD hPEF
    exact h A B C D E F P hCD hEF hPCD hPEF
  · intro hOff A B C D E F P hCD hEF hPCD hPEF
    by_cases hPbase : Col A B P
    · exact playfair_on_reference_line_tarski
        hCD hEF hPbase hPCD hPEF
    · exact hOff A B C D E F P hPbase hCD hEF hPCD hPEF

/-- In the genuinely Euclidean case of Playfair, a candidate parallel
    through an external point is a *strict* parallel: the two lines do not
    intersect. This is the first reduction in GeoCoq's tarski_playfair. -/
theorem playfair_strict_of_off_reference_tarski
    {A B C D P : Point}
    (hPar : Parallel A B C D)
    (hPoff : ¬ Col A B P)
    (hPCD : Col C D P) :
    ∀ S : Point, ¬ (Col A B S ∧ Col C D S) := by
  rcases hPar with ⟨_, _, hsame | hdisj⟩
  · exact False.elim (hPoff ((hsame P).mpr hPCD))
  · exact hdisj

/-- If two nondegenerate lines are different, one of the endpoints of the
    second line lies outside the first. The proof uses genuine Tarski line
    extensionality, already derived from the primitive axioms. -/
theorem playfair_distinct_lines_have_external_endpoint_tarski
    {C D E F : Point}
    (hCD : C ≠ D) (hEF : E ≠ F)
    (hdiff : ¬ ∀ S : Point, Col C D S ↔ Col E F S) :
    ¬ Col C D E ∨ ¬ Col C D F := by
  classical
  by_cases hE : Col C D E
  · by_cases hF : Col C D F
    · exact False.elim
        (hdiff (col_line_extensionality_tarski hCD hEF hE hF))
    · exact Or.inr hF
  · exact Or.inl hE

/-- Playfair's remaining case begins with two strict parallels and an
    endpoint outside the rival line. The subsequent two-sides argument is
    precisely the genuinely Euclidean part and remains a separate theorem. -/
theorem playfair_off_reference_preparation_tarski
    {A B C D E F P : Point}
    (hPoff : ¬ Col A B P)
    (hCD : Parallel A B C D)
    (hEF : Parallel A B E F)
    (hPCD : Col C D P)
    (hPEF : Col E F P)
    (hdiff : ¬ ∀ S : Point, Col C D S ↔ Col E F S) :
    (∀ S : Point, ¬ (Col A B S ∧ Col C D S)) ∧
    (∀ S : Point, ¬ (Col A B S ∧ Col E F S)) ∧
    (¬ Col C D E ∨ ¬ Col C D F) := by
  refine ⟨playfair_strict_of_off_reference_tarski hCD hPoff hPCD,
    playfair_strict_of_off_reference_tarski hEF hPoff hPEF, ?_⟩
  exact playfair_distinct_lines_have_external_endpoint_tarski
    hCD.2.1 hEF.2.1 hdiff

/-- A segment entirely on a strict parallel cannot cross the reference line.
    This is the elementary no-crossing fact behind the one-side relation
    used in the synthetic Playfair argument. -/
theorem playfair_parallel_segment_no_crossing_tarski
    {A B C D P X Y T : Point}
    (hpar : Parallel A B C D)
    (hPoff : ¬ Col A B P)
    (hPline : Col C D P)
    (hX : Col C D X)
    (hY : Col C D Y)
    (hT : Plane.Bet X T Y) :
    ¬ Col A B T := by
  intro hTbase
  have hdisjoint : ∀ S, ¬ (Col A B S ∧ Col C D S) :=
    playfair_strict_of_off_reference_tarski hpar hPoff hPline
  have hTline : Col C D T :=
    col_segment_closed_tarski hpar.2.1 hX hY hT
  exact hdisjoint T ⟨hTbase, hTline⟩

/-- A segment from the reference line to a parallel line meets the
    reference line only at its prescribed endpoint. This follows from
    the previously proved uniqueness of line intersections. -/
theorem playfair_transversal_meets_base_once_tarski
    {A B C D P X Y T : Point}
    (hpar : Parallel A B C D)
    (hPoff : ¬ Col A B P)
    (hPline : Col C D P)
    (hXbase : Col A B X)
    (hYline : Col C D Y)
    (hTbase : Col A B T)
    (hXT_Y : Plane.Bet X T Y) :
    T = X := by
  have hdisjoint : ∀ S, ¬ (Col A B S ∧ Col C D S) :=
    playfair_strict_of_off_reference_tarski hpar hPoff hPline
  have hYoff : ¬ Col A B Y := by
    intro hYbase
    exact hdisjoint Y ⟨hYbase, hYline⟩
  have hYX : Y ≠ X := by
    intro hYX
    exact hYoff (hYX ▸ hXbase)
  exact line_intersection_unique_tarski hYoff hYX
    hTbase hXbase (Or.inr (Or.inl hXT_Y)) (col_right Y X)

/-- P and Q are on opposite sides of AB when their segment crosses AB
    and neither endpoint lies on AB. This uses only Tarski's primitives. -/
def OppositeSides (A B P Q : Point) : Prop :=
  ¬ Col A B P ∧ ¬ Col A B Q ∧
    ∃ X : Point, Col A B X ∧ Plane.Bet P X Q

theorem oppositeSides_symm_tarski {A B P Q : Point}
    (h : OppositeSides A B P Q) : OppositeSides A B Q P := by
  obtain ⟨hPoff, hQoff, X, hX, hPXQ⟩ := h
  exact ⟨hQoff, hPoff, X, hX, bet_symm hPXQ⟩

/-- The crossing point between opposite sides is unique. This is the
    single-intersection theorem applied to the transversal PQ. -/
theorem oppositeSides_crossing_unique_tarski {A B P Q : Point}
    (h : OppositeSides A B P Q) :
    ∃! X : Point, Col A B X ∧ Plane.Bet P X Q := by
  obtain ⟨hPoff, _hQoff, X, hXbase, hPXQ⟩ := h
  have hPQ : P ≠ Q := by
    intro hEq
    have hPX : P = X :=
      Plane.between_identity P X (by simpa [hEq] using hPXQ)
    exact hPoff (by simpa [← hPX] using hXbase)
  refine ⟨X, ⟨hXbase, hPXQ⟩, ?_⟩
  intro Y ⟨hYbase, hPYQ⟩
  exact line_intersection_unique_tarski hPoff hPQ
    hYbase hXbase
    (Or.inr (Or.inl (bet_symm hPYQ)))
    (Or.inr (Or.inl (bet_symm hPXQ)))

/-- Two points of a parallel line cannot lie on opposite sides of the
    reference line. This is the no-crossing step needed before the
    one-side/two-sides contradiction in the synthetic Playfair argument. -/
theorem playfair_parallel_line_not_opposite_sides_tarski
    {A B C D P Q : Point}
    (hpar : Parallel A B C D)
    (hPline : Col C D P) (hQline : Col C D Q) :
    ¬ OppositeSides A B P Q := by
  rintro ⟨hPoff, _, X, hXbase, hPXQ⟩
  have hNotX : ¬ Col A B X :=
    playfair_parallel_segment_no_crossing_tarski
      hpar hPoff hPline hPline hQline hPXQ
  exact hNotX hXbase

/-- A noncollinear wedge gives a genuinely nondegenerate transversal
    from Tarski's Euclid axiom: the resulting points X and Y differ.
    This nondegeneracy is needed when using XY as a line in Playfair's proof. -/
theorem playfair_euclid_wedge_nondegenerate_tarski
    {P B C D T : Point}
    (hPBC : ¬ Col P B C)
    (hPDT : Plane.Bet P D T)
    (hBDC : Plane.Bet B D C) :
    ∃ X Y : Point,
      Plane.Bet P B X ∧ Plane.Bet P C Y ∧
      Plane.Bet X T Y ∧ X ≠ Y := by
  have hPD : P ≠ D := by
    intro hEq
    apply hPBC
    have hBPC : Plane.Bet B P C := by
      simpa [← hEq] using hBDC
    exact Or.inr (Or.inr (bet_symm hBPC))
  obtain ⟨X, Y, hPBX, hPCY, hXTY⟩ :=
    Plane.euclid P B C D T hPDT hBDC hPD
  refine ⟨X, Y, hPBX, hPCY, hXTY, ?_⟩
  intro hXY
  have hPB : P ≠ B := noncol_ne_first_second hPBC
  have hPX : P ≠ X := by
    intro hEq
    have hPB' : P = B :=
      Plane.between_identity P B (by simpa [← hEq] using hPBX)
    exact hPB hPB'
  have hP_X_B : Col P X B :=
    Or.inr (Or.inl (bet_symm hPBX))
  have hP_X_C : Col P X C := by
    have hPCX : Plane.Bet P C X := by simpa [hXY] using hPCY
    exact Or.inr (Or.inl (bet_symm hPCX))
  have hline : ∀ Z : Point, Col P X Z ↔ Col P B Z :=
    col_line_extensionality_tarski hPX hPB
      (col_left P X) hP_X_B
  exact hPBC ((hline C).mp hP_X_C)

/-- A genuine invocation of Tarski's Euclid axiom.  When the two wedge rays
form lines strictly parallel to a reference line, their Euclid-constructed
endpoints lie on opposite sides of that reference line.  The wedge's crossing
point T lies on the reference line by hypothesis.  This is a synthetic
two-sides lemma, not a coordinate or metric interpretation. -/
theorem playfair_euclid_wedge_opposite_sides_tarski
    {L N P B C D T : Point}
    (hPBC : ¬ Col P B C)
    (hPDT : Plane.Bet P D T)
    (hBDC : Plane.Bet B D C)
    (hTbase : Col L N T)
    (hPBpar : Parallel L N P B)
    (hPCpar : Parallel L N P C)
    (hPoff : ¬ Col L N P) :
    ∃ X Y : Point, OppositeSides L N X Y := by
  obtain ⟨X, Y, hPBX, hPCY, hXTY, _⟩ :=
    playfair_euclid_wedge_nondegenerate_tarski hPBC hPDT hBDC
  have hXline : Col P B X := Or.inl hPBX
  have hYline : Col P C Y := Or.inl hPCY
  have hPBdisj : ∀ S, ¬ (Col L N S ∧ Col P B S) :=
    playfair_strict_of_off_reference_tarski hPBpar hPoff (col_left P B)
  have hPCdisj : ∀ S, ¬ (Col L N S ∧ Col P C S) :=
    playfair_strict_of_off_reference_tarski hPCpar hPoff (col_left P C)
  refine ⟨X, Y, ?_, ?_, ⟨T, hTbase, hXTY⟩⟩
  · intro hXbase
    exact hPBdisj X ⟨hXbase, hXline⟩
  · intro hYbase
    exact hPCdisj Y ⟨hYbase, hYline⟩

/-- Uniqueness of a nondegenerate oblique projection from the two geometric
    facts used in GeoCoq: Playfair uniqueness of parallel lines and the
    uniqueness of a line through two distinct points.  The source P is
    assumed outside the target line, avoiding the trivial P=Q branch. -/
theorem directional_projection_unique_of_playfair
    (hPlayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ S : Point, Col C D S ↔ Col E F S)
    (hline_two_points : ∀ A B C D : Point,
      A ≠ B → C ≠ D →
      Col A B C → Col A B D →
      ∀ S : Point, Col A B S ↔ Col C D S)
    (A B U V P Q R : Point)
    (hAB : A ≠ B)
    (hP_off_target : ¬ Col A B P)
    (hQ : Col A B Q) (hR : Col A B R)
    (hPQ : Parallel U V P Q)
    (hPR : Parallel U V P R) :
    Q = R := by
  classical
  by_contra hQR
  have hPQPR : ∀ S : Point, Col P Q S ↔ Col P R S :=
    hPlayfair U V P Q P R P hPQ hPR
      (col_left P Q) (col_left P R)
  have hRPQ : Col P Q R :=
    (hPQPR R).mpr (col_right P R)
  have hQRline : ∀ S : Point, Col P Q S ↔ Col Q R S :=
    hline_two_points P Q Q R hPQ.2.1 hQR
      (col_right P Q) hRPQ
  have hABline : ∀ S : Point, Col A B S ↔ Col Q R S :=
    hline_two_points A B Q R hAB hQR hQ hR
  have hP_on_QR : Col Q R P :=
    (hQRline P).mp (col_left P Q)
  exact hP_off_target ((hABline P).mpr hP_on_QR)

/-- The exact reduction used in GeoCoq's `project_existence`:
    parallel-through-a-point + transitivity of parallels + intersection of
    nonparallel lines yields a weak directional projection.  The two higher
    order arguments are *explicit unproved hypotheses* representing the
    remaining synthetic geometry lemmas, not newly postulated axioms. -/
theorem weak_directional_projection_exists
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ W : Point, Parallel A B P W)
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (A B U V P : Point)
    (hAB : A ≠ B) (hUV : U ≠ V)
    (htransverse : ¬ Parallel U V A B) :
    ∃ Q : Point, WeakDirectionalProjection A B U V P Q := by
  obtain ⟨W, hPW⟩ := hparallel_through U V P hUV
  have hnPW : ¬ Parallel P W A B := by
    intro hPAB
    exact htransverse (hparallel_trans hPW hPAB)
  obtain ⟨Q, hPQ, hQAB⟩ :=
    not_parallel_lines_intersect P W A B hPW.2.1 hAB hnPW
  exact ⟨Q, hQAB, W, hPW, hPQ⟩

/-- Specialization to the second projection of the `AddGraph` diagram:
    after constructing the parallel through T, it meets the scalar axis.
    Its endpoint need not yet be the normalized segment TZ; that is a
    distinct neutral-incidence proof obligation. -/
theorem second_weak_projection_exists
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ W : Point, Parallel A B P W)
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (f : Frame Point) (y : AxisPoint f) (T : Point) :
    ∃ z : AxisPoint f,
      ∃ W : Point, Parallel f.J y.1 T W ∧ Col T W z.1 := by
  obtain ⟨Q, hQAB, W, hTW, hTQ⟩ :=
    weak_directional_projection_exists hparallel_through hparallel_trans
      f.O f.I f.J y.1 T
      f.O_ne_I (f.J_ne_axis_point y.1 y.2)
      (fun h => frame_axis_not_parallel_JY f y (parallel_symm h))
  exact ⟨⟨Q, hQAB⟩, W, hTW, hTQ⟩

/-- Distinct parallel lines are disjoint once a defining point of the
    second line is known to lie off the first. -/
theorem parallel_off_line_disjoint
    {A B C D : Point}
    (h : Parallel A B C D)
    (hC : ¬ Col A B C)
    {Q : Point} (hQ : Col C D Q) :
    ¬ Col A B Q := by
  rcases h with ⟨_, _, hsame | hdisj⟩
  · exact False.elim (hC ((hsame C).mpr (col_left C D)))
  · intro hQA
    exact hdisj Q ⟨hQA, hQ⟩

/-- The uniqueness half of synthetic addition follows from Playfair and
    the neutral line-incidence theorem alone.  In particular no algebraic
    cancellation/field-law assumption is smuggled into the construction. -/
theorem addFunctional_of_playfair_and_line_uniqueness
    (hPlayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ S : Point, Col C D S ↔ Col E F S)
    (hline_two_points : ∀ A B C D : Point,
      A ≠ B → C ≠ D →
      Col A B C → Col A B D →
      ∀ S : Point, Col A B S ↔ Col C D S)
    (f : Frame Point) :
    AddFunctional f := by
  intro x y z w hz hw
  by_cases hx : x = axisZero f
  · subst x
    have hz' : z = y := add_zero_left_unique f y z hz
    have hw' : w = y := add_zero_left_unique f y w hw
    exact hz'.trans hw'.symm
  · obtain ⟨T, hVertT, hHorzT, hLastZ⟩ :=
      (addGraph_nonzero_iff f x y z hx).mp hz
    obtain ⟨U, hVertU, hHorzU, hLastW⟩ :=
      (addGraph_nonzero_iff f x y w hx).mp hw
    have hSameHorz : ∀ P : Point,
        Col f.J T P ↔ Col f.J U P :=
      hPlayfair f.O f.I f.J T f.J U f.J
        hHorzT hHorzU (col_left f.J T) (col_left f.J U)
    have hU_on_JT : Col f.J T U :=
      (hSameHorz U).mpr (col_right f.J U)
    have hx_off_JT : ¬ Col f.J T x.1 := by
      intro hxJT
      exact (parallel_off_line_disjoint hHorzT f.noncol hxJT) x.2
    have hT_eq_U : T = U :=
      directional_projection_unique_of_playfair
        hPlayfair hline_two_points
        f.J T f.O f.J x.1 T U
        hHorzT.2.1 hx_off_JT
        (col_right f.J T) hU_on_JT hVertT hVertU
    subst U
    have hT_off_axis : ¬ Col f.O f.I T :=
      parallel_off_line_disjoint hHorzT f.noncol
        (col_right f.J T)
    have hz_eq_hw : z.1 = w.1 :=
      directional_projection_unique_of_playfair
        hPlayfair hline_two_points
        f.O f.I f.J y.1 T z.1 w.1
        f.O_ne_I hT_off_axis z.2 w.2 hLastZ hLastW
    exact Subtype.ext hz_eq_hw

/-- First projection at the level of two actual constructed lines.
    Through J draw a line horizontal to OI; through x draw a line vertical
    to OJ.  Those lines are nonparallel, hence have a meeting point T;
    moreover T cannot lie on the original scalar axis. -/
theorem first_weak_projection_exists
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ W : Point, Parallel A B P W)
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (f : Frame Point) (x : AxisPoint f) :
    ∃ T H W : Point,
      Parallel f.O f.I f.J H ∧
      Col f.J H T ∧
      Parallel f.O f.J x.1 W ∧
      Col x.1 W T ∧
      ¬ Col f.O f.I T := by
  obtain ⟨H, hHorizontal⟩ :=
    hparallel_through f.O f.I f.J f.O_ne_I
  have hnCross : ¬ Parallel f.O f.J f.J H := by
    intro hVerticalHorizontal
    apply frame_axes_not_parallel f
    exact hparallel_trans hHorizontal
      (parallel_symm hVerticalHorizontal)
  obtain ⟨T, hTJH, W, hVertical, hTxW⟩ :=
    weak_directional_projection_exists
      hparallel_through hparallel_trans
      f.J H f.O f.J x.1
      hHorizontal.2.1 f.O_ne_J hnCross
  have hTOffAxis : ¬ Col f.O f.I T :=
    parallel_off_line_disjoint hHorizontal f.noncol hTJH
  exact ⟨T, H, W, hHorizontal, hTJH,
    hVertical, hTxW, hTOffAxis⟩

/-- The second *strong* projection is obtained from the weak one once
    neutral incidence gives uniqueness of the line through two points.
    T must lie off the scalar axis, which was established by the first
    projection construction. -/
theorem second_strong_projection_of_line_uniqueness
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ W : Point, Parallel A B P W)
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (hline_of_col : ∀ {A B C : Point},
      A ≠ B → Col A B C → A ≠ C →
      ∀ P : Point, Col A B P ↔ Col A C P)
    (f : Frame Point) (y : AxisPoint f) (T : Point)
    (hT_off_axis : ¬ Col f.O f.I T) :
    ∃ z : AxisPoint f, Parallel f.J y.1 T z.1 := by
  obtain ⟨z, W, hTW, hcol⟩ :=
    second_weak_projection_exists
      hparallel_through hparallel_trans f y T
  have hTz : T ≠ z.1 := by
    intro h
    exact hT_off_axis (by simpa [h] using z.2)
  refine ⟨z, ?_⟩
  exact parallel_retarget_right_of_line_eq
    hTW hTz (hline_of_col hTW.2.1 hcol hTz)

/-- The first *strong* projection.  The nonzero input condition x≠O
    prevents the intermediate T from degenerating to J, which is required
    because `Parallel OI JT` demands J≠T. -/
theorem first_strong_projection_of_line_uniqueness
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ W : Point, Parallel A B P W)
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (hline_of_col : ∀ {A B C : Point},
      A ≠ B → Col A B C → A ≠ C →
      ∀ P : Point, Col A B P ↔ Col A C P)
    (f : Frame Point) (x : AxisPoint f)
    (hx : x ≠ axisZero f) :
    ∃ T : Point,
      Parallel f.O f.J x.1 T ∧
      Parallel f.O f.I f.J T ∧
      ¬ Col f.O f.I T := by
  obtain ⟨T, H, W, hHorizontal, hJT, hVertical, hxWT, hToff⟩ :=
    first_weak_projection_exists
      hparallel_through hparallel_trans f x
  have hxT : x.1 ≠ T := by
    intro heq
    exact hToff (heq ▸ x.2)
  have hVertStrong : Parallel f.O f.J x.1 T :=
    parallel_retarget_right_of_line_eq
      hVertical hxT (hline_of_col hVertical.2.1 hxWT hxT)
  have hxO : f.O ≠ x.1 := by
    intro hOx
    exact hx (Subtype.ext hOx.symm)
  have hJTne : f.J ≠ T := by
    intro hJeqT
    have hline : ∀ P : Point,
        Col f.O f.I P ↔ Col f.O x.1 P :=
      hline_of_col f.O_ne_I x.2 hxO
    have hVertJ : Parallel f.O f.J x.1 f.J := by
      simpa [hJeqT] using hVertStrong
    have hsame : ∀ P : Point,
        Col f.O f.J P ↔ Col x.1 f.J P :=
      parallel_same_of_intersection hVertJ
        (col_right f.O f.J) (col_right x.1 f.J)
    have hxOJ : Col f.O f.J x.1 :=
      (hsame x.1).mpr (col_left x.1 f.J)
    have hOxJ : Col f.O x.1 f.J :=
      col_rotate (col_swap hxOJ)
    exact f.noncol ((hline f.J).mpr hOxJ)
  have hHorzStrong : Parallel f.O f.I f.J T :=
    parallel_retarget_right_of_line_eq
      hHorizontal hJTne (hline_of_col hHorizontal.2.1 hJT hJTne)
  exact ⟨T, hVertStrong, hHorzStrong, hToff⟩

/-- The whole existence half of `AddTotal`, in exact synthetic form, follows
    from the two standard parallel lemmas and the neutral line-uniqueness
    lemma.  No addition functionality or field law is assumed here. -/
theorem addGraph_exists_of_parallel_construction
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ W : Point, Parallel A B P W)
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (hline_of_col : ∀ {A B C : Point},
      A ≠ B → Col A B C → A ≠ C →
      ∀ P : Point, Col A B P ↔ Col A C P)
    (f : Frame Point) (x y : AxisPoint f) :
    ∃ z : AxisPoint f, AddGraph f x y z := by
  by_cases hx : x = axisZero f
  · subst x
    exact ⟨y, add_zero_left f y⟩
  · obtain ⟨T, hvertical, hhorizontal, hTOffAxis⟩ :=
      first_strong_projection_of_line_uniqueness
        hparallel_through hparallel_trans hline_of_col f x hx
    obtain ⟨z, hfinal⟩ :=
      second_strong_projection_of_line_uniqueness
        hparallel_through hparallel_trans hline_of_col f y T hTOffAxis
    have hxpoint : x.1 ≠ f.O := by
      intro hzero
      exact hx (Subtype.ext hzero)
    exact ⟨z,
      Or.inr ⟨hxpoint, T, hvertical, hhorizontal, hfinal⟩⟩

theorem addTotal_of_parallel_construction_and_functional
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ W : Point, Parallel A B P W)
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (hline_of_col : ∀ {A B C : Point},
      A ≠ B → Col A B C → A ≠ C →
      ∀ P : Point, Col A B P ↔ Col A C P)
    (f : Frame Point) (hfunctional : AddFunctional f) :
    AddTotal f := by
  intro x y
  obtain ⟨z, hz⟩ :=
    addGraph_exists_of_parallel_construction
      hparallel_through hparallel_trans hline_of_col f x y
  exact ⟨z, hz, fun w hw => hfunctional x y w z hw hz⟩

/-- **Unified geometric reduction:** two standard Tarski/Euclid results
    (existence of a parallel through a point, uniqueness of parallels
    through a point) and the neutral uniqueness of a line through two
    distinct points suffice to prove AddTotal.  Every remaining assumption
    is explicitly a synthetic-geometric lemma, not a field axiom. -/
theorem addTotal_of_parallel_existence_playfair_incidence
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ W : Point, Parallel A B P W)
    (hPlayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ S : Point, Col C D S ↔ Col E F S)
    (hline_two_points : ∀ A B C D : Point,
      A ≠ B → C ≠ D →
      Col A B C → Col A B D →
      ∀ S : Point, Col A B S ↔ Col C D S)
    (f : Frame Point) :
    AddTotal f := by
  have hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F := by
    intro A B C D E F hAB hCD
    exact parallel_trans_of_playfair hPlayfair hAB hCD
  have hline_of_col : ∀ {A B C : Point},
      A ≠ B → Col A B C → A ≠ C →
      ∀ P : Point, Col A B P ↔ Col A C P := by
    intro A B C hAB hcol hAC
    exact hline_two_points A B A C hAB hAC (col_left A B) hcol
  have hfunctional : AddFunctional f :=
    addFunctional_of_playfair_and_line_uniqueness
      hPlayfair hline_two_points f
  exact addTotal_of_parallel_construction_and_functional
    hparallel_through hparallel_trans hline_of_col f hfunctional

/-- Precise assembly of AddTotal from the two geometric projections and
    their functionality.  The existential assumptions specify the synthetic
    construction to prove, so there is no hidden assumption that an
    arithmetic field already exists. -/
theorem addTotal_of_two_projections
    (f : Frame Point)
    (hfirst : ∀ x : AxisPoint f,
      x ≠ axisZero f →
      ∃ T : Point,
        Parallel f.O f.J x.1 T ∧
        Parallel f.O f.I f.J T)
    (hsecond : ∀ (y : AxisPoint f) (T : Point),
      ∃ z : AxisPoint f, Parallel f.J y.1 T z.1)
    (hfunctional : AddFunctional f) :
    AddTotal f := by
  intro x y
  by_cases hx : x = axisZero f
  · subst x
    exact add_zero_left_existsUnique f y
  · obtain ⟨T, hvertical, hhorizontal⟩ := hfirst x hx
    obtain ⟨z, hlast⟩ := hsecond y T
    have hxpoint : x.1 ≠ f.O := by
      intro hzero
      exact hx (Subtype.ext hzero)
    have hz : AddGraph f x y z :=
      Or.inr ⟨hxpoint, T, hvertical, hhorizontal, hlast⟩
    refine ⟨z, hz, ?_⟩
    intro w hw
    exact hfunctional x y w z hw hz

/-- A completed *first* projection immediately proves right-zero addition.
    No second projection construction or uniqueness theorem is needed. -/
theorem add_right_zero_of_first_projection
    (f : Frame Point) (x : AxisPoint f) (T : Point)
    (hx : x ≠ axisZero f)
    (hvertical : Parallel f.O f.J x.1 T)
    (hhorizontal : Parallel f.O f.I f.J T) :
    AddGraph f x (axisZero f) x := by
  have hxpoint : x.1 ≠ f.O := by
    intro hxO
    exact hx (Subtype.ext hxO)
  have hlast : Parallel f.J (axisZero f).1 T x.1 := by
    change Parallel f.J f.O T x.1
    exact parallel_reverse_both hvertical
  exact Or.inr ⟨hxpoint, T, hvertical, hhorizontal, hlast⟩

/-- Right-zero addition follows from mere existence of x+1 for every x,
    thus is not an independent field-law obligation after AddTotal. -/
theorem add_right_zero_of_addOne_exists
    (f : Frame Point)
    (hOne : ∀ x : AxisPoint f,
      ∃ z : AxisPoint f, AddGraph f x (axisOne f) z) :
    AddRightZeroLaw f := by
  intro x
  by_cases hx : x = axisZero f
  · subst x
    exact add_zero_left f (axisZero f)
  · obtain ⟨z, hz⟩ := hOne x
    obtain ⟨T, hvertical, hhorizontal, _⟩ :=
      (addGraph_nonzero_iff f x (axisOne f) z hx).mp hz
    exact add_right_zero_of_first_projection f x T hx
      hvertical hhorizontal

theorem add_right_zero_of_addTotal
    (f : Frame Point) (htotal : AddTotal f) : AddRightZeroLaw f :=
  add_right_zero_of_addOne_exists f (fun x =>
    let ⟨z, hz, _⟩ := htotal x (axisOne f)
    ⟨z, hz⟩)

/-- After AddTotal, commutativity is settled whenever either operand is O.
    The nonzero/nonzero case alone requires a new geometric diagram. -/
theorem add_comm_zero_branch_of_total
    (f : Frame Point) (htotal : AddTotal f)
    (x y z : AxisPoint f)
    (hzero : x = axisZero f ∨ y = axisZero f)
    (hxy : AddGraph f x y z) :
    AddGraph f y x z := by
  have hR0 : AddRightZeroLaw f := add_right_zero_of_addTotal f htotal
  rcases hzero with hx | hy
  · subst x
    have hzy : z = y := add_zero_left_unique f y z hxy
    subst z
    exact hR0 y
  · subst y
    obtain ⟨w, _, huniq⟩ := htotal x (axisZero f)
    have hx0 : AddGraph f x (axisZero f) x := hR0 x
    have hzx : z = x :=
      (huniq z hxy).trans (huniq x hx0).symm
    subst z
    exact add_zero_left f x

theorem addCommLaw_iff_nonzero_operands_of_total
    (f : Frame Point) (htotal : AddTotal f) :
    AddCommLaw f ↔
      ∀ x y z : AxisPoint f,
        x ≠ axisZero f → y ≠ axisZero f →
        AddGraph f x y z → AddGraph f y x z := by
  constructor
  · intro hcomm x y z _ _ hxy
    exact hcomm x y z hxy
  · intro hcomm x y z hxy
    by_cases hx : x = axisZero f
    · exact add_comm_zero_branch_of_total f htotal x y z
        (Or.inl hx) hxy
    · by_cases hy : y = axisZero f
      · exact add_comm_zero_branch_of_total f htotal x y z
          (Or.inr hy) hxy
      · exact hcomm x y z hx hy hxy

end AdditionNondegenerate

end TarskiField


/-! SOURCE: workstreams/Multiplication.lean -/


namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-!
## Tarski geometric multiplication: projection obligations and a completed reduction

This module imports the consolidated Tarski geometry source and uses only
its existing definitions and the two primitive Tarski relations.

There is no additional axiom. `MulFirstProjectionTotal` and
`MulSecondProjectionTotal` are explicitly named propositions still to be
derived from the Tarski Euclidean axiom; `mulTotal_of_two_projections` is a
theorem explaining how those geometric theorems prove totality of the exact
`MulGraph` definition. This file must not be presented as a verified module
until it has been merged and compiled in Lean.
-/

/-- The first geometric operation transfers a point on OI to the auxiliary
line OJ along lines parallel to IJ. Its existence and uniqueness are a
parallel-projection theorem, not an ordered-field axiom. -/
def MulFirstProjectionTotal (f : Frame Point) : Prop :=
  ∀ (y : AxisPoint f), y.1 ≠ f.O →
    ∃! W : Point,
      Col f.O f.J W ∧ Parallel f.I f.J y.1 W

/-- The second geometric operation projects from a nonzero point on OJ
to OI along the direction Jx. Its existence and uniqueness are a separate
Euclidean parallel-projection theorem. -/
def MulSecondProjectionTotal (f : Frame Point) : Prop :=
  ∀ (x : AxisPoint f) (W : Point),
    Col f.O f.J W → W ≠ f.O →
    ∃! z : AxisPoint f,
      Parallel f.J x.1 W z.1

/-!
### Synthetic central reflection

GeoCoq constructs a parallel through a point using perpendiculars and
midpoint/reflection lemmas before invoking Euclid to obtain intersections.
The elementary central-reflection construction, which follows already from
Tarski's segment construction and five-segment axioms, is proved here.
The general midpoint-existence theorem remains a separate geometric task.
-/

/-- M bisects AB, expressed in the language of betweenness and
congruence only. -/
def MulMidpoint (M A B : Point) : Prop :=
  Bet A M B ∧ Cong M A M B

/-- Reflecting a point A across a specified center M gives a unique
point B. This is Tarski segment construction, not vector subtraction. -/
theorem mul_reflection_exists_unique (M A : Point) :
    ∃! B : Point, MulMidpoint M A B := by
  obtain ⟨B, hB, huniq⟩ := opposite_exists_unique M A
  refine ⟨B, ⟨hB.1, cong_symm hB.2⟩, ?_⟩
  intro C hC
  exact huniq C ⟨hC.1, cong_symm hC.2⟩

/-- Central symmetry exchanges the endpoints of the bisected segment. -/
theorem mul_midpoint_reverse {M A B : Point}
    (h : MulMidpoint M A B) : MulMidpoint M B A :=
  ⟨bet_symm h.1, cong_symm h.2⟩

/-- The reflection of the reflection across the same center is the
original point. -/
theorem mul_reflection_involution {M A B C : Point}
    (hAB : MulMidpoint M A B)
    (hBC : MulMidpoint M B C) : A = C := by
  obtain ⟨A', _, huniq⟩ := mul_reflection_exists_unique M B
  have hAA' : A = A' := huniq A (mul_midpoint_reverse hAB)
  have hCA' : C = A' := huniq C hBC
  exact hAA'.trans hCA'.symm

/-- The center of a nondegenerate segment is distinct from its first
endpoint; this uses only the Tarski identity for zero-length congruence. -/
theorem mul_midpoint_center_ne_left {M A B : Point}
    (h : MulMidpoint M A B) (hAB : A ≠ B) : M ≠ A := by
  intro hMA
  subst M
  exact hAB (cong_identity A B A (cong_symm h.2))

/-- The center of a nondegenerate segment is distinct from its second
endpoint, without assuming any metric coordinate. -/
theorem mul_midpoint_center_ne_right {M A B : Point}
    (h : MulMidpoint M A B) (hAB : A ≠ B) : M ≠ B := by
  intro hMB
  subst M
  exact hAB (cong_identity B A B h.2).symm

/-- Reflecting a point different from the center produces a distinct point.
This is the nondegeneracy needed when the reflection becomes a line endpoint
in a later parallel construction. -/
theorem mul_reflection_distinct {M A B : Point}
    (h : MulMidpoint M A B) (hMA : M ≠ A) : A ≠ B := by
  intro hAB
  subst B
  exact hMA (between_identity A M h.1).symm

/-- If two nondegenerate Tarski lines intersect at `I` and `C` lies off
the first line, reflection of `C` across `I` produces a point on the
second line, on the opposite side of the first. This is the neutral
construction underlying GeoCoq's `not_par_two_sides`. -/
theorem not_par_two_sides_tarski
    {A B C D I : Point}
    (hCD : C ≠ D)
    (hIAB : Col A B I)
    (hICD : Col C D I)
    (hCoff : ¬ Col A B C) :
    ∃ Y : Point, Col C D Y ∧ OppositeSides A B C Y := by
  have hAB : A ≠ B := noncol_ne_first_second hCoff
  have hIC : I ≠ C := by
    intro h
    apply hCoff
    simpa [h] using hIAB
  obtain ⟨Y, hMid, _⟩ := mul_reflection_exists_unique I C
  have hCY : C ≠ Y := mul_reflection_distinct hMid hIC
  have hIY : I ≠ Y := mul_midpoint_center_ne_right hMid hCY
  have hlineCD : ∀ S : Point, Col C D S ↔ Col C I S :=
    col_line_extensionality_tarski hCD hIC.symm
      (col_left C D) hICD
  have hYCD : Col C D Y :=
    (hlineCD Y).mpr (Or.inl hMid.1)
  have hYoff : ¬ Col A B Y := by
    intro hYAB
    have hlineAB : ∀ S : Point, Col A B S ↔ Col I Y S :=
      col_line_extensionality_tarski hAB hIY hIAB hYAB
    have hCIY : Col I Y C := Or.inr (Or.inr hMid.1)
    exact hCoff ((hlineAB C).mpr hCIY)
  exact ⟨Y, hYCD, hCoff, hYoff, I, hIAB, hMid.1⟩

/-- Central reflection preserves congruence, using only Tarski's segment axioms. -/
theorem mul_reflection_preserves_cong
    {M P P' Q Q' : Point}
    (hP : MulMidpoint M P' P)
    (hQ : MulMidpoint M Q' Q) :
    Cong P Q P' Q' := by
  by_cases hPM : P = M
  · subst P
    have hP'M : P' = M :=
      (cong_identity M P' M hP.2).symm
    subst P'
    exact cong_symm hQ.2
  · obtain ⟨X, hP'PX, hPX⟩ :=
      segment_construction P' P Q M
    obtain ⟨X', hXP'X', hP'X'⟩ :=
      segment_construction X P' Q M
    obtain ⟨Y, hQ'QY, hQY⟩ :=
      segment_construction Q' Q P M
    obtain ⟨Y', hYQ'Y', hQ'Y'⟩ :=
      segment_construction Y Q' P M
    have hMPX : Bet M P X :=
      bet_exchange hP.1 hP'PX
    have hP'MX : Bet P' M X :=
      bet_extend hP.1 hP'PX
    have hXMP' : Bet X M P' :=
      bet_symm hP'MX
    have hX'P'M : Bet X' P' M :=
      bet_symm (bet_exchange hXMP' hXP'X')
    have hXMX' : Bet X M X' :=
      bet_extend hXMP' hXP'X'
    have hMQY : Bet M Q Y :=
      bet_exchange hQ.1 hQ'QY
    have hYQM : Bet Y Q M :=
      bet_symm hMQY
    have hYMQ' : Bet Y M Q' :=
      bet_symm (bet_extend hQ.1 hQ'QY)
    have hMQ'Y' : Bet M Q' Y' :=
      bet_exchange hYMQ' hYQ'Y'
    have hYMY' : Bet Y M Y' :=
      bet_extend hYMQ' hYQ'Y'
    have hQY_Q'Y' : Cong Q Y Q' Y' :=
      cong_trans hQY (cong_symm hQ'Y')
    have hMY_MY' : Cong M Y M Y' :=
      segment_cong_add hMQY hMQ'Y'
        (cong_symm hQ.2) hQY_Q'Y'
    have hMP_YQ : Cong M P Y Q :=
      cong_reverse_both (cong_symm hQY)
    have hMX_YM : Cong M X Y M :=
      segment_cong_add hMPX hYQM hMP_YQ hPX
    have hMQ_X'P' : Cong M Q X' P' :=
      cong_symm (cong_reverse_both hP'X')
    have hMQ'_X'P' : Cong M Q' X' P' :=
      cong_trans hQ.2 hMQ_X'P'
    have hQ'Y'_P'M : Cong Q' Y' P' M :=
      cong_trans hQ'Y' (cong_reverse_both (cong_symm hP.2))
    have hMY'_X'M : Cong M Y' X' M :=
      segment_cong_add hMQ'Y' hX'P'M hMQ'_X'P' hQ'Y'_P'M
    have hMX_MY' : Cong M X M Y' :=
      cong_trans hMX_YM (cong_reverse_left hMY_MY')
    have hMX'_MY : Cong M X' M Y :=
      cong_trans
        (cong_reverse_left (cong_symm hMY'_X'M))
        (cong_symm hMY_MY')
    have hMX'_MY' : Cong M X' M Y' :=
      cong_trans hMX'_MY hMY_MY'
    have hMX_MX' : Cong M X M X' :=
      cong_trans hMX_MY' (cong_symm hMX'_MY')
    have hXM : X ≠ M := by
      intro hXM
      have hMPeq : M = P :=
        between_identity M P
          (by simpa [hXM] using hMPX)
      exact hPM hMPeq.symm
    have hX'Y'_YX : Cong X' Y' Y X :=
      five_segment X Y' M M X' Y Y' X
        (cong_reverse_both hMX_MY')
        hMX'_MY
        (cong_pseudo_reflexivity X Y')
        (cong_symm hMX_MY')
        hXMX' (bet_symm hYMY') hXM
    have hYX_Y'X' : Cong Y X Y' X' :=
      cong_reverse_right (cong_symm hX'Y'_YX)
    have hQM_Q'M : Cong Q M Q' M :=
      cong_symm (cong_reverse_both hQ.2)
    have hQX_Q'X' : Cong Q X Q' X' :=
      inner_five_segment
        hYQM (bet_symm hMQ'Y')
        (cong_reverse_both hMY_MY')
        hQM_Q'M hYX_Y'X' hMX_MX'
    have hPM_P'M : Cong P M P' M :=
      cong_symm (cong_reverse_both hP.2)
    exact inner_five_segment
      (bet_symm hMPX) hX'P'M
      (cong_reverse_both hMX_MX')
      hPM_P'M
      (cong_reverse_both hQX_Q'X')
      (cong_symm hQ.2)

/-- Point reflection preserves betweenness. -/
theorem mul_reflection_preserves_bet
    {M A B C A' B' C' : Point}
    (hA : MulMidpoint M A A')
    (hB : MulMidpoint M B B')
    (hC : MulMidpoint M C C')
    (hABC : Bet A B C) :
    Bet A' B' C' := by
  apply bet_of_three_segment_congruences hABC
  · exact mul_reflection_preserves_cong
      (mul_midpoint_reverse hA)
      (mul_midpoint_reverse hB)
  · exact mul_reflection_preserves_cong
      (mul_midpoint_reverse hB)
      (mul_midpoint_reverse hC)
  · exact mul_reflection_preserves_cong
      (mul_midpoint_reverse hA)
      (mul_midpoint_reverse hC)

/-- Point reflection preserves collinearity. -/
theorem mul_reflection_preserves_col
    {M A B C A' B' C' : Point}
    (hA : MulMidpoint M A A')
    (hB : MulMidpoint M B B')
    (hC : MulMidpoint M C C')
    (hABC : Col A B C) :
    Col A' B' C' := by
  rcases hABC with h | h | h
  · exact Or.inl (mul_reflection_preserves_bet hA hB hC h)
  · exact Or.inr (Or.inl (mul_reflection_preserves_bet hB hC hA h))
  · exact Or.inr (Or.inr (mul_reflection_preserves_bet hC hA hB h))

/-- A line outside the center is disjoint from its reflected image. -/
theorem centered_reflection_parallel_tarski
    {M A B A' B' : Point}
    (hAB : A ≠ B)
    (hM : ¬ Col A B M)
    (hA : MulMidpoint M A A')
    (hB : MulMidpoint M B B') :
    Parallel A B A' B' := by
  have hcong : Cong A B A' B' :=
    mul_reflection_preserves_cong
      (mul_midpoint_reverse hA)
      (mul_midpoint_reverse hB)
  have hA'B' : A' ≠ B' := by
    intro heq
    apply hAB
    exact cong_identity A B A'
      (by simpa [heq] using hcong)
  refine ⟨hAB, hA'B', Or.inr ?_⟩
  intro X hX
  obtain ⟨X', hXX', _⟩ :=
    mul_reflection_exists_unique M X
  have hX'image : Col A' B' X' :=
    mul_reflection_preserves_col hA hB hXX' hX.1
  have hX'original : Col A B X' :=
    mul_reflection_preserves_col
      (mul_midpoint_reverse hA)
      (mul_midpoint_reverse hB)
      hXX' hX.2
  by_cases hXX : X = X'
  · have hXM : X = M :=
      between_identity X M
        (by simpa [hXX] using hXX'.1)
    exact hM (by simpa [hXM] using hX.1)
  · have hline :
        ∀ S : Point, Col A B S ↔ Col X X' S :=
      col_line_extensionality_tarski
        hAB hXX hX.1 hX'original
    have hMline : Col X X' M :=
      Or.inr (Or.inl (bet_symm hXX'.1))
    exact hM ((hline M).mpr hMline)

/-- A midpoint of the segment joining the external point P to A already
constructs the desired parallel through P: reflect the line AB across that
midpoint. This bypasses the general parallelogram/common-diagonals lemma.
The only missing input in this route is existence of the midpoint of AP. -/
theorem parallel_through_off_line_of_midpoint_tarski
    {A B P M : Point}
    (hAB : A ≠ B)
    (hPoff : ¬ Col A B P)
    (hMid : MulMidpoint M A P) :
    ∃ Q : Point, Parallel A B P Q := by
  have hAP : A ≠ P := by
    intro heq
    apply hPoff
    simpa [← heq] using (col_left A B)
  have hAM : A ≠ M :=
    (mul_midpoint_center_ne_left hMid hAP).symm
  have hMoff : ¬ Col A B M := by
    intro hMbase
    have hline : ∀ S : Point, Col A B S ↔ Col A M S :=
      col_line_extensionality_tarski
        hAB hAM (col_left A B) hMbase
    have hPonAM : Col A M P := Or.inl hMid.1
    exact hPoff ((hline P).mpr hPonAM)
  obtain ⟨Q, hBQ, _⟩ :=
    mul_reflection_exists_unique M B
  exact ⟨Q, centered_reflection_parallel_tarski
    hAB hMoff hMid hBQ⟩

/-- Two successive point reflections give a nondegenerate candidate through P,
    with the reflected endpoint still outside the original line AB. -/
theorem double_reflection_candidate_tarski
    {A B P : Point}
    (hAB : A ≠ B)
    (hP : ¬ Col A B P) :
    ∃ R Q : Point,
      MulMidpoint A P R ∧
      MulMidpoint B R Q ∧
      P ≠ Q ∧
      ¬ Col A B Q := by
  obtain ⟨R, hAR, _⟩ := mul_reflection_exists_unique A P
  obtain ⟨Q, hBQ, _⟩ := mul_reflection_exists_unique B R
  have hAP : A ≠ P := noncol_ne_first_third hP
  have hPR : P ≠ R := mul_reflection_distinct hAR hAP
  have hAneR : A ≠ R := mul_midpoint_center_ne_right hAR hPR
  have hRoff : ¬ Col A B R := by
    intro hRline
    have hline : ∀ S : Point, Col A B S ↔ Col A R S :=
      col_line_extensionality_tarski
        hAB hAneR (col_left A B) hRline
    apply hP
    exact (hline P).mpr (Or.inr (Or.inr hAR.1))
  have hBR : B ≠ R := by
    intro heq
    apply hRoff
    simpa only [← heq] using (col_right A B)
  have hRQ : R ≠ Q := mul_reflection_distinct hBQ hBR
  have hBneQ : B ≠ Q := mul_midpoint_center_ne_right hBQ hRQ
  have hQoff : ¬ Col A B Q := by
    intro hQline
    have hline : ∀ S : Point, Col A B S ↔ Col B Q S :=
      col_line_extensionality_tarski
        hAB hBneQ (col_right A B) hQline
    apply hRoff
    exact (hline R).mpr (Or.inr (Or.inr hBQ.1))
  have hPQ : P ≠ Q := by
    intro heq
    have hRBP : Bet R B P := by
      rw [heq]
      exact hBQ.1
    have hAon : Col P R A :=
      Or.inr (Or.inl (bet_symm hAR.1))
    have hBon : Col P R B :=
      Or.inr (Or.inl hRBP)
    have hline : ∀ S : Point, Col P R S ↔ Col A B S :=
      col_line_extensionality_tarski hPR hAB hAon hBon
    exact hP ((hline P).mp (col_left P R))
  exact ⟨R, Q, hAR, hBQ, hPQ, hQoff⟩

/-- If A and B lie on two sides of a triangle and P is outside AB,
    then P,R,Q are noncollinear, using only neutral Tarski incidence. -/
theorem midpoint_triangle_noncol_tarski
    {A B P R Q : Point}
    (hAB : A ≠ B)
    (hP : ¬ Col A B P)
    (hAR : MulMidpoint A P R)
    (hBQ : MulMidpoint B R Q) :
    ¬ Col P R Q := by
  have hAP : A ≠ P := noncol_ne_first_third hP
  have hPR : P ≠ R := mul_reflection_distinct hAR hAP
  have hRQ : R ≠ Q := by
    intro heq
    have hRB : R = B := by
      apply between_identity R B
      simpa [← heq] using hBQ.1
    apply hP
    exact Or.inr (Or.inr (by simpa [hRB] using hAR.1))
  intro hPRQ
  have hline : ∀ X : Point, Col P R X ↔ Col R Q X :=
    col_line_extensionality_tarski
      hPR hRQ (col_right P R) hPRQ
  have hAon : Col P R A :=
    Or.inr (Or.inl (bet_symm hAR.1))
  have hBon : Col P R B :=
    (hline B).mpr
      (Or.inr (Or.inl (bet_symm hBQ.1)))
  have hbase : ∀ X : Point, Col P R X ↔ Col A B X :=
    col_line_extensionality_tarski
      hPR hAB hAon hBon
  exact hP ((hbase P).mp (col_left P R))

/-- Strengthened double-reflection construction:
    the resulting triangle is nondegenerate. -/
theorem double_reflection_triangle_tarski
    {A B P : Point}
    (hAB : A ≠ B)
    (hP : ¬ Col A B P) :
    ∃ R Q : Point,
      MulMidpoint A P R ∧
      MulMidpoint B R Q ∧
      P ≠ Q ∧
      ¬ Col P R Q := by
  obtain ⟨R, Q, hAR, hBQ, hPQ, _⟩ :=
    double_reflection_candidate_tarski hAB hP
  exact ⟨R, Q, hAR, hBQ, hPQ,
    midpoint_triangle_noncol_tarski hAB hP hAR hBQ⟩

/-- The sides of a quadrilateral with bisected diagonals are parallel
    in pairs. This is a theorem of neutral Tarski geometry. -/
theorem midpoint_diagonals_parallelogram_tarski
    {B P R Q S : Point}
    (htri : ¬ Col P R Q)
    (hRQ : MulMidpoint B R Q)
    (hPS : MulMidpoint B P S) :
    Parallel P R S Q ∧ Parallel R S Q P := by
  have hPR : P ≠ R := noncol_ne_first_second htri
  have hRQne : R ≠ Q := noncol_ne_second_third htri
  have hBR : B ≠ R :=
    mul_midpoint_center_ne_left hRQ hRQne
  have hRB : R ≠ B := hBR.symm
  have hBoffPR : ¬ Col P R B := by
    intro hBPR
    have hline : ∀ T : Point, Col P R T ↔ Col R B T :=
      col_line_extensionality_tarski
        hPR hRB (col_right P R) hBPR
    exact htri ((hline Q).mpr (Or.inl hRQ.1))
  have hBP : B ≠ P := by
    intro heq
    apply hBoffPR
    simpa [heq] using (col_left P R)
  have hPSne : P ≠ S := mul_reflection_distinct hPS hBP
  have hBS : B ≠ S :=
    mul_midpoint_center_ne_right hPS hPSne
  have hRS : R ≠ S := by
    intro heq
    have hPBR : Bet P B R := by
      simpa [heq] using hPS.1
    exact hBoffPR (Or.inr (Or.inl (bet_symm hPBR)))
  have hBoffRS : ¬ Col R S B := by
    intro hBRS
    have hRBS : Col R B S := col_swap_last hBRS
    have hB_RQ : Col R Q B :=
      Or.inr (Or.inl (bet_symm hRQ.1))
    have hlineRQ : ∀ T : Point, Col R Q T ↔ Col R B T :=
      col_line_extensionality_tarski
        hRQne hRB (col_left R Q) hB_RQ
    have hS_RQ : Col R Q S := (hlineRQ S).mpr hRBS
    have hlineBS : ∀ T : Point, Col R Q T ↔ Col B S T :=
      col_line_extensionality_tarski hRQne hBS hB_RQ hS_RQ
    have hP_BS : Col B S P := Or.inr (Or.inr hPS.1)
    have hP_RQ : Col R Q P := (hlineBS P).mpr hP_BS
    exact htri (col_rotate (col_rotate hP_RQ))
  constructor
  · exact centered_reflection_parallel_tarski hPR hBoffPR hPS hRQ
  · exact centered_reflection_parallel_tarski hRS hBoffRS hRQ
      (mul_midpoint_reverse hPS)

/-- Construct a nondegenerate parallelogram from the two bisected diagonals. -/
theorem triangle_midpoint_parallelogram_tarski
    {A B P R Q : Point}
    (_hA : MulMidpoint A P R)
    (hB : MulMidpoint B R Q)
    (htri : ¬ Col P R Q) :
    ∃ S : Point,
      MulMidpoint B P S ∧
      Parallel P R S Q ∧
      Parallel R S Q P := by
  obtain ⟨S, hS, _⟩ := mul_reflection_exists_unique B P
  obtain ⟨h₁, h₂⟩ :=
    midpoint_diagonals_parallelogram_tarski htri hB hS
  exact ⟨S, hS, h₁, h₂⟩

/-- A central reflection takes the midpoint of a segment to the midpoint
    of its reflected segment. No coordinates or field arithmetic are used. -/
theorem mul_reflection_preserves_midpoint
    {M X Y Z X' Y' Z' : Point}
    (hX : MulMidpoint M X X')
    (hY : MulMidpoint M Y Y')
    (hZ : MulMidpoint M Z Z')
    (hMid : MulMidpoint Y X Z) :
    MulMidpoint Y' X' Z' := by
  have hXY : Cong Y X Y' X' :=
    mul_reflection_preserves_cong
      (mul_midpoint_reverse hY)
      (mul_midpoint_reverse hX)
  have hYZ : Cong Y Z Y' Z' :=
    mul_reflection_preserves_cong
      (mul_midpoint_reverse hY)
      (mul_midpoint_reverse hZ)
  refine ⟨mul_reflection_preserves_bet hX hY hZ hMid.1, ?_⟩
  exact cong_trans (cong_symm hXY) (cong_trans hMid.2 hYZ)

/-- Reflect A (the midpoint of PR) across B (the midpoint of RQ),
    obtaining T, the midpoint of SQ. This connects both midpoint premises
    to the existing synthetic parallelogram. -/
theorem triangle_midpoint_reflection_bridge_tarski
    {A B P R Q : Point}
    (hAR : MulMidpoint A P R)
    (hBQ : MulMidpoint B R Q)
    (htri : ¬ Col P R Q) :
    ∃ S T : Point,
      MulMidpoint B P S ∧
      MulMidpoint B A T ∧
      MulMidpoint T S Q ∧
      Col A B T ∧
      Col S Q T ∧
      Parallel P R S Q ∧
      Parallel R S Q P ∧
      Cong A R T Q := by
  obtain ⟨S, hBS, hPRSQ, hRSQP⟩ :=
    triangle_midpoint_parallelogram_tarski hAR hBQ htri
  obtain ⟨T, hBT, _⟩ := mul_reflection_exists_unique B A
  have hTSQ : MulMidpoint T S Q :=
    mul_reflection_preserves_midpoint hBS hBT hBQ hAR
  have hABT : Col A B T := Or.inl hBT.1
  have hSQT : Col S Q T :=
    Or.inr (Or.inl (bet_symm hTSQ.1))
  have hARTQ : Cong A R T Q :=
    mul_reflection_preserves_cong
      (mul_midpoint_reverse hBT)
      (mul_midpoint_reverse hBQ)
  exact ⟨S, T, hBS, hBT, hTSQ, hABT, hSQT,
    hPRSQ, hRSQP, hARTQ⟩

/-- The midpoint A of PR is off the line through R and B, when B
    bisects RQ and the triangle PRQ is noncollinear. -/
theorem triangle_midpoint_off_RB_tarski
    {A B P R Q : Point}
    (hA : MulMidpoint A P R)
    (hB : MulMidpoint B R Q)
    (htri : ¬ Col P R Q) :
    ¬ Col R B A := by
  have hPR : P ≠ R := noncol_ne_first_second htri
  have hRQ : R ≠ Q := noncol_ne_second_third htri
  have hRB : R ≠ B :=
    (mul_midpoint_center_ne_left hB hRQ).symm
  have hRA : R ≠ A :=
    (mul_midpoint_center_ne_right hA hPR).symm
  have hA_PR : Col P R A :=
    col_swap_last (Or.inl hA.1)
  intro hA_RB
  have hB_RQ : Col R Q B :=
    Or.inr (Or.inl (bet_symm hB.1))
  have hline_RQ_RB :
      ∀ Z : Point, Col R Q Z ↔ Col R B Z :=
    col_line_extensionality_tarski
      hRQ hRB (col_left R Q) hB_RQ
  have hA_RQ : Col R Q A :=
    (hline_RQ_RB A).mpr hA_RB
  have hline_RQ_RA :
      ∀ Z : Point, Col R Q Z ↔ Col R A Z :=
    col_line_extensionality_tarski
      hRQ hRA (col_left R Q) hA_RQ
  have hP_RA : Col R A P := col_rotate hA_PR
  have hP_RQ : Col R Q P :=
    (hline_RQ_RA P).mpr hP_RA
  exact htri (col_rotate (col_rotate hP_RQ))

/-- Two midpoints of a nondegenerate triangle construct a pair of
    parallel congruent segments via reflection of B about A. -/
theorem triangle_midpoint_reflected_pair_tarski
    {A B P R Q : Point}
    (hA : MulMidpoint A P R)
    (hB : MulMidpoint B R Q)
    (htri : ¬ Col P R Q) :
    ∃ X : Point,
      MulMidpoint A B X ∧
      A ≠ B ∧
      B ≠ X ∧
      Col A B X ∧
      Parallel P X B Q ∧
      Cong P X B Q := by
  have hRQ : R ≠ Q := noncol_ne_second_third htri
  have hRB : R ≠ B :=
    (mul_midpoint_center_ne_left hB hRQ).symm
  have hBQ : B ≠ Q :=
    mul_midpoint_center_ne_right hB hRQ
  have hAoff : ¬ Col R B A :=
    triangle_midpoint_off_RB_tarski hA hB htri
  have hAB : A ≠ B := by
    intro heq
    apply hAoff
    simpa [heq] using (col_right R B)
  obtain ⟨X, hAX, _⟩ := mul_reflection_exists_unique A B
  have hBX : B ≠ X := mul_reflection_distinct hAX hAB
  have hABX : Col A B X :=
    Or.inr (Or.inr (bet_symm hAX.1))
  have hPar_RB_PX : Parallel R B P X :=
    centered_reflection_parallel_tarski
      hRB hAoff (mul_midpoint_reverse hA) hAX
  have hCong_PX_RB : Cong P X R B :=
    mul_reflection_preserves_cong
      (mul_midpoint_reverse hA) hAX
  have hCong_RB_BQ : Cong R B B Q :=
    cong_reverse_left hB.2
  have hCong_PX_BQ : Cong P X B Q :=
    cong_trans hCong_PX_RB hCong_RB_BQ
  have hline_RB_BQ :
      ∀ Z : Point, Col R B Z ↔ Col B Q Z :=
    col_line_extensionality_tarski
      hRB hBQ (col_right R B) (Or.inl hB.1)
  have hPar_BQ_PX : Parallel B Q P X := by
    rcases hPar_RB_PX with ⟨_, hPX, hsame | hdisjoint⟩
    · refine ⟨hBQ, hPX, Or.inl ?_⟩
      intro Z
      exact (hline_RB_BQ Z).symm.trans (hsame Z)
    · refine ⟨hBQ, hPX, Or.inr ?_⟩
      intro Z hZ
      exact hdisjoint Z
        ⟨(hline_RB_BQ Z).mpr hZ.1, hZ.2⟩
  exact ⟨X, hAX, hAB, hBX, hABX,
    parallel_symm hPar_BQ_PX, hCong_PX_BQ⟩

/-- The original triangle vertex P is outside the line through the reflection
of B across A and B.  Only midpoint and incidence facts are used. -/
theorem triangle_reflected_P_off_XB_tarski
    {A B P R Q X : Point}
    (hA : MulMidpoint A P R)
    (hB : MulMidpoint B R Q)
    (htri : ¬ Col P R Q)
    (hAX : MulMidpoint A B X) :
    ¬ Col X B P := by
  have hPR : P ≠ R := noncol_ne_first_second htri
  have hRQ : R ≠ Q := noncol_ne_second_third htri
  have hAoffRB : ¬ Col R B A :=
    triangle_midpoint_off_RB_tarski hA hB htri
  have hAneP : A ≠ P :=
    mul_midpoint_center_ne_left hA hPR
  have hAneB : A ≠ B := by
    intro heq
    apply hAoffRB
    simpa [heq] using (col_right R B)
  have hXneB : X ≠ B :=
    (mul_reflection_distinct hAX hAneB).symm
  have hRneB : R ≠ B :=
    (mul_midpoint_center_ne_left hB hRQ).symm
  have hAonXB : Col X B A :=
    Or.inr (Or.inl hAX.1)
  intro hP
  have hlineXB_PA :
      ∀ Z : Point, Col X B Z ↔ Col P A Z :=
    col_line_extensionality_tarski
      hXneB hAneP.symm hP hAonXB
  have hAonPR : Col P R A :=
    Or.inr (Or.inl (bet_symm hA.1))
  have hRonPA : Col P A R :=
    col_swap_last hAonPR
  have hRonXB : Col X B R :=
    (hlineXB_PA R).mpr hRonPA
  have hlineXB_RB :
      ∀ Z : Point, Col X B Z ↔ Col R B Z :=
    col_line_extensionality_tarski
      hXneB hRneB hRonXB (col_right X B)
  exact hAoffRB ((hlineXB_RB A).mp hAonXB)

/-- A common midpoint of PB and XQ supplies central reflection taking XB to
QP, hence parallelism of these two lines. -/
theorem diagonal_common_midpoint_parallel_tarski
    {B P X Q M : Point}
    (hXB : X ≠ B)
    (hPoff : ¬ Col X B P)
    (hMPB : MulMidpoint M P B)
    (hMXQ : MulMidpoint M X Q) :
    Parallel X B Q P := by
  have hPB : P ≠ B := by
    intro heq
    apply hPoff
    simpa [heq] using (col_right X B)
  have hBM : B ≠ M :=
    (mul_midpoint_center_ne_right hMPB hPB).symm
  have hMoff : ¬ Col X B M := by
    intro hM
    have hline :
        ∀ Z : Point, Col X B Z ↔ Col B M Z :=
      col_line_extensionality_tarski
        hXB hBM (col_right X B) hM
    have hPonBM : Col B M P :=
      Or.inl (bet_symm hMPB.1)
    exact hPoff ((hline P).mpr hPonBM)
  exact centered_reflection_parallel_tarski
    hXB hMoff hMXQ
    (mul_midpoint_reverse hMPB)

/-- The triangle midpoint theorem, under a geometrically explicit common
midpoint of the diagonals. No coordinate assumptions are made. -/
theorem triangle_mid_par_of_common_midpoint_tarski
    {A B P R Q X M : Point}
    (hA : MulMidpoint A P R)
    (hB : MulMidpoint B R Q)
    (htri : ¬ Col P R Q)
    (hAX : MulMidpoint A B X)
    (hMPB : MulMidpoint M P B)
    (hMXQ : MulMidpoint M X Q) :
    Parallel A B P Q := by
  have hAoffRB : ¬ Col R B A :=
    triangle_midpoint_off_RB_tarski hA hB htri
  have hAB : A ≠ B := by
    intro heq
    apply hAoffRB
    simpa [heq] using (col_right R B)
  have hXB : X ≠ B :=
    (mul_reflection_distinct hAX hAB).symm
  have hPoffXB : ¬ Col X B P :=
    triangle_reflected_P_off_XB_tarski hA hB htri hAX
  have hparXB_QP : Parallel X B Q P :=
    diagonal_common_midpoint_parallel_tarski
      hXB hPoffXB hMPB hMXQ
  have hparXB_PQ : Parallel X B P Q :=
    parallel_reverse_right hparXB_QP
  have hAonXB : Col X B A :=
    Or.inr (Or.inl hAX.1)
  have hline :
      ∀ Z : Point, Col X B Z ↔ Col A B Z :=
    col_line_extensionality_tarski
      hXB hAB hAonXB (col_right X B)
  rcases hparXB_PQ with ⟨_, hPQ, hsame | hdisjoint⟩
  · refine ⟨hAB, hPQ, Or.inl ?_⟩
    intro Z
    exact (hline Z).symm.trans (hsame Z)
  · refine ⟨hAB, hPQ, Or.inr ?_⟩
    intro Z hZ
    exact hdisjoint Z ⟨(hline Z).mpr hZ.1, hZ.2⟩

/-- Two midpoints of the same segment agree. The proof reflects the second
candidate around the first, then applies uniqueness of an interior point at
a prescribed distance from an endpoint. This is synthetic Tarski geometry. -/
theorem mul_midpoint_center_unique_tarski
    {C D M N : Point}
    (hM : MulMidpoint M C D)
    (hN : MulMidpoint N C D) :
    M = N := by
  by_cases hCD : C = D
  · subst D
    have hCM : C = M := between_identity C M hM.1
    have hCN : C = N := between_identity C N hN.1
    exact hCM.symm.trans hCN
  · obtain ⟨N', hMN', _⟩ :=
      mul_reflection_exists_unique M N
    have hCN_DN : Cong C N D N :=
      cong_reverse_both hN.2
    have hCN_DN' : Cong C N D N' :=
      cong_symm (mul_reflection_preserves_cong hM hMN')
    have hDN_CN' : Cong D N C N' :=
      cong_symm (mul_reflection_preserves_cong
        (mul_midpoint_reverse hM) hMN')
    have hDN_DN' : Cong D N D N' :=
      cong_trans (cong_symm hCN_DN) hCN_DN'
    have hCN_CN' : Cong C N C N' :=
      cong_trans hCN_DN hDN_CN'
    have hCN'D : Bet C N' D :=
      bet_of_three_segment_congruences hN.1
        hCN_CN' (cong_reverse_both hDN_DN') (congr_refl C D)
    have hN_eq_N' : N = N' :=
      segment_inner_unique hCD hN.1 hCN'D hDN_DN'
    have hNMN : Bet N M N := by
      simpa only [← hN_eq_N'] using hMN'.1
    exact (between_identity N M hNMN).symm

/-- The metric core of GeoCoq Ch07 `l7_22_aux` (Krippen's lemma).
The two nested congruent segments force W to be equidistant from A1,B1;
two-station propagation then makes the Pasch intersection Q their midpoint.
No linear order on an interpreted field or Euclid/continuity axiom is used. -/
theorem krippen_crossing_is_midpoint_tarski
    {A1 B1 C U V W Q M1 : Point}
    (hUA1C : Bet U A1 C) (hVB1C : Bet V B1 C)
    (hUCVC : Cong U C V C) (hA1C_B1C : Cong A1 C B1 C)
    (hUWVW : Cong U W V W)
    (hWQC : Bet W Q C) (hA1QB1 : Bet A1 Q B1)
    (hM1 : MulMidpoint M1 A1 B1) :
    Q = M1 := by
  have hWA1_WB1 : Cong W A1 W B1 :=
    cong_reverse_both
      (inner_five_segment hUA1C hVB1C hUCVC hA1C_B1C
        hUWVW (congr_refl C W))
  have hCA1_CB1 : Cong C A1 C B1 :=
    cong_reverse_both hA1C_B1C
  have hQA1_QB1 : Cong Q A1 Q B1 := by
    by_cases hWC : W = C
    · subst W
      have hCQ : C = Q := between_identity C Q hWQC
      subst Q
      exact hCA1_CB1
    · have hCW : C ≠ W := by
        intro h
        exact hWC h.symm
      have hCWQ : Col C W Q :=
        col_rotate (col_rotate (Or.inl hWQC))
      exact col_equidistant_of_two_stations hCW hCWQ
        hCA1_CB1 hWA1_WB1
  have hMidQ : MulMidpoint Q A1 B1 :=
    ⟨hA1QB1, hQA1_QB1⟩
  exact mul_midpoint_center_unique_tarski hMidQ hM1

/-- The synthetic Krippen conclusion once the larger comparison triangle
has been reflected through C. The intersection Q is constructed here by
the two-Pasch theorem rather than supplied as an existence hypothesis.
This is the complete incidence-and-congruence core of Ch07 l7_22_aux. -/
theorem krippen_of_reflected_configuration_tarski
    {A1 B1 C U V W M1 M2 : Point}
    (hUA1C : Bet U A1 C) (hVB1C : Bet V B1 C)
    (hUWV : Bet U W V)
    (hUCVC : Cong U C V C) (hA1C_B1C : Cong A1 C B1 C)
    (hUWVW : Cong U W V W)
    (hM1 : MulMidpoint M1 A1 B1)
    (hCM2W : MulMidpoint C M2 W) :
    Bet M1 C M2 := by
  obtain ⟨Q, hWQC, hA1QB1⟩ :=
    pasch_two_crossings_tarski hUA1C hVB1C hUWV
  have hQM1 : Q = M1 :=
    krippen_crossing_is_midpoint_tarski
      hUA1C hVB1C hUCVC hA1C_B1C hUWVW
      hWQC hA1QB1 hM1
  have hWM1C : Bet W M1 C := hQM1 ▸ hWQC
  exact bet_exchange hWM1C (bet_symm hCM2W.1)

/-- Two distinct stations equidistant from A and B force any point M on
their connecting line and inside AB to be its midpoint. This is the
characterization part of the neutral midpoint construction; construction of
the stations and their intersection remains a separate existence theorem. -/
theorem midpoint_of_equidistant_crossing_tarski
    {A B C D M : Point}
    (hCD : C ≠ D)
    (hCA : Cong C A C B)
    (hDA : Cong D A D B)
    (hM : Col C D M)
    (hBet : Bet A M B) :
    MulMidpoint M A B := by
  exact ⟨hBet,
    col_equidistant_of_two_stations hCD hM hCA hDA⟩

/-! ### The first constructive stages of GeoCoq Ch07 `l7_25`

The source theorem starts from `Cong C A C B` and constructs a midpoint of
`AB`. Its collinear case and its two successive Pasch intersections are
independent of any perpendicularity, Euclidean coordinates, or continuity.
The remaining noncollinear obligation is precisely to prove that the first
Pasch intersection `R` is equidistant from `A` and `B`. -/

/-- GeoCoq `l7_20`: a point on `AB` which is equidistant from the endpoints
is either the midpoint or the two endpoints coincide. The exterior cases
follow by subtracting two congruent nested segments. -/
theorem col_equidistant_midpoint_or_eq_tarski
    {A B C : Point} (hcol : Col A B C)
    (hCA : Cong C A C B) :
    A = B ∨ MulMidpoint C A B := by
  rcases hcol with hABC | hBCA | hCAB
  · left
    have hBA : Cong B A B B :=
      segment_cong_sub_outer (bet_symm hABC) (bet_end C B)
        (congr_refl C B) hCA
    exact (cong_identity B A B hBA).symm
  · exact Or.inr ⟨bet_symm hBCA, hCA⟩
  · left
    have hAB : Cong A B A A :=
      segment_cong_sub_outer hCAB (bet_end C A)
        (congr_refl C A) (cong_symm hCA)
    exact cong_identity A B A hAB

/-- GeoCoq `l7_25`, collinear branch: the equidistant collinear point gives
a midpoint, including the degenerate case `A = B`. -/
theorem midpoint_exists_of_col_equidistant_tarski
    {A B C : Point} (hcol : Col A B C)
    (hCA : Cong C A C B) :
    ∃ M : Point, MulMidpoint M A B := by
  rcases col_equidistant_midpoint_or_eq_tarski hcol hCA with heq | hmid
  · subst B
    exact ⟨A, bet_end A A, congr_refl A A⟩
  · exact ⟨C, hmid⟩

/-- Two applications of inner Pasch construct the two intersections in
the noncollinear branch of GeoCoq `l7_25`. All existential witnesses are
obtained from Tarski's segment construction and inner Pasch axioms. -/
theorem midpoint_pasch_candidate_tarski (A B C : Point) :
    ∃ P Q R X : Point,
      Bet C A P ∧ A ≠ P ∧
      Bet C B Q ∧ Cong B Q A P ∧
      Bet A R Q ∧ Bet B R P ∧
      Bet A X B ∧ Bet R X C := by
  obtain ⟨P, hCAP, hAP⟩ := segment_extension_nontrivial C A
  obtain ⟨Q, hCBQ, hBQAP⟩ := segment_construction C B A P
  obtain ⟨R, hARQ, hBRP⟩ :=
    inner_pasch P Q C A B (bet_symm hCAP) (bet_symm hCBQ)
  obtain ⟨X, hAXB, hRXC⟩ :=
    inner_pasch C B P A R hCAP hBRP
  exact ⟨P, Q, R, X, hCAP, hAP, hCBQ, hBQAP,
    hARQ, hBRP, hAXB, hRXC⟩

/-- Metric part of GeoCoq `l7_25` before the difficult crossing argument.
The equal extensions of `CA` and `CB` have equal total lengths; the
five-segment axiom also makes the two crossing sides `PB` and `QA`
congruent. Both are genuine synthetic deductions. -/
theorem isosceles_extensions_cross_cong_tarski
    {A B C P Q : Point}
    (hCAne : C ≠ A) (hCA : Cong C A C B)
    (hCAP : Bet C A P) (hCBQ : Bet C B Q)
    (hBQAP : Cong B Q A P) :
    Cong C P C Q ∧ Cong P B Q A := by
  have hAPBQ : Cong A P B Q := cong_symm hBQAP
  have hCP_CQ : Cong C P C Q :=
    segment_cong_add hCAP hCBQ hCA hAPBQ
  have hPB_QA : Cong P B Q A :=
    five_segment C C A B P Q B A
      hCA hAPBQ (cong_symm hCA)
      (cong_pseudo_reflexivity A B)
      hCAP hCBQ hCAne
  exact ⟨hCP_CQ, hPB_QA⟩

/-- If the first Pasch intersection is also equidistant from the endpoints,
the second intersection is the desired midpoint. This isolates the exact
metric obligation remaining in the noncollinear branch of `l7_25`. -/
theorem midpoint_of_pasch_candidate_equidistant_tarski
    {A B C R X : Point}
    (hCA : Cong C A C B) (hRA : Cong R A R B)
    (hAXB : Bet A X B) (hRXC : Bet R X C) :
    MulMidpoint X A B := by
  refine ⟨hAXB, ?_⟩
  by_cases hCR : C = R
  · subst C
    have hRX : R = X := between_identity R X hRXC
    simpa [hRX] using hRA
  · exact col_equidistant_of_two_stations hCR
      (Or.inr (Or.inl hRXC)) hCA hRA

/-- GeoCoq Ch07 `l7_25`: the first Pasch intersection of the crossed
segments in the isosceles construction is equidistant from A and B.
The proof uses only derived Tarski congruence propagation, segment copying,
and the uniqueness of an intersection of two distinct lines. -/
theorem pasch_crossing_equidistant_tarski
    {A B C P Q R : Point}
    (hNoncol : ¬ Col A B C)
    (hCA : Cong C A C B)
    (hCAP : Bet C A P)
    (hAP : A ≠ P)
    (hCBQ : Bet C B Q)
    (hBQAP : Cong B Q A P)
    (hARQ : Bet A R Q)
    (hBRP : Bet B R P) :
    Cong R A R B := by
  have hCAne : C ≠ A :=
    (noncol_ne_first_third hNoncol).symm
  have hBCne : B ≠ C :=
    noncol_ne_second_third hNoncol
  have hPB_QA : Cong P B Q A :=
    (isosceles_extensions_cross_cong_tarski
      hCAne hCA hCAP hCBQ hBQAP).2
  have hBP_AQ : Cong B P A Q :=
    cong_reverse_both hPB_QA
  obtain ⟨R', hAR'Q, _, hRP_R'Q⟩ :=
    copy_point_inside_congruent_segment hBRP hBP_AQ
  have hRA_R'B : Cong R A R' B :=
    inner_five_segment
      hBRP hAR'Q hBP_AQ hRP_R'Q
      (cong_pseudo_reflexivity B A)
      (cong_symm (cong_reverse_both hBQAP))
  have hRQ_R'P : Cong R Q R' P :=
    inner_five_segment
      hBRP hAR'Q hBP_AQ hRP_R'Q
      hBQAP (cong_pseudo_reflexivity P Q)
  have hBR'P : Bet B R' P :=
    bet_of_three_segment_congruences
      hARQ (cong_reverse_both hRA_R'B)
      hRQ_R'P (cong_symm hBP_AQ)
  have hBQne : B ≠ Q := by
    intro hBQ
    have hz : Cong A P B B := by
      simpa only [← hBQ] using (cong_symm hBQAP)
    exact hAP (cong_identity A P B hz)
  have hBQC : Col B Q C :=
    Or.inr (Or.inr hCBQ)
  have hline : ∀ Z : Point, Col B Q Z ↔ Col B C Z :=
    col_line_extensionality_tarski
      hBQne hBCne (col_left B Q) hBQC
  have hAQB : ¬ Col A Q B := by
    intro hcol
    have hBQA : Col B Q A := col_reverse hcol
    have hBCA : Col B C A := (hline A).mp hBQA
    exact hNoncol (col_rotate (col_rotate hBCA))
  have hBPne : B ≠ P := by
    intro hBP
    have hz : Cong A Q B B := by
      simpa only [← hBP] using (cong_symm hBP_AQ)
    exact (noncol_ne_first_second hAQB) (cong_identity A Q B hz)
  have hRAQ : Col A Q R :=
    Or.inr (Or.inl (bet_symm hARQ))
  have hR'AQ : Col A Q R' :=
    Or.inr (Or.inl (bet_symm hAR'Q))
  have hRBP : Col B P R :=
    Or.inr (Or.inl (bet_symm hBRP))
  have hR'BP : Col B P R' :=
    Or.inr (Or.inl (bet_symm hBR'P))
  have hRR' : R = R' :=
    line_intersection_unique_tarski
      hAQB hBPne hRAQ hR'AQ hRBP hR'BP
  simpa only [← hRR'] using hRA_R'B

/-- GeoCoq Ch07 `l7_25`: any two endpoints equidistant from a given
station have a midpoint. The station is part of the hypothesis; existence
of such a station for arbitrary endpoints is a later geometric theorem. -/
theorem midpoint_exists_of_equidistant_station_tarski
    {A B C : Point} (hCA : Cong C A C B) :
    ∃ M : Point, MulMidpoint M A B := by
  classical
  by_cases hcol : Col A B C
  · exact midpoint_exists_of_col_equidistant_tarski hcol hCA
  · obtain ⟨P, Q, R, X, hCAP, hAP, hCBQ, hBQAP,
        hARQ, hBRP, hAXB, hRXC⟩ :=
      midpoint_pasch_candidate_tarski A B C
    have hRA : Cong R A R B :=
      pasch_crossing_equidistant_tarski
        hcol hCA hCAP hAP hCBQ hBQAP hARQ hBRP
    exact ⟨X,
      midpoint_of_pasch_candidate_equidistant_tarski
        hCA hRA hAXB hRXC⟩

/-- The existence of an equidistant station and general midpoint existence
are equivalent; the reverse implication uses the midpoint itself. -/
theorem equidistant_station_iff_midpoint_tarski (A B : Point) :
    (∃ C : Point, Cong C A C B) ↔
      (∃ M : Point, MulMidpoint M A B) := by
  constructor
  · rintro ⟨C, hC⟩
    exact midpoint_exists_of_equidistant_station_tarski hC
  · rintro ⟨M, hM⟩
    exact ⟨M, hM.2⟩

/-! ### Ch08 right-angle infrastructure, interpreted in neutral Tarski geometry

The GeoCoq predicate `Per A B C` is defined by reflecting `C` across `B`
and requiring the two reflected endpoints to be equidistant from `A`.
It introduces no perpendicularity axiom or numerical coordinates. These
first right-angle lemmas support the later construction of an equidistant
station for arbitrary `A,B` (and hence general midpoint existence). -/

/-- The Tarski-only definition of a right angle with vertex B. -/
def TarskiPer (A B C : Point) : Prop :=
  ∃ C' : Point, MulMidpoint B C C' ∧ Cong A C A C'

/-- GeoCoq Ch08 `l8_2`: the legs of a right angle may be exchanged.
This follows by reflecting both legs across the vertex B. -/
theorem tarski_per_swap_legs_tarski
    {A B C : Point} (h : TarskiPer A B C) :
    TarskiPer C B A := by
  obtain ⟨C', hMidC, hAC⟩ := h
  obtain ⟨A', hMidA, _⟩ := mul_reflection_exists_unique B A
  refine ⟨A', hMidA, ?_⟩
  have hReflection : Cong A' C A C' :=
    mul_reflection_preserves_cong
      hMidA (mul_midpoint_reverse hMidC)
  have hAC_A'C : Cong A C A' C :=
    cong_trans hAC (cong_symm hReflection)
  exact cong_reverse_both hAC_A'C

/-- GeoCoq Ch08 `l8_3`: a right-angle leg can be prolonged or shortened
along its supporting line. The congruence follows by two-station propagation
on that line, rather than from coordinate orthogonality. -/
theorem tarski_per_change_first_collinear_tarski
    {A B C A' : Point}
    (h : TarskiPer A B C)
    (hAB : A ≠ B) (hCol : Col B A A') :
    TarskiPer A' B C := by
  obtain ⟨C', hMidC, hAC⟩ := h
  refine ⟨C', hMidC, ?_⟩
  exact col_equidistant_of_two_stations
    hAB (col_swap hCol) hAC hMidC.2

/-- GeoCoq Ch08 `l8_4`: reflecting the other leg through its vertex
preserves the right-angle predicate. -/
theorem tarski_per_reflect_third_tarski
    {A B C C' : Point}
    (h : TarskiPer A B C)
    (hMid : MulMidpoint B C C') :
    TarskiPer A B C' := by
  obtain ⟨D, hMidD, hAC⟩ := h
  obtain ⟨E, _, huniq⟩ := mul_reflection_exists_unique B C
  have hDC' : D = C' :=
    (huniq D hMidD).trans (huniq C' hMid).symm
  refine ⟨C, mul_midpoint_reverse hMid, ?_⟩
  simpa [hDC'] using (cong_symm hAC)

/-- GeoCoq Ch08 `l8_5`: the degenerate leg forms a formal right angle. -/
theorem tarski_per_degenerate_tarski (A B : Point) :
    TarskiPer A B B := by
  exact ⟨B, ⟨bet_end B B, congr_refl B B⟩, congr_refl A B⟩

/-- GeoCoq Ch08 `l8_9`: a right angle whose two legs lie on the same line
must be degenerate. The central step is uniqueness of the midpoint of CC'. -/
theorem tarski_per_collinear_legs_degenerate_tarski
    {A B C : Point}
    (h : TarskiPer A B C) (hCol : Col A B C) :
    A = B ∨ C = B := by
  by_cases hAB : A = B
  · exact Or.inl hAB
  · right
    obtain ⟨C', hMid, hAC⟩ := h
    by_cases hCB : C = B
    · exact hCB
    have hCC' : C ≠ C' :=
      mul_reflection_distinct hMid (by
        intro h
        exact hCB h.symm)
    have hline1 : ∀ S : Point, Col A B S ↔ Col C B S :=
      col_line_extensionality_tarski
        hAB hCB hCol (col_right A B)
    have hC'_CB : Col C B C' := Or.inl hMid.1
    have hC'_AB : Col A B C' := (hline1 C').mpr hC'_CB
    have hline2 : ∀ S : Point, Col A B S ↔ Col C C' S :=
      col_line_extensionality_tarski
        hAB hCC' hCol hC'_AB
    have hA_CC' : Col C C' A :=
      (hline2 A).mp (col_left A B)
    rcases col_equidistant_midpoint_or_eq_tarski
        hA_CC' hAC with hEq | hMidA
    · exact False.elim (hCC' hEq)
    · have hBA : B = A :=
        mul_midpoint_center_unique_tarski hMid hMidA
      exact False.elim (hAB hBA.symm)

/-- GeoCoq Ch08 `l8_10`: SSS congruence transfers a Tarski right angle.
The nondegenerate case is one application of the primitive five-segment
axiom, after reflecting the right-angle leg across the target vertex. -/
theorem tarski_per_of_three_segment_congruences_tarski
    {A B C A' B' C' : Point}
    (hPer : TarskiPer A B C)
    (hAB : Cong A B A' B')
    (hBC : Cong B C B' C')
    (hAC : Cong A C A' C') :
    TarskiPer A' B' C' := by
  obtain ⟨D, hMid, hAD⟩ := hPer
  by_cases hCB : C = B
  · have hB'C' : B' = C' :=
      cong_identity B' C' B (by
        simpa [hCB] using (cong_symm hBC))
    subst C'
    exact tarski_per_degenerate_tarski A' B'
  · obtain ⟨D', hMid', _⟩ :=
      mul_reflection_exists_unique B' C'
    have hBD : Cong B D B' D' :=
      cong_trans (cong_symm hMid.2)
        (cong_trans hBC hMid'.2)
    have hDA : Cong D A D' A' :=
      five_segment C C' B B' D D' A A'
        (cong_reverse_both hBC) hBD
        (cong_reverse_both hAC)
        (cong_reverse_both hAB)
        hMid.1 hMid'.1 hCB
    refine ⟨D', hMid', ?_⟩
    exact cong_trans (cong_symm hAC)
      (cong_trans hAD (cong_reverse_both hDA))

/-- GeoCoq Definition 8.11: perpendicularity at the point X, expressed
by the Tarski right-angle predicate for arbitrary points on both lines. -/
def TarskiPerpAt (X A B C D : Point) : Prop :=
  A ≠ B ∧ C ≠ D ∧ Col X A B ∧ Col X C D ∧
    ∀ U V : Point, Col U A B → Col V C D → TarskiPer U X V

/-- GeoCoq Definition 8.11: the intersection point of perpendicular
lines is existentially quantified, not supplied by an additional axiom. -/
def TarskiPerp (A B C D : Point) : Prop :=
  ∃ X : Point, TarskiPerpAt X A B C D

/-- GeoCoq Ch08 `l8_13_2`: a single nondegenerate right angle at the
intersection of two lines determines perpendicularity of the entire lines.
The proof transports the right angle first along one line and then along the
other, using only Tarski's collinearity and congruence lemmas. -/
theorem tarski_perp_at_of_one_right_angle_tarski
    {X A B C D U V : Point}
    (hAB : A ≠ B) (hCD : C ≠ D)
    (hXAB : Col X A B) (hXCD : Col X C D)
    (hUAB : Col U A B) (hVCD : Col V C D)
    (hUX : U ≠ X) (hVX : V ≠ X)
    (hPer : TarskiPer U X V) :
    TarskiPerpAt X A B C D := by
  have hXU : X ≠ U := hUX.symm
  have hXV : X ≠ V := hVX.symm
  have hAB_XU : ∀ S : Point, Col A B S ↔ Col X U S :=
    col_line_extensionality_tarski hAB hXU
      (col_rotate hXAB) (col_rotate hUAB)
  have hCD_XV : ∀ S : Point, Col C D S ↔ Col X V S :=
    col_line_extensionality_tarski hCD hXV
      (col_rotate hXCD) (col_rotate hVCD)
  refine ⟨hAB, hCD, hXAB, hXCD, ?_⟩
  intro U' V' hU' hV'
  have hXUU' : Col X U U' :=
    (hAB_XU U').mp (col_rotate hU')
  have hXVV' : Col X V V' :=
    (hCD_XV V').mp (col_rotate hV')
  have hPerU' : TarskiPer U' X V :=
    tarski_per_change_first_collinear_tarski hPer hUX hXUU'
  have hPerV' : TarskiPer V' X U' :=
    tarski_per_change_first_collinear_tarski
      (tarski_per_swap_legs_tarski hPerU') hVX hXVV'
  exact tarski_per_swap_legs_tarski hPerV'

/-- GeoCoq Ch08 `l8_12`: perpendicularity at a point is symmetric. -/
theorem tarski_perp_at_swap_lines_tarski
    {X A B C D : Point}
    (h : TarskiPerpAt X A B C D) :
    TarskiPerpAt X C D A B := by
  rcases h with ⟨hAB, hCD, hXAB, hXCD, hPer⟩
  refine ⟨hCD, hAB, hXCD, hXAB, ?_⟩
  intro U V hU hV
  exact tarski_per_swap_legs_tarski (hPer V U hV hU)

/-- Symmetry of synthetic line perpendicularity. -/
theorem tarski_perp_swap_lines_tarski
    {A B C D : Point} (h : TarskiPerp A B C D) :
    TarskiPerp C D A B := by
  obtain ⟨X, hX⟩ := h
  exact ⟨X, tarski_perp_at_swap_lines_tarski hX⟩

/-- The diagonal pairing incompatible with the original midpoint A of PR is
excluded by noncollinearity of the triangle PRQ. Notice that the fact that B
bisects RQ is not needed for this exclusion. -/
theorem triangle_reflected_wrong_pair_impossible_tarski
    {A B P R Q X M : Point}
    (hA : MulMidpoint A P R)
    (htri : ¬ Col P R Q)
    (hAX : MulMidpoint A B X)
    (hWrongPQ : MulMidpoint M P Q)
    (hWrongXB : MulMidpoint M X B) :
    False := by
  have hAM : A = M :=
    mul_midpoint_center_unique_tarski
      (mul_midpoint_reverse hAX) hWrongXB
  subst M
  have hPR : P ≠ R := noncol_ne_first_second htri
  have hAP : A ≠ P := mul_midpoint_center_ne_left hA hPR
  have hPA : P ≠ A := hAP.symm
  have hAonPR : Col P R A :=
    Or.inr (Or.inl (bet_symm hA.1))
  have hline : ∀ Z : Point, Col P R Z ↔ Col P A Z :=
    col_line_extensionality_tarski
      hPR hPA (col_left P R) hAonPR
  have hQonPA : Col P A Q := Or.inl hWrongPQ.1
  exact htri ((hline Q).mpr hQonPA)

/-- The exact geometric dependence of the reflected common-midpoint
construction: only the two-alternative midpoint theorem for parallel congruent
segments remains. Both orientation alternatives are discharged here. The
geometric premise must ultimately be derived from Plane, not added as an axiom. -/
theorem triangle_reflected_common_midpoint_of_par_cong_mid_tarski
    (hParCongMid : ∀ U V W Z : Point,
      Parallel U V W Z → Cong U V W Z →
      ∃ M : Point,
        (MulMidpoint M U W ∧ MulMidpoint M V Z) ∨
        (MulMidpoint M U Z ∧ MulMidpoint M V W))
    {A B P R Q : Point}
    (hA : MulMidpoint A P R)
    (hB : MulMidpoint B R Q)
    (htri : ¬ Col P R Q) :
    ∃ X M : Point,
      MulMidpoint A B X ∧
      MulMidpoint M P B ∧
      MulMidpoint M X Q := by
  obtain ⟨X, hAX, _, _, _, hPar, hCong⟩ :=
    triangle_midpoint_reflected_pair_tarski hA hB htri
  obtain ⟨M, hgood | hbad⟩ :=
    hParCongMid P X B Q hPar hCong
  · exact ⟨X, M, hAX, hgood.1, hgood.2⟩
  · exact False.elim
      (triangle_reflected_wrong_pair_impossible_tarski
        hA htri hAX hbad.1 hbad.2)

/-- The candidate additive inverse of the scalar unit is exactly the
central reflection of I across the frame origin O. Existence and
uniqueness follow from the earlier synthetic opposite-point construction. -/
theorem mul_negative_one_midpoint_exists_unique (f : Frame Point) :
    ∃! z : AxisPoint f, MulMidpoint f.O f.I z.1 := by
  obtain ⟨z, hz, huniq⟩ := axis_opposite_one_exists_unique f
  refine ⟨z, ⟨hz.1, cong_symm hz.2⟩, ?_⟩
  intro w hw
  exact huniq w ⟨hw.1, cong_symm hw.2⟩

/-- Once the second operand is nonzero, the multiplication graph is
precisely its two parallel projections. -/
theorem mulGraph_nonzero_second_iff (f : Frame Point)
    (x y z : AxisPoint f) (hy : y ≠ axisZero f) :
    MulGraph f x y z ↔
      ∃ W : Point,
        Col f.O f.J W ∧
        Parallel f.I f.J y.1 W ∧
        Parallel f.J x.1 W z.1 := by
  constructor
  · rintro (⟨hy0, _⟩ | ⟨_, W, hW⟩)
    · exact False.elim (hy (Subtype.ext hy0))
    · exact ⟨W, hW⟩
  · intro hW
    refine Or.inr ⟨?_, hW⟩
    intro hy0
    exact hy (Subtype.ext hy0)

/-- The nonzero-second-operand case is exactly the unproved part of
multiplication functionality; the zero case is already automatic. -/
theorem mulFunctional_iff_nonzero_second (f : Frame Point) :
    MulFunctional f ↔
      ∀ x y z w : AxisPoint f, y ≠ axisZero f →
        MulGraph f x y z → MulGraph f x y w → z = w := by
  constructor
  · intro hfunc x y z w _ hz hw
    exact hfunc x y z w hz hw
  · intro hnonzero x y z w hz hw
    by_cases hy : y = axisZero f
    · subst y
      have hz' : z = axisZero f := mul_zero_right_unique f x z hz
      have hw' : w = axisZero f := mul_zero_right_unique f x w hw
      exact hz'.trans hw'.symm
    · exact hnonzero x y z w hy hz hw

/-!
### The two neutral projection constructions, with auxiliary endpoints

These are proofs of *point existence* from the general through-point
parallel theorem and the transitivity of parallelism.  Those general
theorems remain geometric obligations to be established from Plane;
they are explicit theorem hypotheses here, not additional axioms.
The auxiliary endpoint U is needed until neutral incidence proves that
replacing it with the actual intersection point preserves the line.
-/

/-- Draw through y a line parallel to IJ and intersect it with OJ.
The required intersection exists because IJ and OJ are not parallel.
This is the first geometric step in multiplication. -/
theorem mul_first_weak_projection_exists
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ U : Point, Parallel A B P U)
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (f : Frame Point) (y : AxisPoint f) :
    ∃ W U : Point,
      Col f.O f.J W ∧
      Parallel f.I f.J y.1 U ∧
      Col y.1 U W := by
  obtain ⟨U, hpar⟩ :=
    hparallel_through f.I f.J y.1 f.I_ne_J
  have hnparallel : ¬ Parallel y.1 U f.O f.J := by
    intro hbad
    exact frame_IJ_not_parallel_OJ f
      (hparallel_trans hpar hbad)
  obtain ⟨W, hUW, hOJ⟩ :=
    not_parallel_lines_intersect y.1 U f.O f.J
      hpar.2.1 f.O_ne_J hnparallel
  exact ⟨W, U, hOJ, hpar, hUW⟩

/-- Draw through W a line parallel to Jx and intersect it with OI.
The constructed intersection has the right scalar-axis subtype; only
normalization of the auxiliary endpoint remains for MulGraph. -/
theorem mul_second_weak_projection_exists
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ U : Point, Parallel A B P U)
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (f : Frame Point) (x : AxisPoint f) (W : Point) :
    ∃ z : AxisPoint f, ∃ U : Point,
      Parallel f.J x.1 W U ∧
      Col W U z.1 := by
  obtain ⟨U, hpar⟩ :=
    hparallel_through f.J x.1 W
      (f.J_ne_axis_point x.1 x.2)
  have hnparallel : ¬ Parallel W U f.O f.I := by
    intro hbad
    exact frame_JX_not_parallel_OI f x
      (hparallel_trans hpar hbad)
  obtain ⟨Z, hUZ, hOI⟩ :=
    not_parallel_lines_intersect W U f.O f.I
      hpar.2.1 f.O_ne_I hnparallel
  exact ⟨⟨Z, hOI⟩, U, hpar, hUZ⟩

/-- The first projection of the scalar unit is constructed explicitly:
I projects to J along IJ. This unconditional instance uses only the
frame's noncollinearity. -/
theorem mul_first_projection_of_one_exists (f : Frame Point) :
    ∃ W : Point,
      Col f.O f.J W ∧
      Parallel f.I f.J (axisOne f).1 W :=
  ⟨f.J, col_right f.O f.J, parallel_refl f.I_ne_J⟩

/-- The second projection of J in direction Jx returns x. -/
theorem mul_second_projection_of_J_exists
    (f : Frame Point) (x : AxisPoint f) :
    ∃ z : AxisPoint f, Parallel f.J x.1 f.J z.1 :=
  ⟨x, parallel_refl (f.J_ne_axis_point x.1 x.2)⟩

/-- The frame axes meet only at O, derived from the ordinary
nondegenerate-line extensionality theorem and the noncollinear frame.
This removes a separate intersection-uniqueness assumption from both
multiplication projection constructions. -/
theorem mul_frame_axes_intersection_unique_of_col_line_eq
    (hcol_line_eq : ∀ {A B C : Point},
      A ≠ B → Col A B C → C ≠ A →
      ∀ T : Point, Col A B T ↔ Col A C T)
    (f : Frame Point) (T : Point)
    (hOI : Col f.O f.I T)
    (hOJ : Col f.O f.J T) : T = f.O := by
  by_contra hTO
  have hOI_eq : ∀ X : Point,
      Col f.O f.I X ↔ Col f.O T X :=
    hcol_line_eq f.O_ne_I hOI hTO
  have hOJ_eq : ∀ X : Point,
      Col f.O f.J X ↔ Col f.O T X :=
    hcol_line_eq f.O_ne_J hOJ hTO
  have hJ : Col f.O f.I f.J :=
    (hOI_eq f.J).mpr ((hOJ_eq f.J).mp (col_right f.O f.J))
  exact f.noncol hJ

/-- A geometric line can be described by *any* two distinct points on it.
This standard incidence consequence is proved from the more primitive
one-endpoint replacement property, including the degenerate C=A case. -/
theorem mul_line_eq_of_two_points
    (hcol_line_eq : ∀ {A B C : Point},
      A ≠ B → Col A B C → C ≠ A →
      ∀ T : Point, Col A B T ↔ Col A C T)
    {A B C D : Point}
    (hAB : A ≠ B) (hCD : C ≠ D)
    (hABC : Col A B C) (hABD : Col A B D) :
    ∀ T : Point, Col A B T ↔ Col C D T := by
  by_cases hAC : A = C
  · subst C
    exact hcol_line_eq hAB hABD (Ne.symm hCD)
  · have hAB_AC : ∀ T : Point, Col A B T ↔ Col A C T :=
      hcol_line_eq hAB hABC (Ne.symm hAC)
    have hCAD : Col C A D :=
      col_swap ((hAB_AC D).mp hABD)
    have hCA_CD : ∀ T : Point, Col C A T ↔ Col C D T :=
      hcol_line_eq (Ne.symm hAC) hCAD (Ne.symm hCD)
    intro T
    constructor
    · intro hT
      exact (hCA_CD T).mp (col_swap ((hAB_AC T).mp hT))
    · intro hT
      exact (hAB_AC T).mpr (col_swap ((hCA_CD T).mpr hT))

/-- Distinct nonparallel lines have at most one common point. The proof
uses incidence extensionality and the *definition* of Parallel; no
coordinate model or additional parallel postulate is needed. -/
theorem mul_two_intersections_unique_of_col_line_eq
    (hcol_line_eq : ∀ {A B C : Point},
      A ≠ B → Col A B C → C ≠ A →
      ∀ T : Point, Col A B T ↔ Col A C T)
    {A B C D X Y : Point}
    (hAB : A ≠ B) (hCD : C ≠ D)
    (hnpar : ¬ Parallel A B C D)
    (hAX : Col A B X) (hCX : Col C D X)
    (hAY : Col A B Y) (hCY : Col C D Y) : X = Y := by
  by_contra hXY
  have hAB_XY : ∀ T : Point, Col A B T ↔ Col X Y T :=
    mul_line_eq_of_two_points hcol_line_eq hAB hXY hAX hAY
  have hCD_XY : ∀ T : Point, Col C D T ↔ Col X Y T :=
    mul_line_eq_of_two_points hcol_line_eq hCD hXY hCX hCY
  apply hnpar
  exact ⟨hAB, hCD, Or.inl (fun T =>
    (hAB_XY T).trans (hCD_XY T).symm)⟩

/-- Once neutral incidence gives uniqueness of the two axis intersection
and invariance of a nondegenerate line under changing its endpoint, the
first *weak* projection becomes the actual first multiplication projection.
The only remaining parallel hypotheses are generic geometric construction
and transitivity, not arithmetic laws. -/
theorem mul_first_projection_exists_of_incidence
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ U : Point, Parallel A B P U)
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (hcol_line_eq : ∀ {A B C : Point},
      A ≠ B → Col A B C → C ≠ A →
      ∀ T : Point, Col A B T ↔ Col A C T)
    (f : Frame Point)
    (y : AxisPoint f) (hy : y.1 ≠ f.O) :
    ∃ W : Point,
      Col f.O f.J W ∧ Parallel f.I f.J y.1 W := by
  obtain ⟨W, U, hOJ, hpar, hYU⟩ :=
    mul_first_weak_projection_exists
      hparallel_through hparallel_trans f y
  have hWy : W ≠ y.1 := by
    intro h
    have hOI : Col f.O f.I W := by
      simpa [h] using y.2
    exact hy (h.symm.trans
      (mul_frame_axes_intersection_unique_of_col_line_eq
        hcol_line_eq f W hOI hOJ))
  have hline : ∀ T : Point, Col y.1 U T ↔ Col y.1 W T :=
    hcol_line_eq hpar.2.1 hYU hWy
  rcases hpar with ⟨hIJ, _, hsame | hdisjoint⟩
  · refine ⟨W, hOJ, hIJ, hWy.symm, Or.inl ?_⟩
    intro T
    exact (hsame T).trans (hline T)
  · refine ⟨W, hOJ, hIJ, hWy.symm, Or.inr ?_⟩
    intro T hT
    exact hdisjoint T ⟨hT.1, (hline T).mpr hT.2⟩

/-- The analogous incidence normalization for the second multiplication
projection. In particular, the second line has distinct endpoints because
W is nonzero on OJ whereas its intersection is on OI. -/
theorem mul_second_projection_exists_of_incidence
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ U : Point, Parallel A B P U)
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (hcol_line_eq : ∀ {A B C : Point},
      A ≠ B → Col A B C → C ≠ A →
      ∀ T : Point, Col A B T ↔ Col A C T)
    (f : Frame Point)
    (x : AxisPoint f) (W : Point)
    (hWcol : Col f.O f.J W) (hWnonzero : W ≠ f.O) :
    ∃ z : AxisPoint f, Parallel f.J x.1 W z.1 := by
  obtain ⟨z, U, hpar, hWUz⟩ :=
    mul_second_weak_projection_exists
      hparallel_through hparallel_trans f x W
  have hWz : W ≠ z.1 := by
    intro h
    have hWO : Col f.O f.I W := by simpa [h] using z.2
    exact hWnonzero
      (mul_frame_axes_intersection_unique_of_col_line_eq
        hcol_line_eq f W hWO hWcol)
  have hline : ∀ T : Point, Col W U T ↔ Col W z.1 T :=
    hcol_line_eq hpar.2.1 hWUz hWz.symm
  rcases hpar with ⟨hJX, _, hsame | hdisjoint⟩
  · refine ⟨z, hJX, hWz, Or.inl ?_⟩
    intro T
    exact (hsame T).trans (hline T)
  · refine ⟨z, hJX, hWz, Or.inr ?_⟩
    intro T hT
    exact hdisjoint T ⟨hT.1, (hline T).mpr hT.2⟩

/-- The first multiplication projection is unique after proving
Playfair's uniqueness of a parallel through a point. Both candidate
projection lines share y; they therefore coincide, and their
intersection with OJ is unique by neutral incidence. -/
theorem mul_first_projection_unique_of_playfair
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (hplayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ Q : Point, Col C D Q ↔ Col E F Q)
    (hcol_line_eq : ∀ {A B C : Point},
      A ≠ B → Col A B C → C ≠ A →
      ∀ T : Point, Col A B T ↔ Col A C T)
    (f : Frame Point) (y : AxisPoint f)
    {W W' : Point}
    (hW : Col f.O f.J W ∧ Parallel f.I f.J y.1 W)
    (hW' : Col f.O f.J W' ∧ Parallel f.I f.J y.1 W') :
    W = W' := by
  have hsame : ∀ T : Point, Col y.1 W T ↔ Col y.1 W' T :=
    hplayfair f.I f.J y.1 W y.1 W' y.1
      hW.2 hW'.2 (col_left y.1 W) (col_left y.1 W')
  have hYW' : Col y.1 W W' :=
    (hsame W').mpr (col_right y.1 W')
  have hnparallel : ¬ Parallel y.1 W f.O f.J := by
    intro hbad
    exact frame_IJ_not_parallel_OJ f (hparallel_trans hW.2 hbad)
  exact mul_two_intersections_unique_of_col_line_eq
    hcol_line_eq hW.2.2.1 f.O_ne_J hnparallel
    (col_right y.1 W) hW.1 hYW' hW'.1

/-- The second multiplication projection is unique by the same argument:
two candidate lines through W are parallel to Jx and hence coincide;
the fixed scalar axis is transverse to Jx. -/
theorem mul_second_projection_unique_of_playfair
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (hplayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ Q : Point, Col C D Q ↔ Col E F Q)
    (hcol_line_eq : ∀ {A B C : Point},
      A ≠ B → Col A B C → C ≠ A →
      ∀ T : Point, Col A B T ↔ Col A C T)
    (f : Frame Point) (x : AxisPoint f) (W : Point)
    {z z' : AxisPoint f}
    (hz : Parallel f.J x.1 W z.1)
    (hz' : Parallel f.J x.1 W z'.1) : z = z' := by
  have hsame : ∀ T : Point, Col W z.1 T ↔ Col W z'.1 T :=
    hplayfair f.J x.1 W z.1 W z'.1 W
      hz hz' (col_left W z.1) (col_left W z'.1)
  have hWz' : Col W z.1 z'.1 :=
    (hsame z'.1).mpr (col_right W z'.1)
  have hnparallel : ¬ Parallel W z.1 f.O f.I := by
    intro hbad
    exact frame_JX_not_parallel_OI f x (hparallel_trans hz hbad)
  apply Subtype.ext
  exact mul_two_intersections_unique_of_col_line_eq
    hcol_line_eq hz.2.1 f.O_ne_I hnparallel
    (col_right W z.1) z.2 hWz' z'.2

/-- Multiplication is a total and single-valued *relation* once the two
parallel-projection theorems have been derived. There is no appeal to
numeric coordinates, field laws, or classical algebra. -/
theorem mulTotal_of_two_projections
    (f : Frame Point)
    (hFirst : MulFirstProjectionTotal f)
    (hSecond : MulSecondProjectionTotal f) : MulTotal f := by
  intro x y
  by_cases hy : y.1 = f.O
  · refine ⟨axisZero f, Or.inl ⟨hy, rfl⟩, ?_⟩
    intro z hz
    rcases hz with ⟨_, heq⟩ | ⟨hne, _⟩
    · exact heq
    · exact False.elim (hne hy)
  · obtain ⟨W, ⟨hWcol, hWpar⟩, hWuniq⟩ := hFirst y hy
    obtain ⟨z, hZpar, hZuniq⟩ :=
      hSecond x W hWcol (mul_first_projection_nonzero f y W hWpar)
    refine ⟨z, Or.inr ⟨hy, W, hWcol, hWpar, hZpar⟩, ?_⟩
    intro z' hz'
    rcases hz' with ⟨hy0, _⟩ | ⟨_, W', hW'col, hW'par, hZ'par⟩
    · exact False.elim (hy hy0)
    · have hWeq : W' = W := hWuniq W' ⟨hW'col, hW'par⟩
      subst W'
      exact hZuniq z' hZ'par

/-- A separate functional-graph consequence, useful even before the
ring operations have been packaged as Lean `Add` and `Mul` instances. -/
theorem mulFunctional_of_two_projections
    (f : Frame Point)
    (hFirst : MulFirstProjectionTotal f)
    (hSecond : MulSecondProjectionTotal f) : MulFunctional f := by
  intro a b z w hz hw
  obtain ⟨r, _, huniq⟩ := mulTotal_of_two_projections f hFirst hSecond a b
  exact (huniq z hz).trans (huniq w hw).symm

/-- Every first multiplication projection exists uniquely once the
four general synthetic geometry results have been obtained. -/
theorem mulFirstProjectionTotal_of_geometry
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ U : Point, Parallel A B P U)
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (hplayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ Q : Point, Col C D Q ↔ Col E F Q)
    (hcol_line_eq : ∀ {A B C : Point},
      A ≠ B → Col A B C → C ≠ A →
      ∀ T : Point, Col A B T ↔ Col A C T)
    (f : Frame Point) : MulFirstProjectionTotal f := by
  intro y hy
  obtain ⟨W, hWcol, hWpar⟩ :=
    mul_first_projection_exists_of_incidence
      hparallel_through hparallel_trans hcol_line_eq f y hy
  refine ⟨W, ⟨hWcol, hWpar⟩, ?_⟩
  intro W' hW'
  exact (mul_first_projection_unique_of_playfair
    hparallel_trans hplayfair hcol_line_eq
    f y ⟨hWcol, hWpar⟩ hW').symm

/-- Every second multiplication projection exists uniquely under the
same geometry results. The nonzero W hypothesis is precisely what
ensures a nondegenerate line from W to the scalar axis. -/
theorem mulSecondProjectionTotal_of_geometry
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ U : Point, Parallel A B P U)
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (hplayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ Q : Point, Col C D Q ↔ Col E F Q)
    (hcol_line_eq : ∀ {A B C : Point},
      A ≠ B → Col A B C → C ≠ A →
      ∀ T : Point, Col A B T ↔ Col A C T)
    (f : Frame Point) : MulSecondProjectionTotal f := by
  intro x W hWcol hWne
  obtain ⟨z, hz⟩ :=
    mul_second_projection_exists_of_incidence
      hparallel_through hparallel_trans hcol_line_eq
      f x W hWcol hWne
  refine ⟨z, hz, ?_⟩
  intro z' hz'
  exact (mul_second_projection_unique_of_playfair
    hparallel_trans hplayfair hcol_line_eq
    f x W hz hz').symm

/-- A fully spelled out proof of multiplication totality from four
specific *synthetic* theorems: through-point parallel existence,
parallel transitivity, Playfair uniqueness and neutral line extensionality.
No generic field operation or extra plane axiom appears in the result. -/
theorem mulTotal_of_geometry
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ U : Point, Parallel A B P U)
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (hplayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ Q : Point, Col C D Q ↔ Col E F Q)
    (hcol_line_eq : ∀ {A B C : Point},
      A ≠ B → Col A B C → C ≠ A →
      ∀ T : Point, Col A B T ↔ Col A C T)
    (f : Frame Point) : MulTotal f :=
  mulTotal_of_two_projections f
    (mulFirstProjectionTotal_of_geometry
      hparallel_through hparallel_trans hplayfair hcol_line_eq f)
    (mulSecondProjectionTotal_of_geometry
      hparallel_through hparallel_trans hplayfair hcol_line_eq f)

/-- Multiplication functionality follows from the two completed
geometric projection uniqueness proofs, independently of all field laws. -/
theorem mulFunctional_of_geometry
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ U : Point, Parallel A B P U)
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (hplayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ Q : Point, Col C D Q ↔ Col E F Q)
    (hcol_line_eq : ∀ {A B C : Point},
      A ≠ B → Col A B C → C ≠ A →
      ∀ T : Point, Col A B T ↔ Col A C T)
    (f : Frame Point) : MulFunctional f :=
  mulFunctional_of_two_projections f
    (mulFirstProjectionTotal_of_geometry
      hparallel_through hparallel_trans hplayfair hcol_line_eq f)
    (mulSecondProjectionTotal_of_geometry
      hparallel_through hparallel_trans hplayfair hcol_line_eq f)

/-- Totality of the full multiplication graph already entails existence
of the first projection, since the product with left operand 1 exposes its
auxiliary point W. This is a necessary geometric subgoal, not a new axiom. -/
theorem mul_first_projection_exists_of_mulTotal
    (f : Frame Point) (hTotal : MulTotal f)
    (y : AxisPoint f) (hy : y.1 ≠ f.O) :
    ∃ W : Point, Col f.O f.J W ∧ Parallel f.I f.J y.1 W := by
  obtain ⟨z, hz, _⟩ := hTotal (axisOne f) y
  rcases hz with ⟨hy0, _⟩ | ⟨_, W, hcol, hpar, _⟩
  · exact False.elim (hy hy0)
  · exact ⟨W, hcol, hpar⟩

/-- Multiplication by 1 on the left needs merely existence of its
first geometric projection. Full uniqueness and the second projection
are unnecessary here. -/
theorem mulLeftOne_of_first_projection_exists
    (f : Frame Point)
    (hFirst : ∀ y : AxisPoint f, y.1 ≠ f.O →
      ∃ W : Point, Col f.O f.J W ∧ Parallel f.I f.J y.1 W) :
    MulLeftOneLaw f := by
  intro a
  by_cases ha : a.1 = f.O
  · refine Or.inl ⟨ha, ?_⟩
    exact Subtype.ext ha
  · obtain ⟨W, hWcol, hWpar⟩ := hFirst a ha
    exact Or.inr ⟨ha, W, hWcol, hWpar, parallel_reverse_both hWpar⟩

/-- A special case using an existing first-projection
existence-and-uniqueness theorem. -/
theorem mulLeftOne_of_first_projection
    (f : Frame Point)
    (hFirst : MulFirstProjectionTotal f) : MulLeftOneLaw f :=
  mulLeftOne_of_first_projection_exists f
    (fun y hy =>
      let ⟨W, hW, _⟩ := hFirst y hy
      ⟨W, hW⟩)

/-- An alternative derivation when one already knows totality of MulGraph.
The witness need not be unique for this argument. -/
theorem mulLeftOne_of_mulTotal
    (f : Frame Point) (hTotal : MulTotal f) : MulLeftOneLaw f := by
  intro a
  obtain ⟨z, hz, _⟩ := hTotal (axisOne f) a
  rcases hz with ⟨ha, _⟩ | ⟨ha, W, hWcol, hWpar, _⟩
  · exact Or.inl ⟨ha, Subtype.ext ha⟩
  · exact Or.inr ⟨ha, W, hWcol, hWpar, parallel_reverse_both hWpar⟩

/-- The left unit follows from the same synthetic geometry ingredients
and, in fact, uses only its first existence projection. -/
theorem mulLeftOne_of_geometry
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ U : Point, Parallel A B P U)
    (hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F)
    (hcol_line_eq : ∀ {A B C : Point},
      A ≠ B → Col A B C → C ≠ A →
      ∀ T : Point, Col A B T ↔ Col A C T)
    (f : Frame Point) : MulLeftOneLaw f :=
  mulLeftOne_of_first_projection_exists f
    (mul_first_projection_exists_of_incidence
      hparallel_through hparallel_trans hcol_line_eq f)

end TarskiField


/-! SOURCE: workstreams/FieldLaws.lean -/


namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-!
Standalone TarskiField module for the geometric field-law workstream.

It does not postulate any geometry or field axioms. The hypotheses `hAdd`,
`hMul`, `hAssoc`, etc. are explicitly named *outstanding theorem obligations*.
What is proved here is the exact bridge from relational construction graphs to
ordinary operations once those geometric obligations have been discharged.

This fragment has not yet been compiled with Lean 4.
-/

-- DEPENDENCY: definitions of `AddTotal`, `MulTotal`, all relational laws,
-- and the previously proved `add_zero_left`, `mul_zero_right`, `mul_one_right`.

theorem addFunctional_of_total (f : Frame Point) (hAdd : AddTotal f) :
    AddFunctional f := by
  intro x y z w hz hw
  obtain ⟨v, hv, hunique⟩ := hAdd x y
  exact (hunique z hz).trans (hunique w hw).symm

theorem mulFunctional_of_total (f : Frame Point) (hMul : MulTotal f) :
    MulFunctional f := by
  intro x y z w hz hw
  obtain ⟨v, hv, hunique⟩ := hMul x y
  exact (hunique z hz).trans (hunique w hw).symm

/-- The internally constructed addition operation; no field operation
    on `Point` or on `AxisPoint` is used. -/
noncomputable def axisAddOf (f : Frame Point) (hAdd : AddTotal f)
    (x y : AxisPoint f) : AxisPoint f :=
  Classical.choose (hAdd x y)

theorem axisAddOf_spec (f : Frame Point) (hAdd : AddTotal f)
    (x y : AxisPoint f) :
    AddGraph f x y (axisAddOf f hAdd x y) :=
  (Classical.choose_spec (hAdd x y)).1

theorem addGraph_iff_axisAddOf_eq (f : Frame Point)
    (hAdd : AddTotal f) (x y z : AxisPoint f) :
    AddGraph f x y z ↔ axisAddOf f hAdd x y = z := by
  constructor
  · intro hz
    exact ((Classical.choose_spec (hAdd x y)).2 z hz).symm
  · intro hz
    rw [← hz]
    exact axisAddOf_spec f hAdd x y

/-- The internally constructed multiplication operation. -/
noncomputable def axisMulOf (f : Frame Point) (hMul : MulTotal f)
    (x y : AxisPoint f) : AxisPoint f :=
  Classical.choose (hMul x y)

theorem axisMulOf_spec (f : Frame Point) (hMul : MulTotal f)
    (x y : AxisPoint f) :
    MulGraph f x y (axisMulOf f hMul x y) :=
  (Classical.choose_spec (hMul x y)).1

theorem mulGraph_iff_axisMulOf_eq (f : Frame Point)
    (hMul : MulTotal f) (x y z : AxisPoint f) :
    MulGraph f x y z ↔ axisMulOf f hMul x y = z := by
  constructor
  · intro hz
    exact ((Classical.choose_spec (hMul x y)).2 z hz).symm
  · intro hz
    rw [← hz]
    exact axisMulOf_spec f hMul x y

/-- These three unit/zero laws *are* consequences of existing geometry once
    the relevant construction is known to be total and functional. -/
theorem axisAddOf_zero_left (f : Frame Point) (hAdd : AddTotal f)
    (x : AxisPoint f) :
    axisAddOf f hAdd (axisZero f) x = x :=
  (addGraph_iff_axisAddOf_eq f hAdd (axisZero f) x x).mp
    (add_zero_left f x)

theorem axisMulOf_zero_right (f : Frame Point) (hMul : MulTotal f)
    (x : AxisPoint f) :
    axisMulOf f hMul x (axisZero f) = axisZero f :=
  (mulGraph_iff_axisMulOf_eq f hMul x (axisZero f) (axisZero f)).mp
    (mul_zero_right f x)

theorem axisMulOf_one_right (f : Frame Point) (hMul : MulTotal f)
    (x : AxisPoint f) :
    axisMulOf f hMul x (axisOne f) = x :=
  (mulGraph_iff_axisMulOf_eq f hMul x (axisOne f) x).mp
    (mul_one_right f x)

/-- The following are translations of the exact relational geometric law
    goals, not derivations of those law goals from the primitive axioms. -/
theorem axisAddOf_comm_of_law (f : Frame Point) (hAdd : AddTotal f)
    (hComm : AddCommLaw f) (x y : AxisPoint f) :
    axisAddOf f hAdd x y = axisAddOf f hAdd y x := by
  have h : AddGraph f y x (axisAddOf f hAdd x y) :=
    hComm x y (axisAddOf f hAdd x y) (axisAddOf_spec f hAdd x y)
  exact ((addGraph_iff_axisAddOf_eq f hAdd y x _).mp h).symm

theorem axisAddOf_assoc_of_law (f : Frame Point) (hAdd : AddTotal f)
    (hAssoc : AddAssocLaw f) (x y z : AxisPoint f) :
    axisAddOf f hAdd (axisAddOf f hAdd x y) z =
      axisAddOf f hAdd x (axisAddOf f hAdd y z) := by
  exact hAssoc x y z
    (axisAddOf f hAdd x y) (axisAddOf f hAdd y z)
    (axisAddOf f hAdd (axisAddOf f hAdd x y) z)
    (axisAddOf f hAdd x (axisAddOf f hAdd y z))
    (axisAddOf_spec f hAdd x y)
    (axisAddOf_spec f hAdd (axisAddOf f hAdd x y) z)
    (axisAddOf_spec f hAdd y z)
    (axisAddOf_spec f hAdd x (axisAddOf f hAdd y z))

theorem axisAddOf_zero_right_of_law (f : Frame Point)
    (hAdd : AddTotal f) (hZero : AddRightZeroLaw f)
    (x : AxisPoint f) :
    axisAddOf f hAdd x (axisZero f) = x :=
  (addGraph_iff_axisAddOf_eq f hAdd x (axisZero f) x).mp (hZero x)

theorem axisAddOf_inverse_of_law (f : Frame Point)
    (hAdd : AddTotal f) (hInverse : AddInverseLaw f)
    (x : AxisPoint f) :
    ∃ y : AxisPoint f, axisAddOf f hAdd x y = axisZero f := by
  obtain ⟨y, hy⟩ := hInverse x
  exact ⟨y, (addGraph_iff_axisAddOf_eq f hAdd x y (axisZero f)).mp hy⟩

theorem axisMulOf_comm_of_law (f : Frame Point) (hMul : MulTotal f)
    (hComm : MulCommLaw f) (x y : AxisPoint f) :
    axisMulOf f hMul x y = axisMulOf f hMul y x := by
  have h : MulGraph f y x (axisMulOf f hMul x y) :=
    hComm x y (axisMulOf f hMul x y) (axisMulOf_spec f hMul x y)
  exact ((mulGraph_iff_axisMulOf_eq f hMul y x _).mp h).symm

theorem axisMulOf_assoc_of_law (f : Frame Point) (hMul : MulTotal f)
    (hAssoc : MulAssocLaw f) (x y z : AxisPoint f) :
    axisMulOf f hMul (axisMulOf f hMul x y) z =
      axisMulOf f hMul x (axisMulOf f hMul y z) := by
  exact hAssoc x y z
    (axisMulOf f hMul x y) (axisMulOf f hMul y z)
    (axisMulOf f hMul (axisMulOf f hMul x y) z)
    (axisMulOf f hMul x (axisMulOf f hMul y z))
    (axisMulOf_spec f hMul x y)
    (axisMulOf_spec f hMul (axisMulOf f hMul x y) z)
    (axisMulOf_spec f hMul y z)
    (axisMulOf_spec f hMul x (axisMulOf f hMul y z))

theorem axisMulOf_one_left_of_law (f : Frame Point)
    (hMul : MulTotal f) (hOne : MulLeftOneLaw f)
    (x : AxisPoint f) :
    axisMulOf f hMul (axisOne f) x = x :=
  (mulGraph_iff_axisMulOf_eq f hMul (axisOne f) x x).mp (hOne x)

theorem axisMulOf_inverse_of_law (f : Frame Point)
    (hMul : MulTotal f) (hInverse : MulInverseLaw f)
    (x : AxisPoint f) (hx : x ≠ axisZero f) :
    ∃ y : AxisPoint f, axisMulOf f hMul x y = axisOne f := by
  obtain ⟨y, hy⟩ := hInverse x hx
  exact ⟨y, (mulGraph_iff_axisMulOf_eq f hMul x y (axisOne f)).mp hy⟩

theorem axisMulOf_left_distrib_of_law (f : Frame Point)
    (hAdd : AddTotal f) (hMul : MulTotal f)
    (hDistrib : LeftDistributiveLaw f) (a b c : AxisPoint f) :
    axisMulOf f hMul a (axisAddOf f hAdd b c) =
      axisAddOf f hAdd
        (axisMulOf f hMul a b) (axisMulOf f hMul a c) := by
  exact hDistrib a b c
    (axisAddOf f hAdd b c)
    (axisMulOf f hMul a b)
    (axisMulOf f hMul a c)
    (axisMulOf f hMul a (axisAddOf f hAdd b c))
    (axisAddOf f hAdd (axisMulOf f hMul a b) (axisMulOf f hMul a c))
    (axisAddOf_spec f hAdd b c)
    (axisMulOf_spec f hMul a (axisAddOf f hAdd b c))
    (axisMulOf_spec f hMul a b)
    (axisMulOf_spec f hMul a c)
    (axisAddOf_spec f hAdd (axisMulOf f hMul a b) (axisMulOf f hMul a c))

/-!
## Exact GeoCoq arithmetization predicates and proven nondegenerate bridge

GeoCoq Definitions, 14.2–14.4 define `Pj A B C D` as `Par A B C D ∨ C = D`.
The equality disjunct is essential: it admits projections with a degenerate
moving segment. `Parallel` in our project disallows such segments. The
relation below copies the *weak* GeoCoq projection pattern using **our**
`Parallel`; a separate collinearity theorem is still required to identify
our extensional `Parallel` with GeoCoq's `Par` in an arbitrary Tarski plane.

The geometric multiplication diagram in our source agrees with GeoCoq's
`Prod O E E' A B C` once one considers the degenerate projection cases.
The forward theorem below is unconditional. The reverse direction is
currently proved for genuinely nondegenerate projection witnesses; removing
the two inequalities is a specific incidence lemma, not a field axiom.
-/

/-- Weak parallel projection in the shape of GeoCoq, §14.2. -/
def GeoCoqPj (A B C D : Point) : Prop :=
  Parallel A B C D ∨ C = D

/-- GeoCoq's two-projection product diagram, specialized to a Tarski frame. -/
def GeoCoqProd (f : Frame Point) (x y z : AxisPoint f) : Prop :=
  ∃ W : Point,
    GeoCoqPj f.I f.J y.1 W ∧
    Col f.O f.J W ∧
    GeoCoqPj f.J x.1 W z.1

/-- Even with GeoCoq's weak `Pj`, a nonzero scalar cannot be projected
    along IJ *onto the origin*: the IJ line meets the scalar axis at I,
    while O does not lie on IJ. This uses only the source's previously
    proved symmetry of collinearity and the definition of parallelism. -/
theorem geoCoq_firstPj_not_origin (f : Frame Point)
    (y : AxisPoint f) (W : Point)
    (hy : y.1 ≠ f.O)
    (hProj : GeoCoqPj f.I f.J y.1 W) :
    W ≠ f.O := by
  intro hW
  rcases hProj with hpar | heq
  · have hcol : Col y.1 W f.I := by
      simpa [hW] using (col_rotate (col_rotate y.2))
    have hsame : ∀ V : Point,
        Col f.I f.J V ↔ Col y.1 W V :=
      parallel_same_of_intersection hpar
        (col_left f.I f.J) hcol
    have hIJO : Col f.I f.J f.O :=
      (hsame f.O).mpr (by
        simpa [hW] using (col_right y.1 f.O))
    exact f.noncol (col_rotate (col_rotate hIJO))
  · exact hy (heq.trans hW)

/-- Extract a genuinely non-origin intermediate point from any weak
    GeoCoq product with nonzero second argument. -/
theorem geoCoqProd_nonzero_intermediate (f : Frame Point)
    (x y z : AxisPoint f) (hy : y.1 ≠ f.O)
    (hProd : GeoCoqProd f x y z) :
    ∃ W : Point, W ≠ f.O ∧
      GeoCoqPj f.I f.J y.1 W ∧
      Col f.O f.J W ∧
      GeoCoqPj f.J x.1 W z.1 := by
  obtain ⟨W, hFirst, hAxis, hSecond⟩ := hProd
  exact ⟨W, geoCoq_firstPj_not_origin f y W hy hFirst,
    hFirst, hAxis, hSecond⟩

/-- A genuinely proved relation to the GeoCoq multiplication diagram:
    every multiplication graph built from our strict parallel projections
    satisfies GeoCoq's weak-projection product, including multiplication by 0. -/
theorem mulGraph_implies_geoCoqProd (f : Frame Point)
    (x y z : AxisPoint f) :
    MulGraph f x y z → GeoCoqProd f x y z := by
  intro h
  rcases h with ⟨hy, hz⟩ | ⟨_, W, hWcol, hFirst, hSecond⟩
  · refine ⟨f.O, Or.inr hy, col_left f.O f.J, Or.inr ?_⟩
    exact (congrArg Subtype.val hz).symm
  · exact ⟨W, Or.inl hFirst, hWcol, Or.inl hSecond⟩

/-- The nondegenerate portion of GeoCoq multiplication, keeping all
    witnesses in the purely geometric language. -/
def GeoCoqProdNondeg (f : Frame Point) (x y z : AxisPoint f) : Prop :=
  y.1 ≠ f.O ∧
  ∃ W : Point,
    Col f.O f.J W ∧
    GeoCoqPj f.I f.J y.1 W ∧
    GeoCoqPj f.J x.1 W z.1 ∧
    y.1 ≠ W ∧ W ≠ z.1

/-- Exact equivalence in the nondegenerate branch. This lemma uses no
    incidence closure axiom, no field law and no Euclidean coordinates. -/
theorem geoCoqProdNondeg_iff_mulGraph (f : Frame Point)
    (x y z : AxisPoint f) :
    GeoCoqProdNondeg f x y z ↔
      (y.1 ≠ f.O ∧ MulGraph f x y z) := by
  constructor
  · rintro ⟨hy, W, hcol, hFirst, hSecond, hneqFirst, hneqSecond⟩
    have hp : Parallel f.I f.J y.1 W := by
      rcases hFirst with h | h
      · exact h
      · exact False.elim (hneqFirst h)
    have hq : Parallel f.J x.1 W z.1 := by
      rcases hSecond with h | h
      · exact h
      · exact False.elim (hneqSecond h)
    exact ⟨hy, Or.inr ⟨hy, W, hcol, hp, hq⟩⟩
  · rintro ⟨hy, hmul⟩
    rcases hmul with ⟨hy0, _⟩ | ⟨_, W, hcol, hp, hq⟩
    · exact False.elim (hy hy0)
    · exact ⟨hy, W, hcol, Or.inl hp, Or.inl hq, hp.2.1, hq.2.1⟩

/-- Removing *both* artificial degenerate projections in the y ≠ O case
    requires only one further incidence theorem: the OI and OJ axes meet
    at O alone. That theorem is an outstanding consequence of the Tarski
    betweenness axioms; it is a named hypothesis here, never declared as
    a new axiom of the geometry. -/
theorem geoCoqProd_nonzero_implies_mulGraph_of_axis_intersection
    (f : Frame Point) (x y z : AxisPoint f)
    (hAxes : ∀ W : Point,
      Col f.O f.I W → Col f.O f.J W → W = f.O)
    (hy : y.1 ≠ f.O)
    (hProd : GeoCoqProd f x y z) :
    MulGraph f x y z := by
  obtain ⟨W, hFirst, hAxis, hSecond⟩ := hProd
  have hW0 : W ≠ f.O :=
    geoCoq_firstPj_not_origin f y W hy hFirst
  have hYW : y.1 ≠ W := by
    intro heq
    have hWaxis : Col f.O f.I W := by
      rw [← heq]
      exact y.2
    exact hy (heq.trans (hAxes W hWaxis hAxis))
  have hWz : W ≠ z.1 := by
    intro heq
    have hWaxis : Col f.O f.I W := by
      rw [heq]
      exact z.2
    exact hW0 (hAxes W hWaxis hAxis)
  have hNondeg : GeoCoqProdNondeg f x y z :=
    ⟨hy, W, hAxis, hFirst, hSecond, hYW, hWz⟩
  exact ((geoCoqProdNondeg_iff_mulGraph f x y z).mp hNondeg).2

/-- GeoCoq's four-projection sum diagram, specialized to a Tarski frame.
    Unlike `RawAddGraph`, this uses the diagonal direction `I J` and
    two auxiliary points. Proving their equality is a separate geometric
    result. We do not assert it here. -/
def GeoCoqSum (f : Frame Point) (x y z : AxisPoint f) : Prop :=
  ∃ A' C' : Point,
    GeoCoqPj f.I f.J x.1 A' ∧
    Col f.O f.J A' ∧
    GeoCoqPj f.O f.I A' C' ∧
    GeoCoqPj f.O f.J y.1 C' ∧
    GeoCoqPj f.J f.I C' z.1

/-!
## Precise synthetic Pappus / Desargues proof targets

These are `Prop` definitions, NOT new axioms or typeclass assumptions.
`affinePappusParallel` is the exact parallel consequence `l13_11` of
GeoCoq's synthetic Pappus chapter (13.5), with its original point order.
`affineDesarguesParallel` is GeoCoq `l13_15` (chapter 13.6): one noncollinear
triangle and two strictly parallel corresponding sides in a perspectivity
configuration force the third side parallel. The remaining task is to prove
these predicates from the existing Tarski `Plane` axioms and then instantiate
the multiplication diagrams. We deliberately make no completion claim.
-/

/-- Disjointness of two nondegenerate affine lines. -/
def StrictParallel (A B C D : Point) : Prop :=
  A ≠ B ∧ C ≠ D ∧
  ∀ X : Point, ¬ (Col A B X ∧ Col C D X)

theorem strictParallel_implies_parallel {A B C D : Point}
    (h : StrictParallel A B C D) : Parallel A B C D := by
  exact ⟨h.1, h.2.1, Or.inr h.2.2⟩

/-- The exact affine-parallel form of Pappus, GeoCoq `l13_11`. -/
def AffinePappusParallel : Prop :=
  ∀ O A B C A' B' C' : Point,
    ¬ Col O A A' →
    B ≠ O → C ≠ O → Col O A B → Col O B C →
    B' ≠ O → C' ≠ O → Col O A' B' → Col O B' C' →
    Parallel B C' C B' → Parallel C A' A C' →
    Parallel A B' B A'

/-- Parallelism is invariant under reversing both defining segments.
    A primitive-geometry fact used when matching a product's final
    projection to the orientation of Pappus's conclusion. -/
theorem field_parallel_reverse_both {A B C D : Point}
    (h : Parallel A B C D) : Parallel B A D C := by
  rcases h with ⟨hAB, hCD, hsame | hdisj⟩
  · refine ⟨hAB.symm, hCD.symm, Or.inl ?_⟩
    intro V
    constructor
    · intro hBA
      exact col_swap ((hsame V).mp (col_swap hBA))
    · intro hDC
      exact col_swap ((hsame V).mpr (col_swap hDC))
  · refine ⟨hAB.symm, hCD.symm, Or.inr ?_⟩
    intro V hV
    exact hdisj V ⟨col_swap hV.1, col_swap hV.2⟩

/-- A genuinely new unconditional incidence lemma proved directly using the
    primitive Tarski definition of `Parallel`: two parallel nondegenerate
    lines through the same first point contain one another's endpoints.
    This is the synthetic fact used in the zero-product proof below. -/
theorem parallel_common_origin_contains_third {O A B : Point}
    (hPar : Parallel O A O B) : Col O A B := by
  have hsame : ∀ V : Point, Col O A V ↔ Col O B V :=
    parallel_same_of_intersection hPar
      (col_left O A) (col_left O B)
  exact (hsame B).mpr (col_right O B)

/-- Actual point substitution in GeoCoq `prod_comm`:
    `l13_11 C B A E' A' B' O`. The earlier projection equality of slopes
    supplies `hCross`; the original product supplies `hMul`. The Pappus
    conclusion is exactly the final parallel projection of the *reversed*
    multiplication. This is a conditional Pappus application, not a proof
    of Pappus from the Tarski axioms. -/
theorem pappus_product_swap_parallel
    (f : Frame Point) (x y z : AxisPoint f) (wx wy : Point)
    (hPappus : AffinePappusParallel (Point := Point))
    (hnoncol : ¬ Col f.O z.1 f.J)
    (hy : y.1 ≠ f.O) (hx : x.1 ≠ f.O)
    (hZy : Col f.O z.1 y.1)
    (hyX : Col f.O y.1 x.1)
    (hwx : wx ≠ f.O) (hwy : wy ≠ f.O)
    (hJwx : Col f.O f.J wx)
    (hwxWy : Col f.O wx wy)
    (hCross : Parallel y.1 wy x.1 wx)
    (hMul : Parallel f.J x.1 wy z.1) :
    Parallel z.1 wx y.1 f.J := by
  apply hPappus f.O z.1 y.1 x.1 f.J wx wy
    hnoncol hy hx hZy hyX hwx hwy hJwx hwxWy hCross
  exact field_parallel_reverse_both hMul

/-- The exact incidence theorem `col_transitivity_1` of GeoCoq Ch06.
    Its proof from `Plane` is an outstanding Ch05/Ch06 task, so this is
    a target proposition rather than an additional axiom. -/
def ColTransitivityGoal : Prop :=
  ∀ P Q A B : Point,
    P ≠ Q → Col P Q A → Col P Q B → Col P A B

/-- Euclidean parallel transitivity, likewise a synthetic theorem goal. -/
def ParallelTransitivityGoal : Prop :=
  ∀ A B C D E F : Point,
    Parallel A B C D → Parallel C D E F → Parallel A B E F

/-- Collinearity of two scalar points with an arbitrary nonzero
    axis point follows from GeoCoq's incidence transitivity target. -/
theorem axis_col_of_colTrans (f : Frame Point)
    (hCol : ColTransitivityGoal (Point := Point))
    (a b : AxisPoint f) : Col f.O a.1 b.1 := by
  exact hCol f.O f.I a.1 b.1 f.O_ne_I a.2 b.2

/-- A nonzero scalar cannot lie on the auxiliary line OJ. This
    derives the crucial noncollinearity in the Pappus configuration. -/
theorem axis_not_col_aux_of_colTrans (f : Frame Point)
    (hCol : ColTransitivityGoal (Point := Point)) (a : AxisPoint f)
    (ha : a.1 ≠ f.O) : ¬ Col f.O a.1 f.J := by
  intro hOJ
  have hOI : Col f.O a.1 f.I := col_rotate (col_swap a.2)
  exact f.noncol (hCol f.O a.1 f.I f.J ha.symm hOI hOJ)

/-- The chosen axis OI and the auxiliary axis OJ have exactly one common
    point. This is a geometric incidence consequence of Ch06's target, not
    an appeal to any scalar field property. -/
theorem frame_axes_intersection_unique_of_colTrans
    (f : Frame Point) (hCol : ColTransitivityGoal (Point := Point))
    (Z : Point) (hZI : Col f.O f.I Z) (hZJ : Col f.O f.J Z) :
    Z = f.O := by
  by_contra hZO
  have hOZI : Col f.O Z f.I := col_rotate (col_swap hZI)
  have hOZJ : Col f.O Z f.J := col_rotate (col_swap hZJ)
  have hOZ : f.O ≠ Z := fun h => hZO h.symm
  exact f.noncol (hCol f.O Z f.I f.J hOZ hOZI hOZJ)

/-- Even GeoCoq's weaker projection relation cannot produce a nonzero
    output when the second multiplication input is the origin. The first
    weak projection is forced to W = O because IJ and OJ intersect at J;
    the second is then forced to z = O because Jx and Oz intersect at x.
    Only Ch06's collinearity transfer is used in the second step. -/
theorem geoCoqProd_zero_right_forces_zero_of_colTrans
    (f : Frame Point) (hCol : ColTransitivityGoal (Point := Point))
    (x z : AxisPoint f)
    (hProd : GeoCoqProd f x (axisZero f) z) :
    z = axisZero f := by
  obtain ⟨W, hFirst, hWAxis, hSecond⟩ := hProd
  have hWzero : W = f.O := by
    rcases hFirst with hPar | hEq
    · have hOWJ : Col f.O W f.J :=
        col_rotate (col_swap hWAxis)
      have hsame : ∀ V : Point,
          Col f.I f.J V ↔ Col f.O W V :=
        parallel_same_of_intersection hPar
          (col_right f.I f.J) hOWJ
      have hIJO : Col f.I f.J f.O :=
        (hsame f.O).mpr (col_left f.O W)
      exact False.elim (f.noncol (col_rotate (col_rotate hIJO)))
    · exact hEq.symm
  subst W
  rcases hSecond with hPar | hEq
  · have hOzx : Col f.O z.1 x.1 :=
      hCol f.O f.I z.1 x.1 f.O_ne_I z.2 x.2
    have hsame : ∀ V : Point,
        Col f.J x.1 V ↔ Col f.O z.1 V :=
      parallel_same_of_intersection hPar
        (col_right f.J x.1) hOzx
    have hOzJ : Col f.O z.1 f.J :=
      (hsame f.J).mp (col_left f.J x.1)
    have hOJz : Col f.O f.J z.1 :=
      col_rotate (col_swap hOzJ)
    exact Subtype.ext
      (frame_axes_intersection_unique_of_colTrans f hCol
        z.1 z.2 hOJz)
  · exact Subtype.ext hEq.symm

/-- The full (including degenerate zero inputs) equivalence between
    our two-projection `MulGraph` and the weak-projection GeoCoq product
    diagram. Its sole geometric prerequisite is Ch06 incidence transitivity,
    rather than a field law or any coordinate interpretation. -/
theorem geoCoqProd_iff_mulGraph_of_colTrans
    (f : Frame Point) (hCol : ColTransitivityGoal (Point := Point))
    (x y z : AxisPoint f) :
    GeoCoqProd f x y z ↔ MulGraph f x y z := by
  constructor
  · intro hProd
    by_cases hy : y.1 = f.O
    · have hyEq : y = axisZero f := Subtype.ext hy
      subst y
      have hzEq : z = axisZero f :=
        geoCoqProd_zero_right_forces_zero_of_colTrans
          f hCol x z hProd
      subst z
      exact mul_zero_right f x
    · exact geoCoqProd_nonzero_implies_mulGraph_of_axis_intersection
        f x y z
        (fun W hI hJ =>
          frame_axes_intersection_unique_of_colTrans f hCol W hI hJ)
        hy hProd
  · exact mulGraph_implies_geoCoqProd f x y z

/-- A genuine nonzero-product theorem on the original MulGraph: the last
    parallel projection cannot hit O if both input points are nonzero.
    Only the explicit Ch06 collinearity-transfer target remains to prove. -/
theorem mulGraph_output_nonzero_of_inputs_nonzero
    (f : Frame Point) (hCol : ColTransitivityGoal (Point := Point))
    (x y z : AxisPoint f)
    (hMul : MulGraph f x y z)
    (hx : x.1 ≠ f.O) (hy : y.1 ≠ f.O) : z.1 ≠ f.O := by
  rcases hMul with ⟨hyzero, _⟩ | ⟨_, W, hWAxis, hProj, hLast⟩
  · exact False.elim (hy hyzero)
  · intro hz
    have hWO : W ≠ f.O := mul_first_projection_nonzero f y W hProj
    have hJWZ : Parallel f.J x.1 W f.O := by simpa [hz] using hLast
    have hJOnW : Col W f.O f.J := col_rotate (col_rotate hWAxis)
    have hsame : ∀ V : Point, Col f.J x.1 V ↔ Col W f.O V :=
      parallel_same_of_intersection hJWZ
        (col_left f.J x.1) hJOnW
    have hWOx : Col W f.O x.1 :=
      (hsame x.1).mp (col_right f.J x.1)
    have hOWJ : Col f.O W f.J := col_rotate (col_swap hWAxis)
    have hOWx : Col f.O W x.1 := col_swap hWOx
    have hOJx : Col f.O f.J x.1 :=
      hCol f.O W f.J x.1 hWO.symm hOWJ hOWx
    exact (axis_not_col_aux_of_colTrans f hCol x hx)
      (col_rotate (col_swap hOJx))

/-- The previously missing zero-left construction follows from the same
    synthetic incidence lemma once existence is supplied by `MulTotal`.
    No zero-multiplication field axiom is inserted. -/
theorem mulGraph_zero_left_of_total_and_colTrans
    (f : Frame Point) (hTotal : MulTotal f)
    (hCol : ColTransitivityGoal (Point := Point)) (y : AxisPoint f) :
    MulGraph f (axisZero f) y (axisZero f) := by
  by_cases hy : y.1 = f.O
  · have hzero : y = axisZero f := Subtype.ext hy
    subst y
    exact mul_zero_right f (axisZero f)
  · obtain ⟨z, hz, _⟩ := hTotal (axisZero f) y
    rcases hz with ⟨hyzero, _⟩ | ⟨_, W, hWAxis, hProj, hLast⟩
    · exact False.elim (hy hyzero)
    · have hJW : Col f.J f.O W := col_swap hWAxis
      have hsame : ∀ V : Point,
          Col f.J f.O V ↔ Col W z.1 V :=
        parallel_same_of_intersection hLast hJW (col_left W z.1)
      have hzJO : Col f.J f.O z.1 :=
        (hsame z.1).mpr (col_right W z.1)
      have hzOJ : Col f.O f.J z.1 := col_swap hzJO
      have hzO : z.1 = f.O :=
        frame_axes_intersection_unique_of_colTrans f hCol z.1 z.2 hzOJ
      have hzEq : z = axisZero f := Subtype.ext hzO
      subst z
      exact Or.inr ⟨hy, W, hWAxis, hProj, hLast⟩

/-- Fully assembled *nondegenerate* multiplication commutation:
    one first projection for x, the original product for (x,y),
    GeoCoq Ch06 collinearity transport, Euclidean parallel transitivity,
    and the exact Pappus parallel theorem yield the reversed MulGraph.

    No commutativity law, coordinates, or field instance is used. Each
    geometric prerequisite is exposed because its Tarski proof remains
    separate. The zero-input/output branches are NOT claimed here. -/
theorem mulGraph_comm_nonzero_of_pappus
    (f : Frame Point)
    (hCol : ColTransitivityGoal (Point := Point))
    (hParallelTrans : ParallelTransitivityGoal (Point := Point))
    (hPappus : AffinePappusParallel (Point := Point))
    (x y z : AxisPoint f)
    (hx : x.1 ≠ f.O) (hy : y.1 ≠ f.O) (hz : z.1 ≠ f.O)
    (hFirstX : ∃ wx : Point,
      Col f.O f.J wx ∧ Parallel f.I f.J x.1 wx)
    (hMul : MulGraph f x y z) :
    MulGraph f y x z := by
  rcases hMul with ⟨hy0, _⟩ | ⟨_, wy, hWyAxis, hyProj, hMulFinal⟩
  · exact False.elim (hy hy0)
  · obtain ⟨wx, hWxAxis, hxProj⟩ := hFirstX
    have hwx : wx ≠ f.O :=
      geoCoq_firstPj_not_origin f x wx hx (Or.inl hxProj)
    have hwy : wy ≠ f.O :=
      geoCoq_firstPj_not_origin f y wy hy (Or.inl hyProj)
    have hCross : Parallel y.1 wy x.1 wx :=
      hParallelTrans y.1 wy f.I f.J x.1 wx
        (parallel_symm hyProj) hxProj
    have hZy : Col f.O z.1 y.1 :=
      axis_col_of_colTrans f hCol z y
    have hyX : Col f.O y.1 x.1 :=
      axis_col_of_colTrans f hCol y x
    have hWxWy : Col f.O wx wy :=
      hCol f.O f.J wx wy f.O_ne_J hWxAxis hWyAxis
    have hNoncol : ¬ Col f.O z.1 f.J :=
      axis_not_col_aux_of_colTrans f hCol z hz
    have hSwap : Parallel z.1 wx y.1 f.J :=
      pappus_product_swap_parallel f x y z wx wy
        hPappus hNoncol hy hx hZy hyX
        hwx hwy hWxAxis hWxWy hCross hMulFinal
    exact Or.inr ⟨hx, wx, hWxAxis, hxProj,
      field_parallel_reverse_both (parallel_symm hSwap)⟩

/-- Full relational multiplication commutativity follows from the **named
    pure-geometric outstanding facts** Pappus, collinearity transfer,
    parallel transitivity, the zero-left construction, and preservation
    of nonzeroness by the nondegenerate two-projection product. In
    particular the theorem does not assume `MulCommLaw` as a premise.
    The workstream must still establish each named hypothesis from `Plane`.
-/
theorem mulCommLaw_of_pappus_and_geometry
    (f : Frame Point)
    (hTotal : MulTotal f)
    (hCol : ColTransitivityGoal (Point := Point))
    (hParallelTrans : ParallelTransitivityGoal (Point := Point))
    (hPappus : AffinePappusParallel (Point := Point))
    (hZeroLeft : ∀ a : AxisPoint f,
      MulGraph f (axisZero f) a (axisZero f))
    (hProdNonzero : ∀ a b c : AxisPoint f,
      MulGraph f a b c →
      a.1 ≠ f.O → b.1 ≠ f.O → c.1 ≠ f.O) :
    MulCommLaw f := by
  intro x y z hxy
  by_cases hy0 : y.1 = f.O
  · have hy : y = axisZero f := Subtype.ext hy0
    subst y
    have hz : z = axisZero f :=
      mul_zero_right_unique f x z hxy
    subst z
    exact hZeroLeft x
  · by_cases hx0 : x.1 = f.O
    · have hx : x = axisZero f := Subtype.ext hx0
      subst x
      obtain ⟨w, _, hunique⟩ := hTotal (axisZero f) y
      have hz : z = axisZero f :=
        (hunique z hxy).trans
          (hunique (axisZero f) (hZeroLeft y)).symm
      subst z
      exact mul_zero_right f y
    · have hz : z.1 ≠ f.O :=
        hProdNonzero x y z hxy hx0 hy0
      obtain ⟨w, hw, _⟩ := hTotal y x
      have hFirstX : ∃ wx : Point,
          Col f.O f.J wx ∧ Parallel f.I f.J x.1 wx := by
        rcases hw with ⟨hzero, _⟩ | ⟨_, wx, hcol, hpar, _⟩
        · exact False.elim (hx0 hzero)
        · exact ⟨wx, hcol, hpar⟩
      exact mulGraph_comm_nonzero_of_pappus f hCol
        hParallelTrans hPappus x y z hx0 hy0 hz hFirstX hxy

/-- The actual commutativity target now requires only existence/uniqueness,
    Ch06 collinearity transitivity, parallel transitivity, and Pappus. The
    formerly separate zero-left and nonzero-product hypotheses are *proved*
    above from the original MulGraph and these same incidence hypotheses. -/
theorem mulCommLaw_of_pappus
    (f : Frame Point)
    (hTotal : MulTotal f)
    (hCol : ColTransitivityGoal (Point := Point))
    (hParallelTrans : ParallelTransitivityGoal (Point := Point))
    (hPappus : AffinePappusParallel (Point := Point)) :
    MulCommLaw f := by
  exact mulCommLaw_of_pappus_and_geometry f
    hTotal hCol hParallelTrans hPappus
    (mulGraph_zero_left_of_total_and_colTrans f hTotal hCol)
    (mulGraph_output_nonzero_of_inputs_nonzero f hCol)

/-- The exact affine-parallel Desargues theorem, GeoCoq `l13_15`. -/
def AffineDesarguesParallel : Prop :=
  ∀ A B C A' B' C' O : Point,
    ¬ Col A B C →
    StrictParallel A B A' B' →
    StrictParallel A C A' C' →
    Col O A A' → Col O B B' → Col O C C' →
    Parallel B C B' C'

/-- The four-pair projection theorem GeoCoq `l13_19`, the most directly
    reusable Desargues consequence for multiplication associativity:
    points A,A',C,C' lie on one axis through O; B,B',D,D' on a second.
    Three connecting segments are parallel to their primed analogues;
    the fourth must also be parallel. This is a synthetic *goal predicate*,
    not an assumed property of the plane. -/
def AffineDesarguesFourPairs : Prop :=
  ∀ A B C D A' B' C' D' O : Point,
    ¬ Col O A B →
    O ≠ A → O ≠ A' → O ≠ C → O ≠ C' →
    O ≠ B → O ≠ B' → O ≠ D → O ≠ D' →
    Col O A C → Col O A A' → Col O A C' →
    Col O B D → Col O B B' → Col O B D' →
    Parallel A B A' B' →
    Parallel A D A' D' →
    Parallel B C B' C' →
    Parallel C D C' D'

/-- Actual point substitution in GeoCoq `prod_assoc1`, namely
    `l13_19 B' B E' AB BC' BC C' ABC O`. The conclusion is the final
    projection from the auxiliary point `wc` to `abc` in the direction
    `J → ab`. This records a genuine geometric inference step; the
    Desargues four-pair theorem itself is still to be proved from `Plane`. -/
theorem desargues_associates_product_projection
    (f : Frame Point) (b ab bc abc : AxisPoint f)
    (wb wbc wc : Point)
    (hDesargues : AffineDesarguesFourPairs (Point := Point))
    (hNoncol : ¬ Col f.O wb b.1)
    (hOwb : f.O ≠ wb) (hOwbc : f.O ≠ wbc)
    (hOJ : f.O ≠ f.J) (hOwc : f.O ≠ wc)
    (hOb : f.O ≠ b.1) (hObc : f.O ≠ bc.1)
    (hOab : f.O ≠ ab.1) (hOabc : f.O ≠ abc.1)
    (hWbJ : Col f.O wb f.J)
    (hWbwbc : Col f.O wb wbc)
    (hWbwc : Col f.O wb wc)
    (hbab : Col f.O b.1 ab.1)
    (hbbc : Col f.O b.1 bc.1)
    (hbabc : Col f.O b.1 abc.1)
    (hP1 : Parallel wb b.1 wbc bc.1)
    (hP2 : Parallel wb ab.1 wbc abc.1)
    (hP3 : Parallel b.1 f.J bc.1 wc) :
    Parallel f.J ab.1 wc abc.1 := by
  exact hDesargues wb b.1 f.J ab.1 wbc bc.1 wc abc.1 f.O
    hNoncol hOwb hOwbc hOJ hOwc hOb hObc hOab hOabc
    hWbJ hWbwbc hWbwc hbab hbbc hbabc hP1 hP2 hP3

/-- The nonzero associativity branch assembled on the **actual MulGraph**.
    Original graphs certify a*b=ab, b*c=bc, a*bc=abc. The three
    auxiliary projections provide the exact Desargues four-pair diagram.
    Its conclusion constructs MulGraph f ab c abc. No field law is a
    premise; the remaining assumptions are named synthetic geometric
    theorem goals and explicit nondegeneracy requirements. -/
theorem mulGraph_assoc_nonzero_of_desargues
    (f : Frame Point)
    (hCol : ColTransitivityGoal (Point := Point))
    (hParallelTrans : ParallelTransitivityGoal (Point := Point))
    (hDesargues : AffineDesarguesFourPairs (Point := Point))
    (a b c ab bc abc : AxisPoint f)
    (_ha : a.1 ≠ f.O) (hb : b.1 ≠ f.O) (hc : c.1 ≠ f.O)
    (hab : ab.1 ≠ f.O) (hbc : bc.1 ≠ f.O)
    (habc : abc.1 ≠ f.O)
    (hAB : MulGraph f a b ab)
    (hBC : MulGraph f b c bc)
    (hABC : MulGraph f a bc abc) :
    MulGraph f ab c abc := by
  rcases hAB with ⟨hzero, _⟩ | ⟨_, wb, hWbAxis, hbProj, hABFinal⟩
  · exact False.elim (hb hzero)
  · rcases hBC with ⟨hzero, _⟩ | ⟨_, wc, hWcAxis, hcProj, hBCFinal⟩
    · exact False.elim (hc hzero)
    · rcases hABC with ⟨hzero, _⟩ | ⟨_, wbc, hWbcAxis, hbcProj, hABCFinal⟩
      · exact False.elim (hbc hzero)
      · have hwb : wb ≠ f.O :=
          geoCoq_firstPj_not_origin f b wb hb (Or.inl hbProj)
        have hwbc : wbc ≠ f.O :=
          geoCoq_firstPj_not_origin f bc wbc hbc (Or.inl hbcProj)
        have hwc : wc ≠ f.O :=
          geoCoq_firstPj_not_origin f c wc hc (Or.inl hcProj)
        have hWbJ : Col f.O wb f.J :=
          col_rotate (col_swap hWbAxis)
        have hWbwbc : Col f.O wb wbc :=
          hCol f.O f.J wb wbc f.O_ne_J hWbAxis hWbcAxis
        have hWbwc : Col f.O wb wc :=
          hCol f.O f.J wb wc f.O_ne_J hWbAxis hWcAxis
        have hbab : Col f.O b.1 ab.1 :=
          axis_col_of_colTrans f hCol b ab
        have hbbc : Col f.O b.1 bc.1 :=
          axis_col_of_colTrans f hCol b bc
        have hbabc : Col f.O b.1 abc.1 :=
          axis_col_of_colTrans f hCol b abc
        have hNoncol : ¬ Col f.O wb b.1 := by
          intro hOb
          have hOJb : Col f.O f.J b.1 :=
            hCol f.O wb f.J b.1 hwb.symm hWbJ hOb
          have hObJ : Col f.O b.1 f.J :=
            col_rotate (col_swap hOJb)
          exact (axis_not_col_aux_of_colTrans f hCol b hb) hObJ
        have hP1 : Parallel wb b.1 wbc bc.1 :=
          field_parallel_reverse_both
            (hParallelTrans b.1 wb f.I f.J bc.1 wbc
              (parallel_symm hbProj) hbcProj)
        have hP2 : Parallel wb ab.1 wbc abc.1 :=
          hParallelTrans wb ab.1 f.J a.1 wbc abc.1
            (parallel_symm hABFinal) hABCFinal
        have hP3 : Parallel b.1 f.J bc.1 wc :=
          field_parallel_reverse_both hBCFinal
        have hLast : Parallel f.J ab.1 wc abc.1 :=
          desargues_associates_product_projection
            f b ab bc abc wb wbc wc hDesargues hNoncol
            hwb.symm hwbc.symm f.O_ne_J hwc.symm
            hb.symm hbc.symm hab.symm habc.symm
            hWbJ hWbwbc hWbwc hbab hbbc hbabc hP1 hP2 hP3
        exact Or.inr ⟨hc, wc, hWcAxis, hcProj, hLast⟩

/-- Equality of the two association results in the nondegenerate case.
    Distinctness of intermediate products is explicit. It can later be
    obtained from the separate synthetic no-zero-product lemma. -/
theorem mul_assoc_nonzero_eq_of_desargues
    (f : Frame Point)
    (hTotal : MulTotal f)
    (hCol : ColTransitivityGoal (Point := Point))
    (hParallelTrans : ParallelTransitivityGoal (Point := Point))
    (hDesargues : AffineDesarguesFourPairs (Point := Point))
    (a b c ab bc lhs rhs : AxisPoint f)
    (ha : a.1 ≠ f.O) (hb : b.1 ≠ f.O) (hc : c.1 ≠ f.O)
    (hab : ab.1 ≠ f.O) (hbc : bc.1 ≠ f.O)
    (hrhs : rhs.1 ≠ f.O)
    (hAB : MulGraph f a b ab)
    (hBC : MulGraph f b c bc)
    (hLHS : MulGraph f ab c lhs)
    (hRHS : MulGraph f a bc rhs) :
    lhs = rhs := by
  have hRHS' : MulGraph f ab c rhs :=
    mulGraph_assoc_nonzero_of_desargues
      f hCol hParallelTrans hDesargues a b c ab bc rhs
      ha hb hc hab hbc hrhs hAB hBC hRHS
  obtain ⟨w, _, hunique⟩ := hTotal ab c
  exact (hunique lhs hLHS).trans (hunique rhs hRHS').symm

/-- Uniqueness of the zero-left product, given the geometric zero-left
    construction and total functionality of the existing `MulGraph`. -/
theorem mulGraph_zero_left_unique_of_total
    (f : Frame Point)
    (hTotal : MulTotal f)
    (hZeroLeft : ∀ t : AxisPoint f,
      MulGraph f (axisZero f) t (axisZero f))
    (t z : AxisPoint f)
    (hProd : MulGraph f (axisZero f) t z) :
    z = axisZero f := by
  obtain ⟨w, _, hunique⟩ := hTotal (axisZero f) t
  exact (hunique z hProd).trans
    (hunique (axisZero f) (hZeroLeft t)).symm

/-- Full associativity of the original relational multiplication, including
    all zero branches, *conditionally on explicitly named synthetic geometry
    goals*. In the three-nonzero case, the theorem above performs the genuine
    Desargues inference rather than assuming associativity. These hypotheses
    are independent obligations to be derived from `Plane` before this may be
    advertised as a Tarski proof of the field law. -/
theorem mulAssocLaw_of_desargues_and_geometry
    (f : Frame Point)
    (hTotal : MulTotal f)
    (hCol : ColTransitivityGoal (Point := Point))
    (hParallelTrans : ParallelTransitivityGoal (Point := Point))
    (hDesargues : AffineDesarguesFourPairs (Point := Point))
    (hZeroLeft : ∀ t : AxisPoint f,
      MulGraph f (axisZero f) t (axisZero f))
    (hProdNonzero : ∀ x y z : AxisPoint f,
      MulGraph f x y z →
      x.1 ≠ f.O → y.1 ≠ f.O → z.1 ≠ f.O) :
    MulAssocLaw f := by
  intro a b c ab bc lhs rhs hAB hABc hBC hAbc
  by_cases hc0 : c.1 = f.O
  · have hc : c = axisZero f := Subtype.ext hc0
    subst c
    have hL : lhs = axisZero f :=
      mul_zero_right_unique f ab lhs hABc
    have hBC0 : bc = axisZero f :=
      mul_zero_right_unique f b bc hBC
    subst bc
    have hR : rhs = axisZero f :=
      mul_zero_right_unique f a rhs hAbc
    exact hL.trans hR.symm
  · by_cases hb0 : b.1 = f.O
    · have hb : b = axisZero f := Subtype.ext hb0
      subst b
      have hAB0 : ab = axisZero f :=
        mul_zero_right_unique f a ab hAB
      subst ab
      have hL : lhs = axisZero f :=
        mulGraph_zero_left_unique_of_total f hTotal hZeroLeft c lhs hABc
      have hBC0 : bc = axisZero f :=
        mulGraph_zero_left_unique_of_total f hTotal hZeroLeft c bc hBC
      subst bc
      have hR : rhs = axisZero f :=
        mul_zero_right_unique f a rhs hAbc
      exact hL.trans hR.symm
    · by_cases ha0 : a.1 = f.O
      · have ha : a = axisZero f := Subtype.ext ha0
        subst a
        have hAB0 : ab = axisZero f :=
          mulGraph_zero_left_unique_of_total f hTotal hZeroLeft b ab hAB
        subst ab
        have hL : lhs = axisZero f :=
          mulGraph_zero_left_unique_of_total f hTotal hZeroLeft c lhs hABc
        have hR : rhs = axisZero f :=
          mulGraph_zero_left_unique_of_total f hTotal hZeroLeft bc rhs hAbc
        exact hL.trans hR.symm
      · have hab : ab.1 ≠ f.O :=
          hProdNonzero a b ab hAB ha0 hb0
        have hbc : bc.1 ≠ f.O :=
          hProdNonzero b c bc hBC hb0 hc0
        have hrhs : rhs.1 ≠ f.O :=
          hProdNonzero a bc rhs hAbc ha0 hbc
        exact mul_assoc_nonzero_eq_of_desargues f hTotal
          hCol hParallelTrans hDesargues a b c ab bc lhs rhs
          ha0 hb0 hc0 hab hbc hrhs hAB hBC hABc hAbc

/-- The original relational associativity target, reduced to the precise
    outstanding synthetic premises Desargues, Ch06 collinearity and parallel
    transitivity, and construction totality. Zero-product facts are derived
    directly from `MulGraph` rather than taken as additional hypotheses. -/
theorem mulAssocLaw_of_desargues
    (f : Frame Point)
    (hTotal : MulTotal f)
    (hCol : ColTransitivityGoal (Point := Point))
    (hParallelTrans : ParallelTransitivityGoal (Point := Point))
    (hDesargues : AffineDesarguesFourPairs (Point := Point)) :
    MulAssocLaw f := by
  exact mulAssocLaw_of_desargues_and_geometry f
    hTotal hCol hParallelTrans hDesargues
    (mulGraph_zero_left_of_total_and_colTrans f hTotal hCol)
    (mulGraph_output_nonzero_of_inputs_nonzero f hCol)

end TarskiField


/-! SOURCE: workstreams/Continuity.lean -/


/-!
  Geometric Horner sign evaluation: an A13 / real-closedness workstream.

  Intended use: install the consolidated parent as the Lean module
  `TarskiUnifiedRevised` (with the same TarskiField namespace), then compile.
  This file does not introduce new axioms, sorry, or external coordinates.

  The two equivalences below eliminate a missing interface: a *first-order*
  polynomial sign predicate and its *geometric relational* Horner evaluation.
  They deliberately require neither field laws nor a totality assumption.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Exact semantics of the positive-polynomial first-order formula. -/
theorem polynomialPositiveFormula_semantics {n : Nat}
    (o i j x : Fin n) (coefficients : List (Fin n))
    (ρ : Fin n → Point) :
    (polynomialPositiveFormula o i j x coefficients).eval ρ ↔
      Col (ρ o) (ρ i) (ρ x) ∧
      ∃ v : Point,
        (hornerExpr (.var x)
          (coefficients.map ScalarExpr.var)).geomValue
          (ρ o) (ρ i) (ρ j) ρ v ∧
        Out (ρ o) (ρ i) v := by
  simp [polynomialPositiveFormula, Formula.eval,
    scalarExprFormula_eval, colFormula_eval, outFormula_eval]

/-- `P(x) < 0` in Tarski's one-sorted syntax is exactly a geometrically
    computed Horner value on the negative side of the oriented scalar axis. -/
theorem polynomialNegativeFormula_horner_iff
    (f : Frame Point) {n : Nat}
    (o i j x : Fin n) (coefficients : List (Fin n))
    (ρ : Fin n → Point) (σ : Fin n → AxisPoint f)
    (hO : ρ o = f.O) (hI : ρ i = f.I) (hJ : ρ j = f.J)
    (hx : ρ x = (σ x).1)
    (hcoeff : ∀ c, c ∈ coefficients → ρ c = (σ c).1) :
    (polynomialNegativeFormula o i j x coefficients).eval ρ ↔
      ∃ v : AxisPoint f,
        HornerGraph f (σ x) (coefficients.map σ) v ∧
        v.1 ≠ f.O ∧ Bet v.1 f.O f.I := by
  rw [polynomialNegativeFormula_semantics]
  constructor
  · rintro ⟨_, V, hgeom, hVaxis, hVnonzero, hVneg⟩
    have hVaxis' : Col f.O f.I V := by
      simpa [hO, hI] using hVaxis
    let v : AxisPoint f := ⟨V, hVaxis'⟩
    have hgeom' :
        (hornerExpr (.var x)
          (coefficients.map ScalarExpr.var)).geomValue
            f.O f.I f.J ρ v.1 := by
      simpa [hO, hI, hJ] using hgeom
    have hhorner : HornerGraph f (σ x) (coefficients.map σ) v :=
      (hornerExpr_geomValue_of_agreement
        f ρ σ x hx coefficients hcoeff v).mp hgeom'
    refine ⟨v, hhorner, ?_, ?_⟩
    · simpa [v, hO] using hVnonzero
    · simpa [v, hO, hI] using hVneg
  · rintro ⟨v, hv, hvnonzero, hvneg⟩
    have hgeom :
        (hornerExpr (.var x)
          (coefficients.map ScalarExpr.var)).geomValue
            f.O f.I f.J ρ v.1 :=
      (hornerExpr_geomValue_of_agreement
        f ρ σ x hx coefficients hcoeff v).mpr hv
    refine ⟨?_, v.1, ?_, ?_, ?_, ?_⟩
    · simpa [hO, hI, hx] using (σ x).2
    · simpa [hO, hI, hJ] using hgeom
    · simpa [hO, hI] using v.2
    · simpa [hO] using hvnonzero
    · simpa [hO, hI] using hvneg

/-- The analogous positive-value bridge, again with no totality or field laws.
    Consequently, finite Tarski formulas for sign-conditions are *already*
    available before constructing the internal ordered-field operations. -/
theorem polynomialPositiveFormula_horner_iff
    (f : Frame Point) {n : Nat}
    (o i j x : Fin n) (coefficients : List (Fin n))
    (ρ : Fin n → Point) (σ : Fin n → AxisPoint f)
    (hO : ρ o = f.O) (hI : ρ i = f.I) (hJ : ρ j = f.J)
    (hx : ρ x = (σ x).1)
    (hcoeff : ∀ c, c ∈ coefficients → ρ c = (σ c).1) :
    (polynomialPositiveFormula o i j x coefficients).eval ρ ↔
      ∃ v : AxisPoint f,
        HornerGraph f (σ x) (coefficients.map σ) v ∧
        Positive f v := by
  rw [polynomialPositiveFormula_semantics]
  constructor
  · rintro ⟨_, V, hgeom, hVpos⟩
    have hVaxis : Col f.O f.I V := by
      have hcol : Out f.O f.I V := by
        simpa [hO, hI] using hVpos
      rcases hcol with ⟨_, _, hBet | hBet⟩
      · exact Or.inl hBet
      · exact Or.inr (Or.inl (bet_symm hBet))
    let v : AxisPoint f := ⟨V, hVaxis⟩
    have hgeom' :
        (hornerExpr (.var x)
          (coefficients.map ScalarExpr.var)).geomValue
            f.O f.I f.J ρ v.1 := by
      simpa [hO, hI, hJ] using hgeom
    refine ⟨v, (hornerExpr_geomValue_of_agreement
      f ρ σ x hx coefficients hcoeff v).mp hgeom', ?_⟩
    simpa [Positive, v, hO, hI] using hVpos
  · rintro ⟨v, hv, hvpos⟩
    have hgeom :
        (hornerExpr (.var x)
          (coefficients.map ScalarExpr.var)).geomValue
            f.O f.I f.J ρ v.1 :=
      (hornerExpr_geomValue_of_agreement
        f ρ σ x hx coefficients hcoeff v).mpr hv
    refine ⟨?_, v.1, ?_, ?_⟩
    · simpa [hO, hI, hx] using (σ x).2
    · simpa [hO, hI, hJ] using hgeom
    · simpa [Positive, hO, hI] using hvpos

/-- A first-order polynomial instance cannot be simultaneously positive and
    negative once the geometric addition and multiplication constructions
    have been shown single-valued. This is the sign-consistency theorem
    needed for the A13 cuts, expressed in Tarski's original language. -/
theorem polynomialSignFormulas_disjoint
    (f : Frame Point) {n : Nat}
    (o i j x : Fin n) (coefficients : List (Fin n))
    (ρ : Fin n → Point) (σ : Fin n → AxisPoint f)
    (hO : ρ o = f.O) (hI : ρ i = f.I) (hJ : ρ j = f.J)
    (hx : ρ x = (σ x).1)
    (hcoeff : ∀ c, c ∈ coefficients → ρ c = (σ c).1)
    (hAdd : AddFunctional f) (hMul : MulFunctional f) :
    ¬ ((polynomialPositiveFormula o i j x coefficients).eval ρ ∧
       (polynomialNegativeFormula o i j x coefficients).eval ρ) := by
  rintro ⟨hp, hn⟩
  obtain ⟨p, hpvalue, hpositive⟩ :=
    (polynomialPositiveFormula_horner_iff
      f o i j x coefficients ρ σ hO hI hJ hx hcoeff).mp hp
  obtain ⟨q, hqvalue, _, hnegative⟩ :=
    (polynomialNegativeFormula_horner_iff
      f o i j x coefficients ρ σ hO hI hJ hx hcoeff).mp hn
  exact (horner_signs_disjoint_of_functional
    f hAdd hMul (σ x) (coefficients.map σ))
      ⟨⟨p, hpvalue, hpositive⟩, ⟨q, hqvalue, hnegative⟩⟩

/-- Establishes the nonempty lower cut from an actual negative value of the
    geometrically evaluated polynomial at the left endpoint. The transfer
    through a two-binder environment is done via the proved Horner semantics,
    not by assuming that an arbitrary negative predicate is continuous. -/
theorem polynomialLowerCut_contains_left_of_negative
    (f : Frame Point) {n : Nat}
    (o i j l r : Fin n) (coefficients : List (Fin n))
    (params : Fin n → Point) (σ : Fin n → AxisPoint f)
    (hO : params o = f.O) (hI : params i = f.I)
    (hJ : params j = f.J) (hl : params l = (σ l).1)
    (hcoeff : ∀ c, c ∈ coefficients → params c = (σ c).1)
    (hleft : (polynomialNegativeFormula o i j l coefficients).eval params) :
    (polynomialLowerCutFormula o i j l r coefficients).eval
      (Fin.cons (params l) params) := by
  let coefficients2 : List (Fin (n + 2)) :=
    (coefficients.map Fin.succ).map Fin.succ
  let σ2 : Fin (n + 2) → AxisPoint f :=
    Fin.cons (σ l) (Fin.cons (axisZero f) σ)
  have hOld :
      ∃ v : AxisPoint f,
        HornerGraph f (σ l) (coefficients.map σ) v ∧
        v.1 ≠ f.O ∧ Bet v.1 f.O f.I :=
    (polynomialNegativeFormula_horner_iff
      f o i j l coefficients params σ
      hO hI hJ hl hcoeff).mp hleft
  have hleft2 :
      ∃ v : AxisPoint f,
        HornerGraph f (σ2 0) (coefficients2.map σ2) v ∧
        v.1 ≠ f.O ∧ Bet v.1 f.O f.I := by
    simpa [σ2, coefficients2, List.map_map, Function.comp_def] using hOld
  have hAxis : Col (params o) (params i) (params l) := by
    simpa [hO, hI, hl] using (σ l).2
  apply (polynomialLowerCutFormula_prefix_eval
    o i j l r coefficients params (params l)).mpr
  refine ⟨hAxis, bet_start (params l) (params r), ?_⟩
  intro T hT
  have hTeq : T = params l :=
    (between_identity (params l) T hT).symm
  subst T
  let ρ2 : Fin (n + 2) → Point :=
    Fin.cons (params l) (Fin.cons (params l) params)
  have hO2 : ρ2 o.succ.succ = f.O := by
    simpa [ρ2] using hO
  have hI2 : ρ2 i.succ.succ = f.I := by
    simpa [ρ2] using hI
  have hJ2 : ρ2 j.succ.succ = f.J := by
    simpa [ρ2] using hJ
  have hl2 : ρ2 0 = (σ2 0).1 := by
    simpa [ρ2, σ2] using hl
  have hcoeff2 : ∀ c, c ∈ coefficients2 →
      ρ2 c = (σ2 c).1 := by
    intro c hc
    change c ∈ (coefficients.map Fin.succ).map Fin.succ at hc
    rcases List.mem_map.mp hc with ⟨c1, hc1, rfl⟩
    rcases List.mem_map.mp hc1 with ⟨c0, hc0, rfl⟩
    simpa [ρ2, σ2] using hcoeff c0 hc0
  have hFormula :=
    (polynomialNegativeFormula_horner_iff
      f o.succ.succ i.succ.succ j.succ.succ 0
      coefficients2 ρ2 σ2 hO2 hI2 hJ2 hl2 hcoeff2).mpr hleft2
  simpa [ρ2, coefficients2] using hFormula

/-- Applying A13 to a genuinely negative left endpoint gives the unique
    least upper bound of the negative initial segment. No field structure is
    assumed on the underlying point type; the bridge uses the explicit
    first-order evaluation of a finite Horner graph. -/
theorem polynomial_cut_A13_of_left_negative
    [ContinuousPlane Point]
    (f : Frame Point) {n : Nat}
    (o i j l r : Fin n) (coefficients : List (Fin n))
    (params : Fin n → Point) (σ : Fin n → AxisPoint f)
    (hO : params o = f.O) (hI : params i = f.I)
    (hJ : params j = f.J) (hl : params l = (σ l).1)
    (hcoeff : ∀ c, c ∈ coefficients → params c = (σ c).1)
    (hleft : (polynomialNegativeFormula o i j l coefficients).eval params) :
    ∃! B : Point,
      Bet (params l) B (params r) ∧
      (upperBoundsFormula l
        (polynomialLowerCutFormula o i j l r coefficients)).eval
          (Fin.cons B params) ∧
      ∀ Y : Point,
        (upperBoundsFormula l
          (polynomialLowerCutFormula o i j l r coefficients)).eval
            (Fin.cons Y params) →
        Bet (params l) B Y := by
  apply polynomial_cut_A13_existsUnique
    o i j l r coefficients params
  exact polynomialLowerCut_contains_left_of_negative
    f o i j l r coefficients params σ hO hI hJ hl hcoeff hleft

/-- Internal form of the previous theorem: the A13 cut is an axis point.
    The only extra hypothesis is the geometric segment-collinearity theorem
    that the incidence workstream is proving directly from Tarski's axioms. -/
theorem polynomial_cut_A13_axis_of_left_negative
    [ContinuousPlane Point]
    (f : Frame Point) {n : Nat}
    (o i j l r : Fin n) (coefficients : List (Fin n))
    (params : Fin n → Point) (σ : Fin n → AxisPoint f)
    (hO : params o = f.O) (hI : params i = f.I)
    (hJ : params j = f.J) (hl : params l = (σ l).1)
    (hrAxis : Col f.O f.I (params r))
    (hclosed : AxisSegmentClosed f)
    (hcoeff : ∀ c, c ∈ coefficients → params c = (σ c).1)
    (hleft : (polynomialNegativeFormula o i j l coefficients).eval params) :
    ∃! b : AxisPoint f,
      Bet (params l) b.1 (params r) ∧
      (upperBoundsFormula l
        (polynomialLowerCutFormula o i j l r coefficients)).eval
          (Fin.cons b.1 params) ∧
      ∀ Y : Point,
        (upperBoundsFormula l
          (polynomialLowerCutFormula o i j l r coefficients)).eval
            (Fin.cons Y params) →
        Bet (params l) b.1 Y := by
  have hlAxis : Col f.O f.I (params l) := by
    simpa [hO, hI, hl] using (σ l).2
  apply polynomial_cut_A13_internal_scalar f
    o i j l r coefficients params hlAxis hrAxis hclosed
  exact polynomialLowerCut_contains_left_of_negative
    f o i j l r coefficients params σ hO hI hJ hl hcoeff hleft

/-- Evaluation of a negative-value formula survives the insertion of the
    two bound variables used to express the initial prefix. The middle
    parameter `X` is *arbitrary* and hence cannot alter a polynomial value. -/
theorem polynomialNegativeFormula_two_binder_iff
    (f : Frame Point) {n : Nat}
    (o i j x : Fin n) (coefficients : List (Fin n))
    (params : Fin n → Point) (σ : Fin n → AxisPoint f)
    (X : Point)
    (hO : params o = f.O) (hI : params i = f.I)
    (hJ : params j = f.J) (hx : params x = (σ x).1)
    (hcoeff : ∀ c, c ∈ coefficients → params c = (σ c).1) :
    (polynomialNegativeFormula
      o.succ.succ i.succ.succ j.succ.succ 0
      ((coefficients.map Fin.succ).map Fin.succ)).eval
        (Fin.cons (params x) (Fin.cons X params)) ↔
    (polynomialNegativeFormula o i j x coefficients).eval params := by
  let coeff2 : List (Fin (n + 2)) :=
    (coefficients.map Fin.succ).map Fin.succ
  let ρ2 : Fin (n + 2) → Point :=
    Fin.cons (params x) (Fin.cons X params)
  let σ2 : Fin (n + 2) → AxisPoint f :=
    Fin.cons (σ x) (Fin.cons (axisZero f) σ)
  have hO2 : ρ2 o.succ.succ = f.O := by
    simpa [ρ2] using hO
  have hI2 : ρ2 i.succ.succ = f.I := by
    simpa [ρ2] using hI
  have hJ2 : ρ2 j.succ.succ = f.J := by
    simpa [ρ2] using hJ
  have hx2 : ρ2 0 = (σ2 0).1 := by
    simpa [ρ2, σ2] using hx
  have hcoeff2 : ∀ c, c ∈ coeff2 → ρ2 c = (σ2 c).1 := by
    intro c hc
    change c ∈ (coefficients.map Fin.succ).map Fin.succ at hc
    rcases List.mem_map.mp hc with ⟨c1, hc1, rfl⟩
    rcases List.mem_map.mp hc1 with ⟨c0, hc0, rfl⟩
    simpa [ρ2, σ2] using hcoeff c0 hc0
  have hShift :=
    polynomialNegativeFormula_horner_iff
      f o.succ.succ i.succ.succ j.succ.succ 0
      coeff2 ρ2 σ2 hO2 hI2 hJ2 hx2 hcoeff2
  have hBase :=
    polynomialNegativeFormula_horner_iff
      f o i j x coefficients params σ hO hI hJ hx hcoeff
  have hBridge :
      (∃ v : AxisPoint f,
        HornerGraph f (σ2 0) (coeff2.map σ2) v ∧
        v.1 ≠ f.O ∧ Bet v.1 f.O f.I) ↔
      (∃ v : AxisPoint f,
        HornerGraph f (σ x) (coefficients.map σ) v ∧
        v.1 ≠ f.O ∧ Bet v.1 f.O f.I) := by
    simp [σ2, coeff2, List.map_map, Function.comp_def]
  simpa [ρ2, coeff2] using hShift.trans (hBridge.trans hBase.symm)

/-- The right endpoint of a negative-prefix cut is excluded if the
    polynomial there is positive. This is an internal geometric fact and
    requires only uniqueness of the two parallel-line arithmetic graphs. -/
theorem polynomialUpperCut_contains_right_of_positive
    (f : Frame Point) {n : Nat}
    (o i j l r : Fin n) (coefficients : List (Fin n))
    (params : Fin n → Point) (σ : Fin n → AxisPoint f)
    (hO : params o = f.O) (hI : params i = f.I)
    (hJ : params j = f.J) (hr : params r = (σ r).1)
    (hcoeff : ∀ c, c ∈ coefficients → params c = (σ c).1)
    (hAdd : AddFunctional f) (hMul : MulFunctional f)
    (hRightPositive :
      (polynomialPositiveFormula o i j r coefficients).eval params) :
    (polynomialUpperCutFormula o i j l r coefficients).eval
      (Fin.cons (params r) params) := by
  have hrAxis : Col (params o) (params i) (params r) := by
    simpa [hO, hI, hr] using (σ r).2
  change Col (params o) (params i) (params r) ∧
    Bet (params l) (params r) (params r) ∧
    ¬ (polynomialLowerCutFormula o i j l r coefficients).eval
        (Fin.cons (params r) params)
  refine ⟨hrAxis, bet_end (params l) (params r), ?_⟩
  intro hRlower
  have hRnegativeShift :
      (polynomialNegativeFormula
        o.succ.succ i.succ.succ j.succ.succ 0
        ((coefficients.map Fin.succ).map Fin.succ)).eval
          (Fin.cons (params r) (Fin.cons (params r) params)) :=
    ((polynomialLowerCutFormula_prefix_eval
      o i j l r coefficients params (params r)).mp hRlower).2.2
        (params r) (bet_end (params l) (params r))
  have hRnegative :
      (polynomialNegativeFormula o i j r coefficients).eval params :=
    (polynomialNegativeFormula_two_binder_iff
      f o i j r coefficients params σ (params r)
      hO hI hJ hr hcoeff).mp hRnegativeShift
  exact (polynomialSignFormulas_disjoint
    f o i j r coefficients params σ
    hO hI hJ hr hcoeff hAdd hMul)
      ⟨hRightPositive, hRnegative⟩

/-!
### Directed betweenness and the internal scalar order

The oriented order `AxisLt` is defined in the original source using a
*positive geometric addition difference*. In contrast, Tarski's primitive
`Bet L B R` is unoriented: it also holds when the endpoints are interchanged.
The least-upper-bound argument must therefore record the orientation
`AxisLt f l r` and a theorem that connects positive geometric differences
to intermediate points. That connection is not one of `Plane`'s axioms;
it is a pending synthetic theorem about the previously defined `AddGraph`.
-/

/-- The non-strict order induced by the existing oriented `AxisLt` graph. -/
def AxisLe (f : Frame Point) (x y : AxisPoint f) : Prop :=
  x = y ∨ AxisLt f x y

theorem axisLe_refl (f : Frame Point) (x : AxisPoint f) :
    AxisLe f x x := Or.inl rfl

theorem axisLe_of_axisLt (f : Frame Point) {x y : AxisPoint f}
    (hxy : AxisLt f x y) : AxisLe f x y :=
  Or.inr hxy

/-- The *precise* geometric order-compatibility lemma still needed from
Tarski incidence and the synthetic parallel-line addition construction.
It is defined as a proposition, **not assumed as a new Plane axiom**. -/
def AxisDirectedBetOrder (f : Frame Point) : Prop :=
  ∀ a b c : AxisPoint f,
    AxisLt f a c → Bet a.1 b.1 c.1 →
      AxisLe f a b ∧ AxisLe f b c

/-- A13's betweenness interval becomes an interval in the *internally
defined* scalar order, provided the indicated directed-betweenness lemma
has been independently derived from Tarski geometry. The use of `AxisLt`
is essential: without an orientation of LR, `Bet L b R` also describes
the opposite (decreasing) order. -/
theorem polynomial_cut_A13_internal_order_of_left_negative
    [ContinuousPlane Point]
    (f : Frame Point) {n : Nat}
    (o i j l r : Fin n) (coefficients : List (Fin n))
    (params : Fin n → Point) (σ : Fin n → AxisPoint f)
    (hO : params o = f.O) (hI : params i = f.I)
    (hJ : params j = f.J)
    (hl : params l = (σ l).1) (hr : params r = (σ r).1)
    (hclosed : AxisSegmentClosed f)
    (horder : AxisDirectedBetOrder f)
    (hLR : AxisLt f (σ l) (σ r))
    (hcoeff : ∀ c, c ∈ coefficients → params c = (σ c).1)
    (hleft : (polynomialNegativeFormula o i j l coefficients).eval params) :
    ∃! b : AxisPoint f,
      Bet (params l) b.1 (params r) ∧
      AxisLe f (σ l) b ∧ AxisLe f b (σ r) ∧
      (upperBoundsFormula l
        (polynomialLowerCutFormula o i j l r coefficients)).eval
          (Fin.cons b.1 params) ∧
      ∀ Y : Point,
        (upperBoundsFormula l
          (polynomialLowerCutFormula o i j l r coefficients)).eval
            (Fin.cons Y params) →
        Bet (params l) b.1 Y := by
  have hrAxis : Col f.O f.I (params r) := by
    simpa [hr] using (σ r).2
  obtain ⟨b, ⟨hb, hbupper, hbleast⟩, hunique⟩ :=
    polynomial_cut_A13_axis_of_left_negative
      f o i j l r coefficients params σ
      hO hI hJ hl hrAxis hclosed hcoeff hleft
  have hbDirected : Bet (σ l).1 b.1 (σ r).1 := by
    simpa [hl, hr] using hb
  obtain ⟨hleftB, hrightB⟩ := horder (σ l) b (σ r) hLR hbDirected
  refine ⟨b, ⟨hb, hleftB, hrightB, hbupper, hbleast⟩, ?_⟩
  intro b' hb'
  apply hunique
  exact ⟨hb'.1, hb'.2.2.2.1, hb'.2.2.2.2⟩

end TarskiField

namespace TarskiField

/-!
### The order-theoretic core of the A13 root argument

This section states a theorem about *any* linearly ordered scalar structure.
It is not a plane axiom, not an invocation of the real numbers, and not a
claim that the synthetic scalar axis has already been proved a field.

The intended instantiation is the internal scalar axis once the addition,
multiplication, order, and polynomial-sign continuity constructions have
been established from Tarski's primitives. The earlier theorems of this
file produce the definable prefix and its A13 least upper bound.

The two local hypotheses below are the precise inputs still required from
the polynomial sign-stability argument:

* If `p b > 0`, a positive value occurs strictly to the *left* of `b`.
* If `p b < 0`, `p` stays negative on an interval immediately to the *right*
  of `b`.

For an internal ordered field, both follow from continuity of the finite
polynomial, order density, and opposite signs at the endpoints. Their
derivation must use the field proven from the plane, not an imported real
coordinate model.
-/

section AbstractCutRoot

variable {F : Type*} [LinearOrder F] [Zero F]

/-- The abstract order semantics of the geometrically defined initial
negative polynomial segment. The parameter `p` is intended to be the
unique value of the internal geometric Horner evaluation. -/
def OrderedNegativePrefix (p : F → F) (L R x : F) : Prop :=
  L ≤ x ∧ x ≤ R ∧ ∀ t : F, L ≤ t → t ≤ x → p t < 0

/-- Once A13 supplies the *least upper bound* of the negative prefix,
local persistence of strict signs forces the boundary value to be zero.

No completeness, Archimedean axiom, field law, order density, or external
`ℝ` is assumed in this lemma: the exact local-sign obligations are made
explicit, pending their eventual proof for the internally interpreted
polynomial. This is the substantive cut-boundary argument, not an A13
invocation with the desired zero-value conclusion as an assumption. -/
theorem ordered_negative_prefix_cut_value_zero
    (p : F → F) (L R b : F)
    (hsegment : L ≤ b ∧ b ≤ R)
    (hbound : ∀ x : F, OrderedNegativePrefix p L R x → x ≤ b)
    (hleast : ∀ y : F,
      (∀ x : F, OrderedNegativePrefix p L R x → x ≤ y) → b ≤ y)
    (hpositive_left : 0 < p b →
      ∃ y : F, L ≤ y ∧ y < b ∧ 0 < p y)
    (hnegative_right : p b < 0 →
      ∃ z : F, b < z ∧ z ≤ R ∧
        ∀ t : F, b ≤ t → t ≤ z → p t < 0) :
    p b = 0 := by
  rcases lt_trichotomy (p b) 0 with hneg | hzero | hpos
  · obtain ⟨z, hbz, hzR, hzneg⟩ := hnegative_right hneg
    have hbefore : ∀ t : F, L ≤ t → t < b → p t < 0 := by
      intro t hLt htb
      by_contra hnonneg
      have hnotbound : ¬ (∀ x : F,
          OrderedNegativePrefix p L R x → x ≤ t) := by
        intro htbound
        exact (not_le_of_gt htb) (hleast t htbound)
      push Not at hnotbound
      obtain ⟨x, hx, htx⟩ := hnotbound
      exact hnonneg (hx.2.2 t hLt (le_of_lt htx))
    have hzprefix : OrderedNegativePrefix p L R z := by
      refine ⟨le_trans hsegment.1 (le_of_lt hbz), hzR, ?_⟩
      intro t hLt htz
      rcases lt_or_ge t b with htb | hbt
      · exact hbefore t hLt htb
      · exact hzneg t hbt htz
    exact False.elim ((not_le_of_gt hbz) (hbound z hzprefix))
  · exact hzero
  · obtain ⟨y, hLy, hyb, hypos⟩ := hpositive_left hpos
    have hybound : ∀ x : F, OrderedNegativePrefix p L R x → x ≤ y := by
      intro x hx
      by_contra hxy
      have hyx : y < x := lt_of_not_ge hxy
      have hyneg : p y < 0 := hx.2.2 y hLy (le_of_lt hyx)
      exact (not_lt_of_ge (le_of_lt hypos)) hyneg
    exact False.elim ((not_le_of_gt hyb) (hleast y hybound))

end AbstractCutRoot

/-!
The next two lemmas isolate the elementary *order-topological* consequence
of continuity used in the preceding cut argument. They require no scalar
addition or multiplication and make no reference to a real-coordinate
plane. The internal axis will supply these order/topology instances only
after the corresponding geometric construction has been proved.
-/

section AbstractLocalSigns

variable {F : Type*} [LinearOrder F] [Zero F]
variable [TopologicalSpace F] [OrderTopology F]
variable [NoMinOrder F] [NoMaxOrder F] [DenselyOrdered F]

theorem positive_on_some_left_neighbour
    (p : F → F) (hp : Continuous p) {L b : F}
    (hLb : L < b) (hpositive : 0 < p b) :
    ∃ y : F, L ≤ y ∧ y < b ∧ 0 < p y := by
  have hopen : IsOpen {t : F | 0 < p t} :=
    isOpen_Ioi.preimage hp
  have hnhds : {t : F | 0 < p t} ∈ nhds b :=
    hopen.mem_nhds hpositive
  obtain ⟨a, c, ⟨hab, hbc⟩, hsub⟩ :=
    (mem_nhds_iff_exists_Ioo_subset).mp hnhds
  have hstart : max a L < b := max_lt hab hLb
  obtain ⟨y, hyabove, hybelow⟩ := exists_between hstart
  refine ⟨y, le_trans (le_max_right a L) (le_of_lt hyabove), hybelow, ?_⟩
  exact hsub ⟨lt_of_le_of_lt (le_max_left a L) hyabove,
    lt_trans hybelow hbc⟩

theorem negative_on_some_right_neighbour
    (p : F → F) (hp : Continuous p) {b R : F}
    (hbR : b < R) (hnegative : p b < 0) :
    ∃ z : F, b < z ∧ z ≤ R ∧
      ∀ t : F, b ≤ t → t ≤ z → p t < 0 := by
  have hopen : IsOpen {t : F | p t < 0} :=
    isOpen_Iio.preimage hp
  have hnhds : {t : F | p t < 0} ∈ nhds b :=
    hopen.mem_nhds hnegative
  obtain ⟨a, c, ⟨hab, hbc⟩, hsub⟩ :=
    (mem_nhds_iff_exists_Ioo_subset).mp hnhds
  have hend : b < min c R := lt_min hbc hbR
  obtain ⟨z, hzabove, hzbelow⟩ := exists_between hend
  refine ⟨z, hzabove,
    le_of_lt (lt_of_lt_of_le hzbelow (min_le_right c R)), ?_⟩
  intro t hbt htz
  exact hsub ⟨lt_of_lt_of_le hab hbt,
    lt_of_le_of_lt htz (lt_of_lt_of_le hzbelow (min_le_left c R))⟩

/-- A continuous function with opposite signs at the endpoints vanishes at
the A13 least-upper-bound cut point. The order completeness needed to obtain
that cut point is not postulated here: `hbound` and `hleast` are the exact
facts that the one-sorted Tarski A13 construction is intended to supply.
This statement assumes neither the real numbers nor a second field sort. -/
theorem continuous_negative_prefix_cut_root
    (p : F → F) (hp : Continuous p)
    (L R b : F)
    (hnegativeL : p L < 0) (hpositiveR : 0 < p R)
    (hsegment : L ≤ b ∧ b ≤ R)
    (hbound : ∀ x : F, OrderedNegativePrefix p L R x → x ≤ b)
    (hleast : ∀ y : F,
      (∀ x : F, OrderedNegativePrefix p L R x → x ≤ y) → b ≤ y) :
    p b = 0 := by
  apply ordered_negative_prefix_cut_value_zero p L R b
    hsegment hbound hleast
  · intro hbpositive
    have hLb : L < b := by
      by_contra hnot
      have hbL : b ≤ L := le_of_not_gt hnot
      have heq : L = b := le_antisymm hsegment.1 hbL
      rw [heq] at hnegativeL
      exact (lt_asymm hnegativeL hbpositive)
    exact positive_on_some_left_neighbour p hp hLb hbpositive
  · intro hbnegative
    have hbR : b < R := by
      by_contra hnot
      have hRb : R ≤ b := le_of_not_gt hnot
      have heq : b = R := le_antisymm hsegment.2 hRb
      rw [heq] at hbnegative
      exact (lt_asymm hbnegative hpositiveR)
    exact negative_on_some_right_neighbour p hp hbR hbnegative

end AbstractLocalSigns

/-!
### Polynomial specialization of the A13 boundary argument

`F` here is a *generic* ordered field variable, not `ℝ` and not an additional
sort or axiom of `Plane`. The point of this reusable theorem is that after
the other workstreams derive the ordered-field operations on `AxisPoint f`,
their interpreted polynomial can use the same argument without an imported
Euclidean-coordinate model. All assumptions are exposed in the signature.
-/

section AbstractPolynomialCut

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable [TopologicalSpace F] [OrderTopology F] [IsTopologicalSemiring F]

theorem polynomial_root_at_A13_cut
    (p : Polynomial F) (L R b : F)
    (hnegativeL : p.eval L < 0) (hpositiveR : 0 < p.eval R)
    (hsegment : L ≤ b ∧ b ≤ R)
    (hbound : ∀ x : F,
      OrderedNegativePrefix (fun t => p.eval t) L R x → x ≤ b)
    (hleast : ∀ y : F,
      (∀ x : F,
        OrderedNegativePrefix (fun t => p.eval t) L R x → x ≤ y) → b ≤ y) :
    p.eval b = 0 := by
  exact continuous_negative_prefix_cut_root
    (fun t : F => p.eval t) (Polynomial.continuous p)
    L R b hnegativeL hpositiveR hsegment hbound hleast

end AbstractPolynomialCut

end TarskiField


/-! SOURCE: workstreams/PolynomialLocalSigns.lean -/


/-!
  Abstract algebraic fact to instantiate on Tarski's *interpreted* scalar axis
  once the scalar operations and order topology have been constructed.

  These theorems hold in every ordered topological semiring; `ℝ`, a Euclidean
  coordinate plane, and geometric circle theorems are not used.

  They provide the sign-stability input needed to prove that an A13 least
  upper bound of the negative polynomial prefix must be a zero of p.
-/

namespace TarskiField

variable {F : Type*}
variable [CommSemiring F] [LinearOrder F] [TopologicalSpace F]
variable [IsTopologicalSemiring F] [OrderTopology F]

/-- The negative locus of a polynomial is open in any ordered topological
    semiring; this is just the continuity of *finite ring operations*. -/
theorem polynomial_negative_locus_open (p : Polynomial F) :
    IsOpen {x : F | p.eval x < 0} := by
  exact isOpen_Iio.preimage (Polynomial.continuous p)

/-- The positive locus is open for the same entirely finite reason. -/
theorem polynomial_positive_locus_open (p : Polynomial F) :
    IsOpen {x : F | 0 < p.eval x} := by
  exact isOpen_Ioi.preimage (Polynomial.continuous p)

/-- A strictly negative value remains negative in a neighborhood. -/
theorem polynomial_negative_eventually (p : Polynomial F) (b : F)
    (hb : p.eval b < 0) :
    ∀ᶠ x in nhds b, p.eval x < 0 :=
  (polynomial_negative_locus_open p).mem_nhds hb

/-- A strictly positive value remains positive in a neighborhood. -/
theorem polynomial_positive_eventually (p : Polynomial F) (b : F)
    (hb : 0 < p.eval b) :
    ∀ᶠ x in nhds b, 0 < p.eval x :=
  (polynomial_positive_locus_open p).mem_nhds hb

end TarskiField


/-! SOURCE: workstreams/Assembly.lean -/


/-!
  Cross-workstream assembly theorems. All geometric dependencies remain
  explicit and are intended to be discharged using `Plane` alone.
  Neither axiom declarations nor outside coordinate models occur here.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]

/-- Two different lines through O can have no second common point once
    the neutral theorem of uniqueness of a line through two points is known.
    The line-uniqueness hypothesis is a pending theorem of Tarski's axioms. -/
theorem axes_meet_only_at_origin_of_line_uniqueness
    (hline_two_points : ∀ A B C D : Point,
      A ≠ B → C ≠ D →
      Col A B C → Col A B D →
      ∀ S : Point, Col A B S ↔ Col C D S)
    (f : Frame Point) (W : Point)
    (hOI : Col f.O f.I W) (hOJ : Col f.O f.J W) :
    W = f.O := by
  by_contra hW
  have hOIline : ∀ S : Point,
      Col f.O f.I S ↔ Col f.O W S :=
    hline_two_points f.O f.I f.O W f.O_ne_I
      (Ne.symm hW) (col_left f.O f.I) hOI
  have hOJline : ∀ S : Point,
      Col f.O f.J S ↔ Col f.O W S :=
    hline_two_points f.O f.J f.O W f.O_ne_J
      (Ne.symm hW) (col_left f.O f.J) hOJ
  have hJOW : Col f.O W f.J :=
    (hOJline f.J).mp (col_right f.O f.J)
  exact f.noncol ((hOIline f.J).mpr hJOW)

/-- Completing the nonzero branch of the GeoCoq multiplication bridge now
    needs only neutral line uniqueness, not a separate axes-intersection
    geometric assumption or a field operation. -/
theorem geoCoqProd_nonzero_implies_mulGraph_of_line_uniqueness
    (hline_two_points : ∀ A B C D : Point,
      A ≠ B → C ≠ D →
      Col A B C → Col A B D →
      ∀ S : Point, Col A B S ↔ Col C D S)
    (f : Frame Point) (x y z : AxisPoint f)
    (hy : y.1 ≠ f.O)
    (hProd : GeoCoqProd f x y z) :
    MulGraph f x y z := by
  apply geoCoqProd_nonzero_implies_mulGraph_of_axis_intersection
    f x y z
    (axes_meet_only_at_origin_of_line_uniqueness hline_two_points f)
    hy hProd

/-!
The two totality arguments are now assembled over the SAME geometric
premises. This is a genuine reduction of the remaining synthetic workload:
neither multiplication nor addition asks for an independent, unproved
existence axiom for its own coordinate projections.
-/

/-- Both geometrically defined operations are total once three general
incidence/parallel theorems have been derived from Tarski's primitive axioms.
No arithmetic structure is assumed on `Point` or the scalar axis. -/
theorem both_operation_graphs_total_of_synthetic_geometry
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ W : Point, Parallel A B P W)
    (hplayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ S : Point, Col C D S ↔ Col E F S)
    (hline_two_points : ∀ A B C D : Point,
      A ≠ B → C ≠ D →
      Col A B C → Col A B D →
      ∀ S : Point, Col A B S ↔ Col C D S)
    (f : Frame Point) : AddTotal f ∧ MulTotal f := by
  have hparallel_trans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F := by
    intro A B C D E F hAB hCD
    exact parallel_trans_of_playfair hplayfair hAB hCD
  have hcol_line_eq : ∀ {A B C : Point},
      A ≠ B → Col A B C → C ≠ A →
      ∀ T : Point, Col A B T ↔ Col A C T := by
    intro A B C hAB hABC hCA
    exact hline_two_points A B A C hAB hCA.symm
      (col_left A B) hABC
  exact ⟨
    addTotal_of_parallel_existence_playfair_incidence
      hparallel_through hplayfair hline_two_points f,
    mulTotal_of_geometry
      hparallel_through hparallel_trans hplayfair hcol_line_eq f⟩

/-- The same three geometric obligations also give functional addition
and multiplication, the first nontrivial input for internal field laws. -/
theorem both_operation_graphs_functional_of_synthetic_geometry
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ W : Point, Parallel A B P W)
    (hplayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ S : Point, Col C D S ↔ Col E F S)
    (hline_two_points : ∀ A B C D : Point,
      A ≠ B → C ≠ D →
      Col A B C → Col A B D →
      ∀ S : Point, Col A B S ↔ Col C D S)
    (f : Frame Point) : AddFunctional f ∧ MulFunctional f := by
  obtain ⟨hadd, hmul⟩ :=
    both_operation_graphs_total_of_synthetic_geometry
      hparallel_through hplayfair hline_two_points f
  exact ⟨addFunctional_of_total f hadd, mulFunctional_of_total f hmul⟩

/-!
The neutral line-extensionality hypothesis has now been discharged *without*
any new axiom: `col_line_extensionality_tarski` is checked using Tarski's
segment construction, five-segment axiom and Pasch. Consequently only
parallel existence and Playfair remain as additional proof obligations for
the simultaneous arithmetic-graph construction.
-/

/-- The full segment-closure property holds in the primitive Tarski plane,
including the degenerate-line case O=I. -/
theorem colSegmentClosed_from_tarski : ColSegmentClosed (Point := Point) := by
  intro O I X B Y hX hY hBet
  by_cases hOI : O = I
  · subst I
    exact Or.inl (bet_start O B)
  · exact col_segment_closed_tarski hOI hX hY hBet

/-- The two coordinate arithmetic graphs need only *two* remaining
parallel-geometry theorems. Neutral incidence is now an unconditional
consequence of `Plane`, via `col_line_extensionality_tarski`. -/
theorem both_operation_graphs_total_of_parallel_theorems
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ W : Point, Parallel A B P W)
    (hplayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ S : Point, Col C D S ↔ Col E F S)
    (f : Frame Point) : AddTotal f ∧ MulTotal f := by
  apply both_operation_graphs_total_of_synthetic_geometry
    hparallel_through hplayfair
  intro A B C D hAB hCD hC hD S
  exact col_line_extensionality_tarski hAB hCD hC hD S

/-- Graph functionality follows from exactly the same two parallel theorems,
with no independent line-extensionality assumption. -/
theorem both_operation_graphs_functional_of_parallel_theorems
    (hparallel_through : ∀ A B P : Point,
      A ≠ B → ∃ W : Point, Parallel A B P W)
    (hplayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ S : Point, Col C D S ↔ Col E F S)
    (f : Frame Point) : AddFunctional f ∧ MulFunctional f := by
  obtain ⟨hadd, hmul⟩ :=
    both_operation_graphs_total_of_parallel_theorems
      hparallel_through hplayfair f
  exact ⟨addFunctional_of_total f hadd, mulFunctional_of_total f hmul⟩

/-- Midpoint existence supplies the missing *existence* half of the
parallel-line construction, without postulating any parallel operation.
The midpoint itself must still be constructed from `Plane`. -/
theorem parallel_through_of_midpoint_existence_tarski
    (hmid : ∀ A P : Point, ∃ M : Point, MulMidpoint M A P) :
    ∀ A B P : Point, A ≠ B → ∃ Q : Point, Parallel A B P Q := by
  intro A B P hAB
  by_cases hP : Col A B P
  · exact parallel_through_point_on_line_tarski hAB hP
  · obtain ⟨M, hM⟩ := hmid A P
    exact parallel_through_off_line_of_midpoint_tarski hAB hP hM

/-- A direct integration point for the synthetic midpoint and Playfair
workstreams: once both geometric theorems are proved, the two internal
arithmetic relations are total and functional. -/
theorem both_operation_graphs_of_midpoint_and_playfair_tarski
    (hmid : ∀ A P : Point, ∃ M : Point, MulMidpoint M A P)
    (hplayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ S : Point, Col C D S ↔ Col E F S)
    (f : Frame Point) :
    (AddTotal f ∧ MulTotal f) ∧
      (AddFunctional f ∧ MulFunctional f) := by
  have hparallel := parallel_through_of_midpoint_existence_tarski hmid
  exact ⟨both_operation_graphs_total_of_parallel_theorems
      hparallel hplayfair f,
    both_operation_graphs_functional_of_parallel_theorems
      hparallel hplayfair f⟩

open Plane

/-- The initial orthogonality configuration of Gupta's construction for
GeoCoq Ch08 l8_18. Both right angles are derived from the primitive
congruence and betweenness structure, not introduced as hypotheses. -/
theorem gupta_l8_18_orthogonal_seed_tarski
    {A B C : Point} (hNoncol : ¬ Col A B C) :
    ∃ Y P Z Q Q' C' X : Point,
      Bet B A Y ∧ Cong A Y A C ∧
      MulMidpoint P C Y ∧
      Bet A Y Z ∧ Cong Y Z Y P ∧
      Bet P Y Q ∧ Cong Y Q Y A ∧
      MulMidpoint Z Q Q' ∧
      Bet Q' Y C' ∧ Cong Y C' Y C ∧
      MulMidpoint X C C' ∧
      Cong Z Q P A ∧
      TarskiPer A P Y ∧ TarskiPer Q Z Y := by
  obtain ⟨Y, hBAY, hAYAC⟩ :=
    segment_construction B A A C
  obtain ⟨P, hPCY⟩ :=
    midpoint_exists_of_equidistant_station_tarski
      (A := C) (B := Y) (C := A) (cong_symm hAYAC)
  obtain ⟨Z, hAYZ, hYZYP⟩ :=
    segment_construction A Y Y P
  obtain ⟨Q, hPYQ, hYQYA⟩ :=
    segment_construction P Y Y A
  obtain ⟨Q', hQZQ', hZQ'QZ⟩ :=
    segment_construction Q Z Q Z
  have hZmid : MulMidpoint Z Q Q' :=
    ⟨hQZQ', cong_reverse_left (cong_symm hZQ'QZ)⟩
  obtain ⟨C', hQ'YC', hYC'YC⟩ :=
    segment_construction Q' Y Y C
  obtain ⟨X, hXCC'⟩ :=
    midpoint_exists_of_equidistant_station_tarski
      (A := C) (B := C') (C := Y) (cong_symm hYC'YC)
  have hAY : A ≠ Y := by
    intro h
    subst Y
    exact (noncol_ne_first_third hNoncol)
      (cong_identity A C A (cong_symm hAYAC))
  have hAY_QY : Cong A Y Q Y :=
    cong_symm (cong_reverse_both hYQYA)
  have hZQ_PA : Cong Z Q P A :=
    five_segment A Q Y Y Z P Q A
      hAY_QY hYZYP
      (cong_pseudo_reflexivity A Q) hYQYA
      hAYZ (bet_symm hPYQ) hAY
  have hPerAPY : TarskiPer A P Y :=
    ⟨C, mul_midpoint_reverse hPCY, hAYAC⟩
  have hAP_QZ : Cong A P Q Z :=
    cong_symm (cong_reverse_both hZQ_PA)
  have hPY_ZY : Cong P Y Z Y :=
    cong_symm (cong_reverse_both hYZYP)
  have hPerQZY : TarskiPer Q Z Y :=
    tarski_per_of_three_segment_congruences_tarski
      hPerAPY hAP_QZ hPY_ZY hAY_QY
  exact ⟨Y, P, Z, Q, Q', C', X,
    hBAY, hAYAC, hPCY,
    hAYZ, hYZYP, hPYQ, hYQYA, hZmid,
    hQ'YC', hYC'YC, hXCC', hZQ_PA,
    hPerAPY, hPerQZY⟩

/-- A right angle identifies its defining reflection with any other
reflection of the same endpoint across the same center. -/
theorem tarski_per_cong_of_reflection_tarski
    {A B C D : Point}
    (hPer : TarskiPer A B C)
    (hMid : MulMidpoint B C D) :
    Cong A C A D := by
  obtain ⟨D', hD', hCong⟩ := hPer
  obtain ⟨E, _, huniq⟩ := mul_reflection_exists_unique B C
  have heq : D' = D :=
    (huniq D' hD').trans (huniq D hMid).symm
  simpa [heq] using hCong

/-- The specific Krippen inputs required by Gupta's perpendicular-foot
construction follow from the already constructed two right angles. -/
theorem gupta_krippen_input_tarski
    {P C Y Q Q' Z C' : Point}
    (hMidPCY : MulMidpoint P C Y)
    (hPYQ : Bet P Y Q)
    (hZmid : MulMidpoint Z Q Q')
    (hPerQZY : TarskiPer Q Z Y)
    (hYC'YC : Cong Y C' Y C) :
    Bet Q Y C ∧ Cong Y Q Y Q' ∧ Cong Y C Y C' := by
  have hQYC : Bet Q Y C :=
    by
      by_cases hPY : P = Y
      · subst P
        have hYC : Y = C :=
          cong_identity Y C Y (by simpa using hMidPCY.2)
        subst C
        exact bet_end Q Y
      · exact bet_symm (bet_outer_trans hMidPCY.1 hPYQ hPY)
  have hYQYQ' : Cong Y Q Y Q' :=
    tarski_per_cong_of_reflection_tarski
      (tarski_per_swap_legs_tarski hPerQZY) hZmid
  exact ⟨hQYC, hYQYQ', cong_symm hYC'YC⟩

/-- A genuine Tarski-language order-transport lemma: the two rays from C
have corresponding points at equal distances, and betweenness along the
first ray transfers to betweenness along the second. -/
theorem congruent_rays_preserve_bet_tarski
    {C A1 B1 B2 U V : Point}
    (hB2ne : B2 ≠ C)
    (hB1CB2 : Bet B1 C B2)
    (hB2CV : Bet B2 C V)
    (hCA1_CB1 : Cong C A1 C B1)
    (hCU_CV : Cong C U C V)
    (hCA1U : Bet C A1 U) :
    Bet C B1 V := by
  obtain ⟨B1', hCB1'V, hCA1_CB1', _⟩ :=
    copy_point_inside_congruent_segment hCA1U hCU_CV
  have hB2CB1 : Bet B2 C B1 := bet_symm hB1CB2
  have hB2CB1' : Bet B2 C B1' :=
    bet_inner_trans hB2CV hCB1'V
  have hCB1_CB1' : Cong C B1 C B1' :=
    cong_trans (cong_symm hCA1_CB1) hCA1_CB1'
  have hB1_eq : B1 = B1' :=
    segment_extension_unique hB2ne hB2CB1 hB2CB1' hCB1_CB1'
  simpa only [← hB1_eq] using hCB1'V

/-- Krippen's midpoint-order conclusion for the reflected configuration,
obtained by combining segment-copy order transport with the two-Pasch
intersection lemma. This makes no use of a preexisting distance order. -/
theorem krippen_ordered_reflection_tarski
    {A1 A2 B1 B2 C M1 M2 U V W : Point}
    (hB2ne : B2 ≠ C)
    (hB1CB2 : Bet B1 C B2)
    (hCA1_CB1 : Cong C A1 C B1)
    (hCA2_CB2 : Cong C A2 C B2)
    (hM1 : MulMidpoint M1 A1 B1)
    (hM2 : MulMidpoint M2 A2 B2)
    (hCU : MulMidpoint C A2 U)
    (hCV : MulMidpoint C B2 V)
    (hCW : MulMidpoint C M2 W)
    (hCA1U : Bet C A1 U) :
    Bet M1 C M2 := by
  have hCB1V : Bet C B1 V :=
    congruent_rays_preserve_bet_tarski
      hB2ne hB1CB2 hCV.1 hCA1_CB1
      (cong_trans (cong_symm hCU.2)
        (cong_trans hCA2_CB2 hCV.2)) hCA1U
  have hWUV : MulMidpoint W U V :=
    mul_reflection_preserves_midpoint hCU hCW hCV hM2
  have hCU_CV : Cong C U C V :=
    cong_trans (cong_symm hCU.2)
      (cong_trans hCA2_CB2 hCV.2)
  exact krippen_of_reflected_configuration_tarski
    (bet_symm hCA1U) (bet_symm hCB1V)
    hWUV.1 (cong_reverse_both hCU_CV)
    (cong_reverse_both hCA1_CB1)
    (cong_reverse_both hWUV.2) hM1 hCW

/-- GeoCoq's Krippen order lemma, in the original Tarski point language.
The two possible ray orders are handled by reflecting the longer or the
shorter comparison segment; no distance-order primitive is introduced. -/
theorem krippen_full_tarski
    {A1 A2 B1 B2 C M1 M2 : Point}
    (hA1CA2 : Bet A1 C A2)
    (hB1CB2 : Bet B1 C B2)
    (hCA1_CB1 : Cong C A1 C B1)
    (hCA2_CB2 : Cong C A2 C B2)
    (hM1 : MulMidpoint M1 A1 B1)
    (hM2 : MulMidpoint M2 A2 B2) :
    Bet M1 C M2 := by
  by_cases hA2C : A2 = C
  · have hCB2 : C = B2 :=
      cong_identity C B2 C (by
        simpa [hA2C] using (cong_symm hCA2_CB2))
    have hCM2 : C = M2 :=
      between_identity C M2 (by
        simpa [hA2C, ← hCB2] using hM2.1)
    simpa [← hCM2] using (bet_end M1 C)
  · have hB2C : B2 ≠ C := by
      intro h
      have heq : C = A2 :=
        cong_identity C A2 C (by simpa [h] using hCA2_CB2)
      exact hA2C heq.symm
    obtain ⟨U, hCU, _⟩ :=
      mul_reflection_exists_unique C A2
    obtain ⟨V, hCV, _⟩ :=
      mul_reflection_exists_unique C B2
    obtain ⟨W, hCW, _⟩ :=
      mul_reflection_exists_unique C M2
    rcases ray_bet_comparable_after_station
        hA2C (bet_symm hA1CA2) hCU.1 with
      hCA1U | hCUA1
    · exact krippen_ordered_reflection_tarski
        hB2C hB1CB2 hCA1_CB1 hCA2_CB2
        hM1 hM2 hCU hCV hCW hCA1U
    · have hUC : U ≠ C := by
        intro h
        have heq : C = A2 :=
          cong_identity C A2 C (by simpa [h] using hCU.2)
        exact hA2C heq.symm
      have hA1C : A1 ≠ C := by
        intro h
        have heq : C = U :=
          between_identity C U (by simpa [h] using hCUA1)
        exact hUC heq.symm
      have hB1C : B1 ≠ C := by
        intro h
        have heq : C = A1 :=
          cong_identity C A1 C (by simpa [h] using hCA1_CB1)
        exact hA1C heq.symm
      obtain ⟨U1, hCU1, _⟩ :=
        mul_reflection_exists_unique C A1
      obtain ⟨V1, hCV1, _⟩ :=
        mul_reflection_exists_unique C B1
      obtain ⟨W1, hCW1, _⟩ :=
        mul_reflection_exists_unique C M1
      have hCA2U1 : Bet C A2 U1 :=
        congruent_rays_preserve_bet_tarski
          hA1C (bet_symm hA1CA2) hCU1.1
          (cong_symm hCU.2) hCU1.2 hCUA1
      have hback : Bet M2 C M1 :=
        krippen_ordered_reflection_tarski
          hB1C (bet_symm hB1CB2)
          hCA2_CB2 hCA1_CB1
          hM2 hM1 hCU1 hCV1 hCW1 hCA2U1
      exact bet_symm hback

/-- Gupta's initial configuration therefore contains the exact inner
betweenness consequence used to construct the perpendicular foot. -/
theorem gupta_krippen_bet_tarski
    {P C Y Q Q' Z C' X : Point}
    (hPCY : MulMidpoint P C Y)
    (hPYQ : Bet P Y Q)
    (hZmid : MulMidpoint Z Q Q')
    (hPer : TarskiPer Q Z Y)
    (hQ'YC' : Bet Q' Y C')
    (hYC'YC : Cong Y C' Y C)
    (hX : MulMidpoint X C C') :
    Bet Z Y X := by
  obtain ⟨hQYC, hYQYQ', hYCYC'⟩ :=
    gupta_krippen_input_tarski
      hPCY hPYQ hZmid hPer hYC'YC
  exact krippen_full_tarski hQYC hQ'YC'
    hYQYQ' hYCYC' hZmid hX

/-- Five-segment propagation in Gupta's construction produces a second
point equidistant from the segment endpoints C and C'. -/
theorem gupta_second_station_equidistant_tarski
    {Q Q' Y C C' Z : Point}
    (hQY : Q ≠ Y)
    (hQYC : Bet Q Y C)
    (hQ'YC' : Bet Q' Y C')
    (hYQYQ' : Cong Y Q Y Q')
    (hYCYC' : Cong Y C Y C')
    (hZ : MulMidpoint Z Q Q') :
    Cong Z C Z C' := by
  have hQY_Q'Y : Cong Q Y Q' Y :=
    cong_reverse_both hYQYQ'
  have hQZ_Q'Z : Cong Q Z Q' Z :=
    cong_reverse_both hZ.2
  have hCZ_C'Z : Cong C Z C' Z :=
    five_segment Q Q' Y Y C C' Z Z
      hQY_Q'Y hYCYC' hQZ_Q'Z
      (congr_refl Y Z) hQYC hQ'YC' hQY
  exact cong_reverse_both hCZ_C'Z

/-- Gupta's perpendicular-foot construction (GeoCoq Ch08 l8_18): any point
outside a nondegenerate line has an internal Tarski perpendicular foot.
This uses only the primitive Tarski plane and the preceding Krippen lemma. -/
theorem gupta_l8_18_foot_tarski
    {A B C : Point} (hNoncol : ¬ Col A B C) :
    ∃ X : Point, Col A B X ∧ TarskiPerp A B C X := by
  obtain ⟨Y, P, Z, Q, Q', C', X, hBAY, hAYAC,
      hPCY, hAYZ, hYZYP, hPYQ, hYQYA, hZmid,
      hQ'YC', hYC'YC, hXCC', _, _, hPerQZY⟩ :=
    gupta_l8_18_orthogonal_seed_tarski hNoncol
  have hAB : A ≠ B := noncol_ne_first_second hNoncol
  have hAC : A ≠ C := noncol_ne_first_third hNoncol
  have hAY : A ≠ Y := by
    intro h
    subst Y
    exact hAC (cong_identity A C A (cong_symm hAYAC))
  have hQY : Q ≠ Y := by
    intro h
    have hYA : Y = A :=
      cong_identity Y A Y (by simpa [h] using (cong_symm hYQYA))
    exact hAY hYA.symm
  have hPY : P ≠ Y := by
    intro h
    have hYC : Y = C :=
      cong_identity Y C Y (by simpa [h] using hPCY.2)
    have hYAB : Col A B Y := Or.inr (Or.inr (bet_symm hBAY))
    exact hNoncol (by rw [← hYC]; exact hYAB)
  have hZY : Z ≠ Y := by
    intro h
    have hYP : Y = P :=
      cong_identity Y P Y (by simpa [h] using (cong_symm hYZYP))
    exact hPY hYP.symm
  have hZ_Y_X : Bet Z Y X :=
    gupta_krippen_bet_tarski hPCY hPYQ hZmid hPerQZY
      hQ'YC' hYC'YC hXCC'
  have hZ_X : Z ≠ X := by
    intro h
    have hZYeq : Z = Y :=
      between_identity Z Y (by simpa [← h] using hZ_Y_X)
    exact hZY hZYeq
  have hY_AB : Col A B Y := Or.inr (Or.inr (bet_symm hBAY))
  have hAB_AY : ∀ T : Point, Col A B T ↔ Col A Y T :=
    col_line_extensionality_tarski hAB hAY
      (col_left A B) hY_AB
  have hZ_AB : Col A B Z :=
    (hAB_AY Z).mpr (Or.inl hAYZ)
  have hAB_ZY : ∀ T : Point, Col A B T ↔ Col Z Y T :=
    col_line_extensionality_tarski hAB hZY hZ_AB hY_AB
  have hX_AB : Col A B X :=
    (hAB_ZY X).mpr (Or.inl hZ_Y_X)
  have hCX : C ≠ X := by
    intro h
    exact hNoncol (by simpa [h] using hX_AB)
  obtain ⟨hQYC, hYQYQ', hYCYC'⟩ :=
    gupta_krippen_input_tarski hPCY hPYQ hZmid hPerQZY hYC'YC
  have hZC : Cong Z C Z C' :=
    gupta_second_station_equidistant_tarski
      hQY hQYC hQ'YC' hYQYQ' hYCYC' hZmid
  have hPerZXC : TarskiPer Z X C := ⟨C', hXCC', hZC⟩
  have hPerpAt : TarskiPerpAt X A B C X :=
    tarski_perp_at_of_one_right_angle_tarski
      hAB hCX
      (col_rotate (col_rotate hX_AB)) (col_left X C)
      (col_rotate (col_rotate hZ_AB)) (Or.inl (bet_start C X))
      hZ_X hCX hPerZXC
  exact ⟨X, hX_AB, ⟨X, hPerpAt⟩⟩

/-- A center of the midpoint reflection cannot coincide with the other
midpoint center when the reflected endpoints are distinct.  This uses only
the uniqueness of Tarski midpoint reflection, no perpendicularity theorem. -/
theorem tarski_per_midpoint_apart_tarski
    {A B C C' D P : Point}
    (_hPer : TarskiPer A B C)
    (hP : MulMidpoint P C' D)
    (hA : MulMidpoint A C' C)
    (hB : MulMidpoint B D C)
    (hBC : B ≠ C) :
    A ≠ P := by
  intro hAP
  have hAPmid : MulMidpoint A C' D := by
    simpa [← hAP] using hP
  obtain ⟨_, _, huniq⟩ := mul_reflection_exists_unique A C'
  have hDC : D = C :=
    (huniq D hAPmid).trans (huniq C hA).symm
  have hCB : C = B :=
    between_identity C B (by simpa [hDC] using hB.1)
  exact hBC hCB.symm

/-- Public GeoCoq-compatible name for the complete Krippen order lemma. -/
theorem krippen_l7_22_tarski
    {A₁ A₂ B₁ B₂ C M₁ M₂ : Point}
    (hA : Bet A₁ C A₂)
    (hB : Bet B₁ C B₂)
    (hCA₁CB₁ : Cong C A₁ C B₁)
    (hCA₂CB₂ : Cong C A₂ C B₂)
    (hM₁ : MulMidpoint M₁ A₁ B₁)
    (hM₂ : MulMidpoint M₂ A₂ B₂) :
    Bet M₁ C M₂ :=
  krippen_full_tarski hA hB hCA₁CB₁ hCA₂CB₂ hM₁ hM₂

/-- Public name for Gupta's perpendicular-foot existence theorem.
The proof is entirely synthetic over the Tarski plane. -/
theorem perpendicular_foot_exists_tarski
    {A B C : Point}
    (hNoncol : ¬ Col A B C) :
    ∃ X : Point, Col A B X ∧ TarskiPerp A B C X :=
  gupta_l8_18_foot_tarski hNoncol

/-- Central reflection preserves right angles in the Tarski geometry.
This uses only midpoint transport and segment congruence. -/
theorem mul_reflection_preserves_per_tarski
    {M A B C A' B' C' : Point}
    (hA : MulMidpoint M A A')
    (hB : MulMidpoint M B B')
    (hC : MulMidpoint M C C')
    (hPer : TarskiPer A B C) :
    TarskiPer A' B' C' := by
  obtain ⟨D, hBD, hAD⟩ := hPer
  obtain ⟨D', hD, _⟩ := mul_reflection_exists_unique M D
  have hB'D : MulMidpoint B' C' D' :=
    mul_reflection_preserves_midpoint hC hB hD hBD
  have hAC : Cong A' C' A C :=
    mul_reflection_preserves_cong hA hC
  have hAD' : Cong A D A' D' :=
    cong_symm (mul_reflection_preserves_cong hA hD)
  have hACD : Cong A' C' A' D' :=
    cong_trans hAC (cong_trans hAD hAD')
  exact ⟨D', hB'D, hACD⟩

/-- A perpendicular foot provides the right angle at that foot. -/
theorem perpendicular_foot_right_angle_tarski
    {A B C : Point} (hNoncol : ¬ Col A B C) :
    ∃ X : Point, Col A B X ∧ TarskiPer A X C := by
  obtain ⟨X, hXAB, ⟨M, hM⟩⟩ :=
    perpendicular_foot_exists_tarski hNoncol
  rcases hM with ⟨_, hCX, hMAB, hMCX, hRight⟩
  have hMX : M = X :=
    line_intersection_unique_tarski hNoncol hCX
      (col_rotate hMAB) hXAB
      (col_rotate hMCX) (col_right C X)
  have hPer : TarskiPer A M C :=
    hRight A C
      (col_rotate (col_rotate (col_left A B)))
      (col_rotate (col_rotate (col_left C X)))
  exact ⟨X, hXAB, hMX ▸ hPer⟩

/-- Both endpoints of the reference line form a right angle with the
perpendicular leg at the foot; this retains the nondegenerate endpoint B
when the foot itself equals A. -/
theorem perpendicular_foot_two_right_angles_tarski
    {A B C : Point} (hNoncol : ¬ Col A B C) :
    ∃ X : Point, Col A B X ∧ TarskiPer A X C ∧ TarskiPer B X C := by
  obtain ⟨X, hXAB, ⟨M, hM⟩⟩ :=
    perpendicular_foot_exists_tarski hNoncol
  rcases hM with ⟨_, hCX, hMAB, hMCX, hRight⟩
  have hMX : M = X :=
    line_intersection_unique_tarski hNoncol hCX
      (col_rotate hMAB) hXAB
      (col_rotate hMCX) (col_right C X)
  have hPerA : TarskiPer A M C :=
    hRight A C
      (col_rotate (col_rotate (col_left A B)))
      (col_rotate (col_rotate (col_left C X)))
  have hPerB : TarskiPer B M C :=
    hRight B C
      (col_rotate (col_rotate (col_right A B)))
      (col_rotate (col_rotate (col_left C X)))
  exact ⟨X, hXAB, hMX ▸ hPerA, hMX ▸ hPerB⟩

/-- GeoCoq l8_21_aux: an isosceles station A allows us to form the
midpoint of the two reflected legs C' and C'', without general midpoint
existence. -/
theorem gupta_l8_21_midpoint_seed_tarski
    {A B C : Point} (hNoncol : ¬ Col A B C) :
    ∃ X C' C'' P : Point,
      Col A B X ∧ TarskiPer A X C ∧
      MulMidpoint X C C' ∧ MulMidpoint A C C'' ∧
      MulMidpoint P C' C'' := by
  obtain ⟨X, hXAB, hPer⟩ :=
    perpendicular_foot_right_angle_tarski hNoncol
  obtain ⟨C', hXC', _⟩ := mul_reflection_exists_unique X C
  obtain ⟨C'', hAC'', _⟩ := mul_reflection_exists_unique A C
  have hAC_AC' : Cong A C A C' :=
    tarski_per_cong_of_reflection_tarski hPer hXC'
  have hAC'_AC'' : Cong A C' A C'' :=
    cong_trans (cong_symm hAC_AC') hAC''.2
  obtain ⟨P, hP⟩ :=
    midpoint_exists_of_equidistant_station_tarski
      (A := C') (B := C'') (C := A) hAC'_AC''
  exact ⟨X, C', C'', P, hXAB, hPer, hXC', hAC'', hP⟩

/-- GeoCoq Ch08 l8_20_1: transport a Tarski right angle across three
midpoint constraints, with only midpoint reflection and inner five segments. -/
theorem tarski_per_midpoint_transport_tarski
    {A B C C' D P : Point}
    (hPer : TarskiPer A B C)
    (hP : MulMidpoint P C' D)
    (hA : MulMidpoint A C' C)
    (hB : MulMidpoint B D C) :
    TarskiPer B A P := by
  by_cases hAB : A = B
  · subst B
    obtain ⟨E, hE, _⟩ := mul_reflection_exists_unique A P
    exact ⟨E, hE, hE.2⟩
  · obtain ⟨B', hAB', _⟩ := mul_reflection_exists_unique A B
    obtain ⟨D', hAD', _⟩ := mul_reflection_exists_unique A D
    obtain ⟨P', hAP', _⟩ := mul_reflection_exists_unique A P
    have hPerB'BC : TarskiPer B' B C :=
      tarski_per_change_first_collinear_tarski
        hPer hAB (Or.inl hAB'.1)
    have hPerBB'C' : TarskiPer B B' C' :=
      mul_reflection_preserves_per_tarski
        (mul_midpoint_reverse hAB') hAB'
        (mul_midpoint_reverse hA) hPerB'BC
    have hB'D'C' : MulMidpoint B' D' C' :=
      mul_reflection_preserves_midpoint
        hAD' hAB' (mul_midpoint_reverse hA) hB
    have hP'CD' : MulMidpoint P' C D' :=
      mul_reflection_preserves_midpoint
        hA hAP' hAD' hP
    have hC'D_D'C : Cong C' D D' C :=
      cong_reverse_right
        (cong_symm (mul_reflection_preserves_cong hA hAD'))
    have hPD_P'C : Cong P D P' C :=
      cong_trans
        (cong_symm (mul_reflection_preserves_cong hAP' hAD'))
        (cong_symm hP'CD'.2)
    have hC'B_D'B : Cong C' B D' B :=
      cong_reverse_both
        (tarski_per_cong_of_reflection_tarski hPerBB'C'
          (mul_midpoint_reverse hB'D'C'))
    have hDB_CB : Cong D B C B := cong_reverse_both hB.2
    have hPB_P'B : Cong P B P' B :=
      inner_five_segment
        hP.1 (bet_symm hP'CD'.1)
        hC'D_D'C hPD_P'C hC'B_D'B hDB_CB
    exact ⟨P', hAP', cong_reverse_both hPB_P'B⟩

/-- GeoCoq Ch08 l8_21_aux: Pasch intersects the two midpoint legs,
producing a base-line point T between C and P and the right angle at A. -/
theorem gupta_l8_21_intersection_seed_tarski
    {A B C : Point} (hNoncol : ¬ Col A B C) :
    ∃ X C' C'' P T : Point,
      Col A B X ∧ TarskiPer A X C ∧
      MulMidpoint X C C' ∧ MulMidpoint A C C'' ∧
      MulMidpoint P C' C'' ∧
      TarskiPer X A P ∧ Col A B T ∧ Bet C T P := by
  obtain ⟨X, C', C'', P, hXAB, hPer,
      hXC', hAC'', hP⟩ :=
    gupta_l8_21_midpoint_seed_tarski hNoncol
  have hPerXAP : TarskiPer X A P :=
    tarski_per_midpoint_transport_tarski
      hPer (mul_midpoint_reverse hP)
      (mul_midpoint_reverse hAC'')
      (mul_midpoint_reverse hXC')
  obtain ⟨T, hPTC, hXTA⟩ :=
    pasch_two_crossings_tarski
      (bet_symm hXC'.1) (bet_symm hAC''.1) hP.1
  have hAB : A ≠ B := noncol_ne_first_second hNoncol
  have hTAB : Col A B T :=
    col_segment_closed_tarski hAB hXAB (col_left A B) hXTA
  exact ⟨X, C', C'', P, T, hXAB, hPer,
    hXC', hAC'', hP, hPerXAP, hTAB, bet_symm hPTC⟩

/-- The foot of the perpendicular is also the intersection witness
of the two perpendicular lines. -/
theorem perpendicular_foot_at_tarski
    {A B C : Point} (hNoncol : ¬ Col A B C) :
    ∃ X : Point, Col A B X ∧ TarskiPerpAt X A B C X := by
  obtain ⟨X, hXAB, ⟨M, hM⟩⟩ :=
    perpendicular_foot_exists_tarski hNoncol
  rcases hM with ⟨hAB, hCX, hMAB, hMCX, hRight⟩
  have hMX : M = X :=
    line_intersection_unique_tarski hNoncol hCX
      (col_rotate hMAB) hXAB
      (col_rotate hMCX) (col_right C X)
  subst M
  exact ⟨X, hXAB, ⟨hAB, hCX, hMAB, hMCX, hRight⟩⟩

/-- GeoCoq l8_21_aux: from an off-line point construct a perpendicular
at A and an intersection T between the original point and that line. -/
theorem gupta_l8_21_aux_tarski
    {A B C : Point} (hNoncol : ¬ Col A B C) :
    ∃ P T : Point,
      TarskiPerp A B P A ∧ Col A B T ∧ Bet C T P := by
  obtain ⟨X, hXAB, hAt⟩ :=
    perpendicular_foot_at_tarski hNoncol
  have hPerAXC : TarskiPer A X C :=
    hAt.2.2.2.2 A C
      (col_rotate (col_rotate (col_left A B)))
      (Or.inl (bet_start C X))
  obtain ⟨C', hXC', _⟩ := mul_reflection_exists_unique X C
  obtain ⟨C'', hAC'', _⟩ := mul_reflection_exists_unique A C
  have hAC_AC' : Cong A C A C' :=
    tarski_per_cong_of_reflection_tarski hPerAXC hXC'
  have hAC'_AC'' : Cong A C' A C'' :=
    cong_trans (cong_symm hAC_AC') hAC''.2
  obtain ⟨P, hP⟩ := midpoint_exists_of_equidistant_station_tarski
    (A := C') (B := C'') (C := A) hAC'_AC''
  have hPerXAP : TarskiPer X A P :=
    tarski_per_midpoint_transport_tarski
      hPerAXC (mul_midpoint_reverse hP)
      (mul_midpoint_reverse hAC'')
      (mul_midpoint_reverse hXC')
  obtain ⟨T, hPTC, hXTA⟩ :=
    pasch_two_crossings_tarski
      (bet_symm hXC'.1) (bet_symm hAC''.1) hP.1
  have hAB : A ≠ B := noncol_ne_first_second hNoncol
  have hTAB : Col A B T :=
    col_segment_closed_tarski hAB hXAB (col_left A B) hXTA
  by_cases hXA : X = A
  · subst X
    have hCA : C ≠ A := (noncol_ne_first_third hNoncol).symm
    have hAC''ne : A ≠ C'' := by
      intro heq
      have hAC : A = C :=
        cong_identity A C A (by simpa [← heq] using hAC''.2)
      exact hCA hAC.symm
    have hPerBAC : TarskiPer B A C :=
      hAt.2.2.2.2 B C
        (col_rotate (col_rotate (col_right A B)))
        (Or.inl (bet_start C A))
    have hPerBAC'' : TarskiPer B A C'' :=
      tarski_per_reflect_third_tarski hPerBAC hAC''
    have hPerpAt : TarskiPerpAt A A B C'' A :=
      tarski_perp_at_of_one_right_angle_tarski
        hAB hAC''ne.symm
        (Or.inl (bet_start A B)) (col_left A C'')
        (col_rotate (col_rotate (col_right A B)))
        (Or.inl (bet_start C'' A))
        hAB.symm hAC''ne.symm hPerBAC''
    exact ⟨C'', A, ⟨A, hPerpAt⟩,
      col_left A B, hAC''.1⟩
  · have hXC : X ≠ C := hAt.2.1.symm
    have hAP : A ≠ P :=
      tarski_per_midpoint_apart_tarski
        hPerAXC (mul_midpoint_reverse hP)
        (mul_midpoint_reverse hAC'')
        (mul_midpoint_reverse hXC') hXC
    have hPerpAt : TarskiPerpAt A A B P A :=
      tarski_perp_at_of_one_right_angle_tarski
        hAB hAP.symm
        (Or.inl (bet_start A B)) (col_left A P)
        (col_rotate (col_rotate hXAB))
        (Or.inl (bet_start P A))
        hXA hAP.symm hPerXAP
    exact ⟨P, T, ⟨A, hPerpAt⟩, hTAB, bet_symm hPTC⟩

/-- Every nondegenerate Tarski line has a point outside that line, by
the lower-dimension axiom and uniqueness of a line through two points. -/
theorem off_line_point_exists_tarski
    {A B : Point} (hAB : A ≠ B) :
    ∃ C : Point, ¬ Col A B C := by
  obtain ⟨O, I, J, hOIJ⟩ := Plane.lower_dim (Point := Point)
  by_cases hO : Col A B O
  · by_cases hI : Col A B I
    · by_cases hJ : Col A B J
      · have hOI : O ≠ I := noncol_ne_first_second hOIJ
        have hline : ∀ S : Point, Col A B S ↔ Col O I S :=
          col_line_extensionality_tarski hAB hOI hO hI
        exact False.elim (hOIJ ((hline J).mp hJ))
      · exact ⟨J, hJ⟩
    · exact ⟨I, hI⟩
  · exact ⟨O, hO⟩

/-- GeoCoq Ch08 l8_21: a perpendicular through A and a crossing point
exist for every C, including points already on the base line. -/
theorem gupta_l8_21_tarski
    {A B C : Point} (hAB : A ≠ B) :
    ∃ P T : Point,
      TarskiPerp A B P A ∧ Col A B T ∧ Bet C T P := by
  by_cases hCol : Col A B C
  · obtain ⟨C', hC'⟩ := off_line_point_exists_tarski hAB
    obtain ⟨P, _, hPerp, _, _⟩ := gupta_l8_21_aux_tarski hC'
    exact ⟨P, C, hPerp, hCol, bet_start C P⟩
  · exact gupta_l8_21_aux_tarski hCol

/-- A geometric segment-length preorder expressed solely by betweenness
and congruence, without a scalar length or field interpretation. -/
def TarskiSegmentLe (A B C D : Point) : Prop :=
  ∃ E : Point, Bet C E D ∧ Cong A B C E

/-- Reflexivity of the synthetic segment-length preorder. -/
theorem tarski_segment_le_refl (A B : Point) :
    TarskiSegmentLe A B A B :=
  ⟨B, bet_end A B, congr_refl A B⟩

/-- Replacing a segment by a congruent one preserves its length comparison. -/
theorem tarski_segment_le_cong_left
    {A B A' B' C D : Point}
    (hCong : Cong A B A' B')
    (hLe : TarskiSegmentLe A' B' C D) :
    TarskiSegmentLe A B C D := by
  obtain ⟨E, hBet, hCE⟩ := hLe
  exact ⟨E, hBet, cong_trans hCong hCE⟩

/-- Segment comparison is invariant under replacing its right-hand
segment by a congruent one.  The corresponding intermediate point is
constructed on the target segment using only Tarski congruence. -/
theorem tarski_segment_le_cong_right
    {A B C D C' D' : Point}
    (hCong : Cong C D C' D')
    (hLe : TarskiSegmentLe A B C D) :
    TarskiSegmentLe A B C' D' := by
  obtain ⟨E, hCED, hABCE⟩ := hLe
  obtain ⟨E', hC'E'D', hCE_C'E', _⟩ :=
    copy_point_inside_congruent_segment hCED hCong
  exact ⟨E', hC'E'D', cong_trans hABCE hCE_C'E'⟩

/-- Transitivity of the synthetic segment-length comparison.  The proof
copies the first subsegment into the second comparison's witness and
uses betweenness transitivity; no ordered field is assumed. -/
theorem tarski_segment_le_trans
    {A B C D E F : Point}
    (hABCD : TarskiSegmentLe A B C D)
    (hCDEF : TarskiSegmentLe C D E F) :
    TarskiSegmentLe A B E F := by
  obtain ⟨P, hCPD, hABCP⟩ := hABCD
  obtain ⟨Q, hEQF, hCDEQ⟩ := hCDEF
  obtain ⟨R, hERQ, hCPER, _⟩ :=
    copy_point_inside_congruent_segment hCPD hCDEQ
  exact ⟨R, bet_extend hERQ hEQF, cong_trans hABCP hCPER⟩

/-- Any two Tarski segments can be compared by a copied subsegment. -/
theorem tarski_segment_le_cases
    (A B C D : Point) :
    TarskiSegmentLe A B C D ∨ TarskiSegmentLe C D A B := by
  by_cases hCD : C = D
  · right
    refine ⟨A, bet_start A B, ?_⟩
    simpa [hCD] using (cong_zero C A)
  obtain ⟨E, hDCE, hCE_AB⟩ := segment_construction D C A B
  by_cases hEC : E = C
  · left
    have hAB : A = B :=
      cong_identity A B C (by
        simpa [hEC] using (cong_symm hCE_AB))
    refine ⟨C, bet_start C D, ?_⟩
    simpa [hAB] using (cong_zero A C)
  obtain ⟨F, hCF, _⟩ := mul_reflection_exists_unique C E
  have hAB_CF : Cong A B C F :=
    cong_trans (cong_symm hCE_AB) hCF.2
  rcases ray_bet_comparable_after_station
      hEC (bet_symm hDCE) hCF.1 with hCDF | hCFD
  · right
    obtain ⟨G, hAGB, hCD_AG, _⟩ :=
      copy_point_inside_congruent_segment hCDF (cong_symm hAB_CF)
    exact ⟨G, hAGB, hCD_AG⟩
  · left
    exact ⟨F, hCFD, hAB_CF⟩

/-- For the midpoint construction, cut from BQ a segment congruent to
AP and meet the resulting transversal PR with the base line by Pasch. -/
theorem tarski_midpoint_aux_pasch_candidate
    {A B P Q T : Point}
    (hAB : A ≠ B)
    (hT : Col A B T)
    (hQTP : Bet Q T P)
    (hLe : TarskiSegmentLe A P B Q) :
    ∃ R X : Point,
      Bet B R Q ∧ Cong A P B R ∧
      Col A B X ∧ Bet R X P := by
  obtain ⟨R, hBRQ, hAPBR⟩ := hLe
  obtain ⟨X, hTXB, hRXP⟩ :=
    inner_pasch P B Q T R (bet_symm hQTP) hBRQ
  have hXAB : Col A B X :=
    col_segment_closed_tarski hAB hT (col_right A B) hTXB
  exact ⟨R, X, hBRQ, hAPBR, hXAB, hRXP⟩

/-- A right angle is preserved when the third leg moves along its line. -/
theorem tarski_per_change_third_collinear_tarski
    {A B C C' : Point}
    (hPer : TarskiPer A B C)
    (hBC : B ≠ C)
    (hCol : Col B C C') :
    TarskiPer A B C' := by
  exact tarski_per_swap_legs_tarski
    (tarski_per_change_first_collinear_tarski
      (tarski_per_swap_legs_tarski hPer) hBC.symm hCol)

/-- A Tarski right angle with two nondegenerate legs is noncollinear. -/
theorem tarski_per_noncol_tarski
    {A B C : Point}
    (hAB : A ≠ B) (hBC : B ≠ C)
    (hPer : TarskiPer A B C) :
    ¬ Col A B C := by
  intro hCol
  rcases tarski_per_collinear_legs_degenerate_tarski hPer hCol with h | h
  · exact hAB h
  · exact hBC h.symm

/-- GeoCoq Ch04 l4_14: copy a collinear triple onto two endpoints of a
congruent segment, preserving the three pairwise segment congruences. -/
theorem tarski_copy_collinear_three_points
    {A B C A' B' : Point}
    (hCol : Col A B C)
    (hAB : Cong A B A' B') :
    ∃ C' : Point,
      Cong A B A' B' ∧ Cong A C A' C' ∧ Cong B C B' C' := by
  rcases hCol with hABC | hBCA | hCAB
  · obtain ⟨C', hA'B'C', hB'C'_BC⟩ :=
      segment_construction A' B' B C
    have hAC_A'C' : Cong A C A' C' :=
      segment_cong_add hABC hA'B'C' hAB
        (cong_symm hB'C'_BC)
    exact ⟨C', hAB, hAC_A'C', cong_symm hB'C'_BC⟩
  · obtain ⟨C', hA'C'B', hAC_A'C', hCB_C'B'⟩ :=
      copy_point_inside_congruent_segment (bet_symm hBCA) hAB
    exact ⟨C', hAB, hAC_A'C', cong_reverse_both hCB_C'B'⟩
  · obtain ⟨C', hB'A'C', hA'C'_AC⟩ :=
      segment_construction B' A' A C
    have hCA_C'A' : Cong C A C' A' :=
      cong_symm (cong_reverse_both hA'C'_AC)
    have hCB_C'B' : Cong C B C' B' :=
      segment_cong_add hCAB (bet_symm hB'A'C') hCA_C'A' hAB
    exact ⟨C', hAB,
      cong_symm hA'C'_AC, cong_reverse_both hCB_C'B'⟩

/-- GeoCoq Ch04 l4_16: five-segment congruence transfer in all three
collinear order configurations. -/
theorem tarski_five_segment_collinear_tarski
    {A B C A' B' C' D D' : Point}
    (hABne : A ≠ B) (hCol : Col A B C)
    (hAB : Cong A B A' B')
    (hBC : Cong B C B' C')
    (hAC : Cong A C A' C')
    (hAD : Cong A D A' D')
    (hBD : Cong B D B' D') :
    Cong C D C' D' := by
  rcases hCol with hABC | hBCA | hCAB
  · have hA'B'C' : Bet A' B' C' :=
      bet_of_three_segment_congruences hABC hAB hBC hAC
    exact five_segment A A' B B' C C' D D'
      hAB hBC hAD hBD hABC hA'B'C' hABne
  · have hB'C'A' : Bet B' C' A' :=
      bet_of_three_segment_congruences hBCA hBC
        (cong_reverse_both hAC) (cong_reverse_both hAB)
    exact inner_five_segment hBCA hB'C'A'
      (cong_reverse_both hAB) (cong_reverse_both hAC)
      hBD hAD
  · have hBAC : Bet B A C := bet_symm hCAB
    have hB'A'C' : Bet B' A' C' :=
      bet_of_three_segment_congruences hBAC
        (cong_reverse_both hAB) hAC hBC
    exact five_segment B B' A A' C C' D D'
      (cong_reverse_both hAB) hAC hBD hAD
      hBAC hB'A'C' hABne.symm

/-- Three pairwise congruent sides transport collinearity of the triple. -/
theorem tarski_col_of_congr_three_points
    {A B C A' B' C' : Point}
    (hCol : Col A B C)
    (hAB : Cong A B A' B')
    (hAC : Cong A C A' C')
    (hBC : Cong B C B' C') :
    Col A' B' C' := by
  rcases hCol with hABC | hBCA | hCAB
  · exact Or.inl
      (bet_of_three_segment_congruences hABC hAB hBC hAC)
  · exact Or.inr (Or.inl
      (bet_of_three_segment_congruences hBCA hBC
        (cong_reverse_both hAC) (cong_reverse_both hAB)))
  · exact Or.inr (Or.inr
      (bet_of_three_segment_congruences hCAB
        (cong_reverse_both hAC) hAB (cong_reverse_both hBC)))

/-- GeoCoq Ch07 l7_21: opposite-side congruences force both crossing
diagonals to be bisected at their intersection point P. -/
theorem tarski_l7_21_diagonals_midpoint
    {A B C D P : Point}
    (hNoncol : ¬ Col A B C)
    (hBD : B ≠ D)
    (hABCD : Cong A B C D)
    (hBCDA : Cong B C D A)
    (hAPC : Col A P C)
    (hBPD : Col B P D) :
    MulMidpoint P A C ∧ MulMidpoint P B D := by
  have hBDP : Col B D P := col_swap_last hBPD
  obtain ⟨P', hBD_DB, hBP_DP', hDP_BP'⟩ :=
    tarski_copy_collinear_three_points hBDP
      (cong_pseudo_reflexivity B D)
  have hDBP' : Col D B P' :=
    tarski_col_of_congr_three_points hBDP
      hBD_DB hBP_DP' hDP_BP'
  have hPA_P'C : Cong P A P' C :=
    tarski_five_segment_collinear_tarski
      hBD hBDP hBD_DB hDP_BP' hBP_DP'
      (cong_reverse_both hABCD) (cong_symm hBCDA)
  have hPC_P'A : Cong P C P' A :=
    tarski_five_segment_collinear_tarski
      hBD hBDP hBD_DB hDP_BP' hBP_DP'
      hBCDA (cong_reverse_both (cong_symm hABCD))
  have hCP'A : Col C P' A :=
    tarski_col_of_congr_three_points hAPC
      (cong_reverse_both hPA_P'C)
      (cong_pseudo_reflexivity A C) hPC_P'A
  have hACB : ¬ Col A C B := by
    intro h
    exact hNoncol (col_swap_last h)
  have hPP' : P = P' :=
    line_intersection_unique_tarski hACB hBD
      (col_swap_last hAPC)
      (col_rotate (col_rotate hCP'A))
      hBDP (col_swap hDBP')
  have hPA_PC : Cong P A P C := by
    simpa [← hPP'] using hPA_P'C
  have hPB_PD : Cong P B P D := by
    have hBPD_P : Cong B P D P := by
      simpa [← hPP'] using hBP_DP'
    exact cong_reverse_both hBPD_P
  have hAC : A ≠ C := noncol_ne_first_third hNoncol
  have hMidAC : MulMidpoint P A C := by
    rcases col_equidistant_midpoint_or_eq_tarski
        (col_swap_last hAPC) hPA_PC with h | h
    · exact False.elim (hAC h)
    · exact h
  have hMidBD : MulMidpoint P B D := by
    rcases col_equidistant_midpoint_or_eq_tarski hBDP hPB_PD
      with h | h
    · exact False.elim (hBD h)
    · exact h
  exact ⟨hMidAC, hMidBD⟩

/-- The two perpendicular legs produce the four reflected distance
relations required by the purely synthetic construction for GeoCoq's
right-triangle congruence theorem (`per_cong`). -/
theorem tarski_per_cong_reflection_seed
    {A B P R X : Point}
    (hAB : A ≠ B)
    (hPerBAP : TarskiPer B A P)
    (hPerABR : TarskiPer A B R)
    (hX : Col A B X) :
    ∃ P' Q : Point,
      MulMidpoint A P P' ∧ MulMidpoint B R Q ∧
      Cong B P B P' ∧ Cong A R A Q ∧
      Cong X P X P' ∧ Cong X R X Q := by
  obtain ⟨P', hP', _⟩ := mul_reflection_exists_unique A P
  obtain ⟨Q, hQ, _⟩ := mul_reflection_exists_unique B R
  have hBP : Cong B P B P' :=
    tarski_per_cong_of_reflection_tarski hPerBAP hP'
  have hAR : Cong A R A Q :=
    tarski_per_cong_of_reflection_tarski hPerABR hQ
  have hPerXAP : TarskiPer X A P :=
    tarski_per_change_first_collinear_tarski
      hPerBAP hAB.symm hX
  have hXP : Cong X P X P' :=
    tarski_per_cong_of_reflection_tarski hPerXAP hP'
  have hPerXBR : TarskiPer X B R :=
    tarski_per_change_first_collinear_tarski
      hPerABR hAB (col_swap hX)
  have hXR : Cong X R X Q :=
    tarski_per_cong_of_reflection_tarski hPerXBR hQ
  exact ⟨P', Q, hP', hQ, hBP, hAR, hXP, hXR⟩

/-- A nondegenerate perpendicular crossing contains a point of the second
line outside the first.  This is a synthetic consequence of right-angle
non-collinearity and line extensionality. -/
theorem tarski_perp_at_off_first_line_tarski
    {X A B C D : Point}
    (h : TarskiPerpAt X A B C D) :
    ∃ V : Point, Col V C D ∧ V ≠ X ∧ ¬ Col A B V := by
  rcases h with ⟨hAB, hCD, hXAB, hXCD, hRight⟩
  have hUX : ∃ U : Point, Col U A B ∧ U ≠ X := by
    by_cases hAX : A = X
    · refine ⟨B, col_swap (col_right A B), ?_⟩
      intro hBX
      exact hAB (hAX.trans hBX.symm)
    · exact ⟨A, col_rotate (col_rotate (col_left A B)), hAX⟩
  have hVX : ∃ V : Point, Col V C D ∧ V ≠ X := by
    by_cases hCX : C = X
    · refine ⟨D, col_swap (col_right C D), ?_⟩
      intro hDX
      exact hCD (hCX.trans hDX.symm)
    · exact ⟨C, col_rotate (col_rotate (col_left C D)), hCX⟩
  obtain ⟨U, hUAB, hUne⟩ := hUX
  obtain ⟨V, hVCD, hVne⟩ := hVX
  have hUAB' : Col A B U := col_rotate hUAB
  have hXAB' : Col A B X := col_rotate hXAB
  have hline : ∀ S : Point, Col A B S ↔ Col U X S :=
    col_line_extensionality_tarski hAB hUne hUAB' hXAB'
  have hNoncol : ¬ Col U X V :=
    tarski_per_noncol_tarski hUne hVne.symm
      (hRight U V hUAB hVCD)
  exact ⟨V, hVCD, hVne,
    fun hVAB => hNoncol ((hline V).mp hVAB)⟩

/-- GeoCoq Ch08 l8_18_uniqueness: a pair of perpendicular lines has at
most one common foot, by uniqueness of the intersection of distinct lines. -/
theorem tarski_perp_at_intersection_unique_tarski
    {X Y A B C D : Point}
    (hX : TarskiPerpAt X A B C D)
    (hY : TarskiPerpAt Y A B C D) : X = Y := by
  obtain ⟨V, hVCD, hVne, hVoff⟩ :=
    tarski_perp_at_off_first_line_tarski hX
  have hCD : C ≠ D := hX.2.1
  have hXCD : Col C D X := col_rotate hX.2.2.2.1
  have hYCD : Col C D Y := col_rotate hY.2.2.2.1
  have hline : ∀ S : Point, Col C D S ↔ Col V X S :=
    col_line_extensionality_tarski
      hCD hVne (col_rotate hVCD) hXCD
  exact line_intersection_unique_tarski hVoff hVne
    (col_rotate hX.2.2.1) (col_rotate hY.2.2.1)
    ((hline X).mp hXCD) ((hline Y).mp hYCD)

/-- The two five-segment steps at the end of GeoCoq Ch08 `per_cong`.
This is a genuine congruence transfer, entirely in Tarski's primitive
betweenness and congruence language; its geometric premises will be
discharged by the preceding perpendicular construction. -/
theorem tarski_per_cong_final_five_segment_tarski
    {A B P R X P' R' : Point}
    (hPX : P ≠ X)
    (hPXR : Bet P X R)
    (hP'XR' : Bet P' X R')
    (hP' : MulMidpoint A P P')
    (hR' : MulMidpoint B R R')
    (hAPBR : Cong A P B R)
    (hXP : Cong X P X P')
    (hXR : Cong X R X R') :
    Cong A R P B := by
  have hP'A_R'B : Cong P' A R' B :=
    cong_trans (cong_symm (cong_reverse_right hP'.2))
      (cong_trans hAPBR (cong_reverse_right hR'.2))
  have hP'P_R'R : Cong P' P R' R :=
    segment_cong_add (bet_symm hP'.1) (bet_symm hR'.1)
      hP'A_R'B hAPBR
  have hRP'_R'P : Cong R P' R' P :=
    five_segment P P' X X R R' P' P
      (cong_reverse_both hXP) hXR
      (cong_pseudo_reflexivity P P')
      (cong_symm hXP)
      hPXR hP'XR' hPX
  have hAR_BP : Cong A R B P :=
    inner_five_segment
      (bet_symm hP'.1) (bet_symm hR'.1)
      hP'P_R'R hAPBR (cong_reverse_left hRP'_R'P)
      (cong_pseudo_reflexivity P R)
  exact cong_reverse_right hAR_BP

/-- GeoCoq Ch08 l8_7: if the angles at B and C in the same triangle
are both right, the two vertices coincide.  The proof uses two
reflections and two-station distance propagation, not coordinates. -/
theorem tarski_two_right_angles_endpoint_eq_tarski
    {A B C : Point}
    (hABC : TarskiPer A B C)
    (hACB : TarskiPer A C B) : B = C := by
  by_cases hBC : B = C
  · exact hBC
  obtain ⟨C', hMidB, hAC_AC'⟩ := hABC
  obtain ⟨A', hMidC, _⟩ := mul_reflection_exists_unique C A
  have hBCA : TarskiPer B C A :=
    tarski_per_swap_legs_tarski hACB
  have hC'CA : TarskiPer C' C A :=
    tarski_per_change_first_collinear_tarski
      hBCA hBC (Or.inl hMidB.1)
  have hC'A_C'A' : Cong C' A C' A' :=
    tarski_per_cong_of_reflection_tarski hC'CA hMidC
  have hA'C_AC : Cong A' C A C :=
    cong_symm (cong_reverse_both hMidC.2)
  have hA'C_A'C' : Cong A' C A' C' :=
    cong_trans (cong_trans hA'C_AC hAC_AC')
      (cong_reverse_both hC'A_C'A')
  have hCC' : C = C' := by
    by_cases hAA' : A = A'
    · have hCA : C = A := by
        have hb : Bet A C A := by
          simpa [← hAA'] using hMidC.1
        exact (between_identity A C hb).symm
      have hz : Cong C C C C' := by
        simpa [hCA] using hAC_AC'
      exact cong_identity C C' C (cong_symm hz)
    · have hcol : Col A A' C :=
        Or.inr (Or.inl (bet_symm hMidC.1))
      have hz : Cong C C C C' :=
        col_equidistant_of_two_stations
          hAA' hcol hAC_AC' hA'C_A'C'
      exact cong_identity C C' C (cong_symm hz)
  have hCBC : Bet C B C := by
    simpa [← hCC'] using hMidB.1
  exact (between_identity C B hCBC).symm

/-- A perpendicular through C and X intersects a nondegenerate base line
at X whenever X is already on that line. -/
theorem tarski_perp_foot_as_perp_at_tarski
    {A B C X : Point}
    (hNoncol : ¬ Col A B C)
    (hX : Col A B X)
    (hPerp : TarskiPerp A B C X) :
    TarskiPerpAt X A B C X := by
  obtain ⟨W, hW⟩ := hPerp
  have hCX : C ≠ X := by
    intro h
    exact hNoncol (by simpa [h] using hX)
  have hWX : W = X :=
    line_intersection_unique_tarski hNoncol hCX
      (col_rotate hW.2.2.1) hX
      (col_rotate hW.2.2.2.1) (col_right C X)
  simpa [hWX] using hW

/-- GeoCoq Ch08 l8_18_uniqueness: the perpendicular foot from C to a
nondegenerate base line is unique.  Two distinct feet would make both
base angles of triangle CXY right, contrary to the Tarski l8_7 lemma. -/
theorem tarski_perpendicular_foot_unique_tarski
    {A B C X Y : Point}
    (hNoncol : ¬ Col A B C)
    (hX : Col A B X)
    (hPX : TarskiPerp A B C X)
    (hY : Col A B Y)
    (hPY : TarskiPerp A B C Y) : X = Y := by
  have hAtX : TarskiPerpAt X A B C X :=
    tarski_perp_foot_as_perp_at_tarski hNoncol hX hPX
  have hAtY : TarskiPerpAt Y A B C Y :=
    tarski_perp_foot_as_perp_at_tarski hNoncol hY hPY
  have hCX_Y : TarskiPer C X Y :=
    tarski_per_swap_legs_tarski
      (hAtX.2.2.2.2 Y C
        (col_rotate (col_rotate hY))
        (Or.inl (bet_start C X)))
  have hCY_X : TarskiPer C Y X :=
    tarski_per_swap_legs_tarski
      (hAtY.2.2.2.2 X C
        (col_rotate (col_rotate hX))
        (Or.inl (bet_start C Y)))
  exact tarski_two_right_angles_endpoint_eq_tarski hCX_Y hCY_X

/-- Perpendicularity at a specified intersection depends only on the two
geometric lines, not on the particular endpoint pairs naming the lines. -/
theorem tarski_perp_at_transport_line_names_tarski
    {X A B C D A' B' C' D' : Point}
    (hPerp : TarskiPerpAt X A B C D)
    (hA'B' : A' ≠ B') (hC'D' : C' ≠ D')
    (hAB : ∀ S : Point, Col A B S ↔ Col A' B' S)
    (hCD : ∀ S : Point, Col C D S ↔ Col C' D' S) :
    TarskiPerpAt X A' B' C' D' := by
  rcases hPerp with ⟨_, _, hXAB, hXCD, hRight⟩
  refine ⟨hA'B', hC'D', ?_, ?_, ?_⟩
  · exact col_rotate (col_rotate ((hAB X).mp (col_rotate hXAB)))
  · exact col_rotate (col_rotate ((hCD X).mp (col_rotate hXCD)))
  · intro U V hU hV
    exact hRight U V
      (col_rotate (col_rotate ((hAB U).mpr (col_rotate hU))))
      (col_rotate (col_rotate ((hCD V).mpr (col_rotate hV))))

/-- Intersection uniqueness also holds when each of two descriptions
chooses different endpoint names for the same pair of perpendicular lines. -/
theorem tarski_perp_intersection_unique_of_same_lines_tarski
    {X Y A B C D A' B' C' D' : Point}
    (hX : TarskiPerpAt X A B C D)
    (hY : TarskiPerpAt Y A' B' C' D')
    (hAB : ∀ S : Point, Col A B S ↔ Col A' B' S)
    (hCD : ∀ S : Point, Col C D S ↔ Col C' D' S) :
    X = Y := by
  have hYA : TarskiPerpAt Y A B C D :=
    tarski_perp_at_transport_line_names_tarski hY
      hX.1 hX.2.1
      (fun S => (hAB S).symm) (fun S => (hCD S).symm)
  exact tarski_perp_at_intersection_unique_tarski hX hYA

/-- GeoCoq Ch08 `per_cong`: a purely Tarski congruence property of two
right triangles with congruent legs.  The proof constructs a reflected
point, applies Krippen to obtain a midpoint on the base, uses uniqueness
of the perpendicular foot, and concludes by the five-segment axiom. -/
theorem tarski_per_cong_tarski
    {A B P R X : Point}
    (hAB : A ≠ B) (hAP : A ≠ P)
    (hPerBAP : TarskiPer B A P)
    (hPerABR : TarskiPer A B R)
    (hAPBR : Cong A P B R)
    (hABX : Col A B X)
    (hPXR : Bet P X R) :
    Cong A R P B := by
  have hBR : B ≠ R := by
    intro h
    have hc : Cong A P B B := by simpa [← h] using hAPBR
    exact hAP (cong_identity A P B hc)
  have hNoncolABR : ¬ Col A B R :=
    tarski_per_noncol_tarski hAB hBR hPerABR
  have hNoPAR : ¬ Col P A R := by
    intro h
    have hPerBAR : TarskiPer B A R :=
      tarski_per_change_third_collinear_tarski
        hPerBAP hAP (col_swap h)
    have hPerRAB : TarskiPer R A B :=
      tarski_per_swap_legs_tarski hPerBAR
    have hPerRBA : TarskiPer R B A :=
      tarski_per_swap_legs_tarski hPerABR
    exact hAB (tarski_two_right_angles_endpoint_eq_tarski
      hPerRAB hPerRBA)
  have hXA : X ≠ A := by
    intro h
    exact hNoPAR (Or.inl (by simpa [h] using hPXR))
  have hAX : A ≠ X := hXA.symm
  have hPerPAX : TarskiPer P A X :=
    tarski_per_change_third_collinear_tarski
      (tarski_per_swap_legs_tarski hPerBAP) hAB hABX
  have hNoPAX : ¬ Col P A X :=
    tarski_per_noncol_tarski hAP.symm hAX hPerPAX
  have hPX : P ≠ X := noncol_ne_first_third hNoPAX
  have hRX : R ≠ X := by
    intro h
    exact hNoncolABR (by simpa [h] using hABX)
  have hXR : X ≠ R := hRX.symm
  obtain ⟨P', hP', _⟩ := mul_reflection_exists_unique A P
  obtain ⟨R', hP'XR', hXR'_XR⟩ :=
    segment_construction P' X X R
  have hXR' : X ≠ R' := by
    intro h
    have heq : X = R :=
      cong_identity X R X (by simpa [← h] using (cong_symm hXR'_XR))
    exact hXR heq
  have hXP : Cong X P X P' :=
    tarski_per_cong_of_reflection_tarski
      (tarski_per_change_first_collinear_tarski
        hPerBAP hAB.symm hABX) hP'
  have hXRcong : Cong X R X R' := cong_symm hXR'_XR
  obtain ⟨M, hM⟩ := midpoint_exists_of_equidistant_station_tarski
    (A := R) (B := R') (C := X) hXRcong
  have hAXM : Bet A X M :=
    krippen_full_tarski hP'XR' hPXR
      (cong_symm hXP) (cong_symm hXRcong)
      (mul_midpoint_reverse hP') (mul_midpoint_reverse hM)
  have hAB_AX : ∀ S : Point, Col A B S ↔ Col A X S :=
    col_line_extensionality_tarski hAB hAX
      (col_left A B) hABX
  have hMAB : Col A B M :=
    (hAB_AX M).mpr (Or.inl hAXM)
  have hMR : M ≠ R := by
    intro h
    exact hNoncolABR (by simpa [h] using hMAB)
  have hMX : M ≠ X := by
    intro hMX
    have hRXR' : Bet R X R' := by
      simpa [hMX] using hM.1
    have hLineXR_XR' :
        ∀ S : Point, Col X R S ↔ Col X R' S :=
      col_line_extensionality_tarski hXR hXR'
        (col_left X R)
        (Or.inr (Or.inr (bet_symm hRXR')))
    have hP_onXR : Col X R P := Or.inr (Or.inr hPXR)
    have hP'_onXR : Col X R P' :=
      (hLineXR_XR' P').mpr (Or.inr (Or.inr hP'XR'))
    have hPP' : P ≠ P' :=
      mul_reflection_distinct hP' hAP
    have hLineXR_PP' :
        ∀ S : Point, Col X R S ↔ Col P P' S :=
      col_line_extensionality_tarski hXR hPP'
        hP_onXR hP'_onXR
    have hA_onXR : Col X R A :=
      (hLineXR_PP' A).mpr
        (Or.inr (Or.inl (bet_symm hP'.1)))
    have hLineXR_PA :
        ∀ S : Point, Col X R S ↔ Col P A S :=
      col_line_extensionality_tarski hXR hAP.symm
        hP_onXR hA_onXR
    exact hNoPAX ((hLineXR_PA X).mp (col_left X R))
  have hPerXMR : TarskiPer X M R :=
    ⟨R', hM, hXRcong⟩
  have hPerpAtM : TarskiPerpAt M A B R M :=
    tarski_perp_at_of_one_right_angle_tarski
      hAB hMR.symm
      (col_rotate (col_rotate hMAB)) (col_left M R)
      (col_rotate (col_rotate hABX))
      (Or.inl (bet_start R M))
      hMX.symm hMR.symm hPerXMR
  have hPerpAtB : TarskiPerpAt B A B R B :=
    tarski_perp_at_of_one_right_angle_tarski
      hAB hBR.symm
      (col_rotate (col_rotate (col_right A B)))
      (col_left B R)
      (Or.inl (bet_start A B))
      (Or.inl (bet_start R B))
      hAB hBR.symm hPerABR
  have hMB : M = B :=
    tarski_perpendicular_foot_unique_tarski
      hNoncolABR hMAB ⟨M, hPerpAtM⟩
      (col_right A B) ⟨B, hPerpAtB⟩
  have hBmid : MulMidpoint B R R' := by
    simpa [hMB] using hM
  exact tarski_per_cong_final_five_segment_tarski
    hPX hPXR hP'XR' hP' hBmid hAPBR hXP hXRcong

/-- Every point on a base line gives a right angle to its perpendicular
through the specified foot.  The foot is nondegenerate and the external
point lies off the base.  All properties follow from the synthetic
perpendicular-at-intersection theorem. -/
theorem tarski_perpendicular_foot_right_all_tarski
    {A B C F : Point}
    (hAB : A ≠ B)
    (hF : Col A B F)
    (hPerp : TarskiPerp A B C F) :
    C ≠ F ∧ ¬ Col A B C ∧
      ∀ U : Point, Col U A B → TarskiPer U F C := by
  obtain ⟨W, hW⟩ := hPerp
  have hCF : C ≠ F := hW.2.1
  have hNoncol : ¬ Col A B C := by
    intro hColC
    obtain ⟨V, hVCF, _, hVoff⟩ :=
      tarski_perp_at_off_first_line_tarski hW
    have hline : ∀ S : Point, Col A B S ↔ Col C F S :=
      col_line_extensionality_tarski hAB hCF hColC hF
    exact hVoff ((hline V).mpr (col_rotate hVCF))
  have hAt : TarskiPerpAt F A B C F :=
    tarski_perp_foot_as_perp_at_tarski hNoncol hF ⟨W, hW⟩
  refine ⟨hCF, hNoncol, ?_⟩
  intro U hU
  exact hAt.2.2.2.2 U C hU (Or.inl (bet_start C F))

/-- GeoCoq Ch08 `midpoint_existence_aux`: construct a midpoint from two
perpendicular rays, a transversal, and a synthetic segment comparison.
The proof joins Pasch, the crossing right-triangle congruence theorem,
and GeoCoq l7_21's opposite-side midpoint criterion. -/
theorem tarski_midpoint_existence_aux_tarski
    {A B P Q T : Point}
    (hAB : A ≠ B)
    (hPerpP : TarskiPerp A B P A)
    (hPerpQ : TarskiPerp A B Q B)
    (hT : Col A B T)
    (hQTP : Bet Q T P)
    (hLe : TarskiSegmentLe A P B Q) :
    ∃ X : Point, MulMidpoint X A B := by
  obtain ⟨hPA, hPoff, hRightP⟩ :=
    tarski_perpendicular_foot_right_all_tarski
      hAB (col_left A B) hPerpP
  obtain ⟨hQB, _, hRightQ⟩ :=
    tarski_perpendicular_foot_right_all_tarski
      hAB (col_right A B) hPerpQ
  obtain ⟨R, X, hBRQ, hAPBR, hABX, hRXP⟩ :=
    tarski_midpoint_aux_pasch_candidate hAB hT hQTP hLe
  have hAP : A ≠ P := hPA.symm
  have hBQ : B ≠ Q := hQB.symm
  have hBR : B ≠ R := by
    intro h
    have hz : Cong A P B B := by
      simpa [← h] using hAPBR
    exact hAP (cong_identity A P B hz)
  have hPerBAP : TarskiPer B A P :=
    hRightP B (col_rotate (col_rotate (col_right A B)))
  have hPerABQ : TarskiPer A B Q :=
    hRightQ A (Or.inl (bet_start A B))
  have hPerABR : TarskiPer A B R :=
    tarski_per_change_third_collinear_tarski
      hPerABQ hBQ (Or.inr (Or.inl (bet_symm hBRQ)))
  have hARPB : Cong A R P B :=
    tarski_per_cong_tarski
      hAB hAP hPerBAP hPerABR
      hAPBR hABX (bet_symm hRXP)
  have hNoncolAPB : ¬ Col A P B := by
    intro h
    exact hPoff (col_swap_last h)
  have hPR : P ≠ R := by
    intro h
    have hPX : P = X :=
      between_identity P X (by simpa [h] using hRXP)
    exact hPoff (by simpa [← hPX] using hABX)
  have hPBRA : Cong P B R A :=
    cong_reverse_right (cong_symm hARPB)
  have hMids : MulMidpoint X A B ∧ MulMidpoint X P R :=
    tarski_l7_21_diagonals_midpoint
      hNoncolAPB hPR hAPBR hPBRA
      (col_swap_last hABX)
      (Or.inl (bet_symm hRXP))
  exact ⟨X, hMids.1⟩

/-- Reversing the named endpoints of the first perpendicular line
preserves the same purely geometric perpendicularity relation. -/
theorem tarski_perp_reverse_base_tarski
    {A B C D : Point}
    (h : TarskiPerp A B C D) :
    TarskiPerp B A C D := by
  obtain ⟨X, hX⟩ := h
  rcases hX with ⟨hAB, hCD, hXAB, hXCD, hRight⟩
  refine ⟨X, hAB.symm, hCD, col_swap_last hXAB, hXCD, ?_⟩
  intro U V hU hV
  exact hRight U V (col_swap_last hU) hV

/-- GeoCoq Ch08 Satz 8.22: every segment admits a midpoint in neutral
Tarski geometry, independently of any parallel axiom, continuity axiom,
coordinate field, or ambient real plane.  Two perpendiculars and Tarski's
segment comparison reduce the claim to the proved Pasch construction. -/
theorem midpoint_existence_tarski (A B : Point) :
    ∃ M : Point, MulMidpoint M A B := by
  by_cases hAB : A = B
  · subst B
    exact ⟨A, bet_start A A, congr_refl A A⟩
  obtain ⟨Q, _, hPerpBAQB, _, _⟩ :=
    gupta_l8_21_tarski (A := B) (B := A) (C := A) (Ne.symm hAB)
  have hPerpABQB : TarskiPerp A B Q B :=
    tarski_perp_reverse_base_tarski hPerpBAQB
  obtain ⟨P, T, hPerpABPA, hTAB, hQTP⟩ :=
    gupta_l8_21_tarski (A := A) (B := B) (C := Q) hAB
  rcases tarski_segment_le_cases A P B Q with hLe | hLe
  · exact tarski_midpoint_existence_aux_tarski
      hAB hPerpABPA hPerpABQB hTAB hQTP hLe
  · obtain ⟨X, hX⟩ :=
      tarski_midpoint_existence_aux_tarski
        (Ne.symm hAB) hPerpBAQB
        (tarski_perp_reverse_base_tarski hPerpABPA)
        (col_swap hTAB) (bet_symm hQTP) hLe
    exact ⟨X, mul_midpoint_reverse hX⟩

/-- Every segment has a point equidistant from both endpoints. This is
constructed from its Tarski midpoint; it is not assumed as an axiom. -/
theorem equidistant_station_exists_tarski (A B : Point) :
    ∃ C : Point, Cong C A C B := by
  obtain ⟨M, hM⟩ := midpoint_existence_tarski A B
  exact ⟨M, hM.2⟩

/-- Through any point outside a nondegenerate line there exists a
parallel line. This is the unconditional Tarski-only construction,
obtained by combining the proved midpoint existence with reflection. -/
theorem parallel_through_off_line_tarski
    {A B P : Point} (hAB : A ≠ B)
    (hPoff : ¬ Col A B P) :
    ∃ Q : Point, Parallel A B P Q := by
  obtain ⟨M, hMid⟩ := midpoint_existence_tarski A P
  exact parallel_through_off_line_of_midpoint_tarski hAB hPoff hMid

/-- The midpoint of any two points exists uniquely.  This is the full
existence-and-uniqueness theorem, with both parts proved from Tarski. -/
theorem midpoint_existsUnique_tarski (A B : Point) :
    ∃! M : Point, MulMidpoint M A B := by
  obtain ⟨M, hM⟩ := midpoint_existence_tarski A B
  exact ⟨M, hM,
    fun N hN => (mul_midpoint_center_unique_tarski hM hN).symm⟩

/-- The parallel through a point outside AB is strictly parallel:
its line is disjoint from AB rather than being the same line. -/
theorem strict_parallel_through_off_line_tarski
    {A B P : Point} (hAB : A ≠ B)
    (hPoff : ¬ Col A B P) :
    ∃ Q : Point, StrictParallel A B P Q := by
  obtain ⟨Q, hPar⟩ := parallel_through_off_line_tarski hAB hPoff
  rcases hPar with ⟨hAB', hPQ, hsame | hdisjoint⟩
  · have hPonAB : Col A B P :=
      (hsame P).mpr (col_left P Q)
    exact False.elim (hPoff hPonAB)
  · exact ⟨Q, hAB', hPQ, hdisjoint⟩

/-- Every point P admits a nondegenerate line through P parallel to AB,
including the case where P already lies on AB. -/
theorem parallel_through_any_point_tarski
    {A B P : Point} (hAB : A ≠ B) :
    ∃ Q : Point, Parallel A B P Q := by
  by_cases hcol : Col A B P
  · by_cases hPA : P = A
    · subst P
      exact ⟨B, parallel_refl hAB⟩
    · have hline : ∀ S : Point, Col A B S ↔ Col P A S :=
        col_line_extensionality_tarski hAB hPA
          hcol (col_left A B)
      exact ⟨A, hAB, hPA, Or.inl hline⟩
  · exact parallel_through_off_line_tarski hAB hcol

/-- After midpoint existence has been derived from Tarski's primitive
axioms, the two internal arithmetic graphs require only the Euclidean
Playfair *uniqueness theorem*.  The parallel-existence hypothesis occurring
in the earlier conditional construction is discharged unconditionally here.
This does not assume either the field laws or an ambient number field. -/
theorem both_operation_graphs_total_of_playfair_tarski
    (f : Frame Point)
    (hplayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ S : Point, Col C D S ↔ Col E F S) :
    AddTotal f ∧ MulTotal f := by
  have hparallel : ∀ A B P : Point, A ≠ B →
      ∃ W : Point, Parallel A B P W := by
    intro A B P hAB
    exact parallel_through_any_point_tarski (A := A) (B := B) (P := P) hAB
  exact both_operation_graphs_total_of_parallel_theorems
    hparallel hplayfair f

/-- Functional as well as total: both geometric operations become
single-valued once the remaining Playfair uniqueness proof is supplied.
No independent functionality or parallel-existence axiom is used. -/
theorem both_operation_graphs_functional_of_playfair_tarski
    (f : Frame Point)
    (hplayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ S : Point, Col C D S ↔ Col E F S) :
    AddFunctional f ∧ MulFunctional f := by
  obtain ⟨hAdd, hMul⟩ :=
    both_operation_graphs_total_of_playfair_tarski f hplayfair
  exact ⟨addFunctional_of_total f hAdd, mulFunctional_of_total f hMul⟩

/-- The geometric multiplication admits an inverse for every nonzero
axis point, once Playfair's line-uniqueness theorem is available.
The inverse is constructed by *reversing both parallel projections*:
first project `I` in direction `Jx` to `OJ`, then project that point
in direction `IJ` to `OI`. No algebraic inverse, field, or coordinates
are used in this proof. -/
theorem mulInverseLaw_of_playfair_tarski
    (f : Frame Point)
    (hplayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ S : Point, Col C D S ↔ Col E F S) :
    MulInverseLaw f := by
  intro x hx
  have hxO : x.1 ≠ f.O := by
    intro h
    exact hx (Subtype.ext h)
  have hJx_not_OJ : ¬ Parallel f.J x.1 f.O f.J := by
    intro hp
    have hsame : ∀ T : Point,
        Col f.J x.1 T ↔ Col f.O f.J T :=
      parallel_same_of_intersection hp
        (col_left f.J x.1) (col_right f.O f.J)
    have hJOx : Col f.O f.J x.1 :=
      (hsame x.1).mp (col_right f.J x.1)
    exact hxO (frame_axes_intersection_only_origin_tarski
      f x.1 x.2 hJOx)
  obtain ⟨U, hJU⟩ :=
    parallel_through_any_point_tarski
      (A := f.J) (B := x.1) (P := f.I)
      (f.J_ne_axis_point x.1 x.2)
  have hIU_not_OJ : ¬ Parallel f.I U f.O f.J := by
    intro hbad
    exact hJx_not_OJ
      (parallel_trans_of_playfair hplayfair hJU hbad)
  obtain ⟨W, hIUW, hWcol⟩ :=
    not_parallel_lines_intersect f.I U f.O f.J
      hJU.2.1 f.O_ne_J hIU_not_OJ
  have hIW : f.I ≠ W := by
    intro heq
    have hIcolOJ : Col f.O f.J f.I := by
      simpa [← heq] using hWcol
    have hIO : f.I = f.O :=
      frame_axes_intersection_only_origin_tarski f f.I
        (col_right f.O f.I) hIcolOJ
    exact f.O_ne_I hIO.symm
  have hlineIW : ∀ T : Point,
      Col f.I U T ↔ Col f.I W T :=
    col_line_extensionality_tarski hJU.2.1 hIW
      (col_left f.I U) hIUW
  have hJI_W : Parallel f.J x.1 f.I W :=
    parallel_retarget_right_of_line_eq hJU hIW hlineIW
  have hWne : W ≠ f.O := by
    intro heq
    have hbad : Parallel f.J x.1 f.I f.O := by
      simpa [heq] using hJI_W
    exact frame_JX_not_parallel_OI f x (parallel_reverse_right hbad)
  have hIJ_not_OI : ¬ Parallel f.I f.J f.O f.I := by
    intro hp
    have hsame : ∀ T : Point,
        Col f.I f.J T ↔ Col f.O f.I T :=
      parallel_same_of_intersection hp
        (col_left f.I f.J) (col_right f.O f.I)
    exact f.noncol ((hsame f.J).mp (col_right f.I f.J))
  obtain ⟨V, hIJWV⟩ :=
    parallel_through_any_point_tarski
      (A := f.I) (B := f.J) (P := W) f.I_ne_J
  have hWV_not_OI : ¬ Parallel W V f.O f.I := by
    intro hbad
    exact hIJ_not_OI
      (parallel_trans_of_playfair hplayfair hIJWV hbad)
  obtain ⟨Y, hWVY, hYcol⟩ :=
    not_parallel_lines_intersect W V f.O f.I
      hIJWV.2.1 f.O_ne_I hWV_not_OI
  have hWY : W ≠ Y := by
    intro heq
    have hWOI : Col f.O f.I W := by
      simpa [heq] using hYcol
    exact hWne (frame_axes_intersection_only_origin_tarski
      f W hWOI hWcol)
  have hlineWY : ∀ T : Point,
      Col W V T ↔ Col W Y T :=
    col_line_extensionality_tarski hIJWV.2.1 hWY
      (col_left W V) hWVY
  have hIJWY : Parallel f.I f.J W Y :=
    parallel_retarget_right_of_line_eq hIJWV hWY hlineWY
  have hIJYW : Parallel f.I f.J Y W :=
    parallel_reverse_right hIJWY
  have hYne : Y ≠ f.O := by
    intro heq
    have hIJOW : Parallel f.I f.J f.O W := by
      simpa [heq] using hIJYW
    have hlineOW : ∀ T : Point,
        Col f.O W T ↔ Col f.O f.J T := by
      intro T
      exact (col_line_extensionality_tarski
        f.O_ne_J hWne.symm (col_left f.O f.J) hWcol T).symm
    have hIJ_OJ : Parallel f.I f.J f.O f.J :=
      parallel_retarget_right_of_line_eq hIJOW f.O_ne_J hlineOW
    exact frame_IJ_not_parallel_OJ f hIJ_OJ
  let y : AxisPoint f := ⟨Y, hYcol⟩
  refine ⟨y, Or.inr ⟨hYne, W, hWcol, hIJYW, ?_⟩⟩
  exact parallel_reverse_right hJI_W

/-- The complete geometric *existence, uniqueness, unit and inverse*
package for multiplication, all derived from the Tarski frame and
the one remaining synthetic Playfair uniqueness statement. -/
theorem mulKernel_of_playfair_tarski
    (f : Frame Point)
    (hplayfair : ∀ A B C D E F P : Point,
      Parallel A B C D → Parallel A B E F →
      Col C D P → Col E F P →
      ∀ S : Point, Col C D S ↔ Col E F S) :
    MulTotal f ∧ MulFunctional f ∧
      MulLeftOneLaw f ∧ MulInverseLaw f := by
  obtain ⟨_, hMul⟩ :=
    both_operation_graphs_total_of_playfair_tarski f hplayfair
  exact ⟨hMul,
    mulFunctional_of_total f hMul,
    mulLeftOne_of_mulTotal f hMul,
    mulInverseLaw_of_playfair_tarski f hplayfair⟩

/-- GeoCoq Ch09 `l9_3`, reconstructed directly using Tarski's `inner_pasch`.
The given midpoint is already a crossing of `AC` with `PQ`, so the
additional identification of an arbitrary TS witness is unnecessary.
This lemma uses neither a side-of-line axiom nor Euclid, coordinates,
or the continuity scheme. -/
theorem oppositeSides_ray_replace_of_midpoint_tarski
    {P Q A C M R B : Point}
    (hTS : OppositeSides P Q A C)
    (hM : Col P Q M) (hMid : MulMidpoint M A C)
    (hR : Col P Q R) (hOut : Out R A B) :
    OppositeSides P Q B C := by
  have hPQ : P ≠ Q := by
    intro h
    subst Q
    exact hTS.1 (Or.inl (bet_start P A))
  have hBoff : ¬ Col P Q B := by
    intro hBcol
    have hline : ∀ T : Point, Col P Q T ↔ Col R B T :=
      col_line_extensionality_tarski hPQ hOut.2.1.symm hR hBcol
    exact hTS.1 ((hline A).mpr (col_swap_last (out_implies_col hOut)))
  rcases hOut.2.2 with hRAB | hRBA
  · obtain ⟨Bp, hBp, _⟩ := mul_reflection_exists_unique M B
    obtain ⟨Rp, hRp, _⟩ := mul_reflection_exists_unique M R
    have hBCR : Bet Bp C Rp :=
      mul_reflection_preserves_bet hBp hMid hRp (bet_symm hRAB)
    obtain ⟨X, hMXRp, hCXB⟩ :=
      inner_pasch B Rp Bp M C hBp.1 (bet_symm hBCR)
    have hRpcol : Col P Q Rp := by
      by_cases hRM : R = M
      · subst R
        have hMRp : M = Rp :=
          cong_identity M Rp M (cong_symm hRp.2)
        simpa [← hMRp] using hM
      · have hline : ∀ T : Point, Col P Q T ↔ Col R M T :=
          col_line_extensionality_tarski hPQ hRM hR hM
        exact (hline Rp).mpr (Or.inl hRp.1)
    exact ⟨hBoff, hTS.2.1, X,
      col_segment_closed_tarski hPQ hM hRpcol hMXRp,
      bet_symm hCXB⟩
  · obtain ⟨X, hBXC, hMXR⟩ :=
      inner_pasch R C A B M hRBA (bet_symm hMid.1)
    exact ⟨hBoff, hTS.2.1, X,
      col_segment_closed_tarski hPQ hM hR hMXR, hBXC⟩

/-- The ray relation is symmetric in its two non-origin points. -/
theorem out_swap_tarski {O A B : Point}
    (h : Out O A B) : Out O B A := by
  rcases h with ⟨hAO, hBO, hAB | hBA⟩
  · exact ⟨hBO, hAO, Or.inr hAB⟩
  · exact ⟨hBO, hAO, Or.inl hBA⟩

/-- Every non-origin point is on its own strict ray. -/
theorem out_self_tarski {O A : Point} (hAO : A ≠ O) :
    Out O A A :=
  ⟨hAO, hAO, Or.inl (bet_end O A)⟩

/-- Ray transitivity (GeoCoq Ch06 `l6_7`) reconstructed from the
previously established Ch05 totality of betweenness.  The four possible
orders of the two input rays are handled without any side-of-line or
parallel axiom. -/
theorem out_trans_tarski {O A B C : Point}
    (hAB : Out O A B) (hBC : Out O B C) : Out O A C := by
  rcases hAB with ⟨hAO, hBO, hOAB | hOBA⟩
  · rcases hBC with ⟨_, hCO, hOBC | hOCB⟩
    · exact ⟨hAO, hCO, Or.inl (bet_extend hOAB hOBC)⟩
    · rcases bet_internal_totality hOAB hOCB with hOAC | hOCA
      · exact ⟨hAO, hCO, Or.inl hOAC⟩
      · exact ⟨hAO, hCO, Or.inr hOCA⟩
  · rcases hBC with ⟨_, hCO, hOBC | hOCB⟩
    · rcases ray_bet_comparable_tarski hBO.symm hOBA hOBC with
        hOAC | hOCA
      · exact ⟨hAO, hCO, Or.inl hOAC⟩
      · exact ⟨hAO, hCO, Or.inr hOCA⟩
    · exact ⟨hAO, hCO, Or.inr (bet_extend hOCB hOBA)⟩

/-- Moving a named point inward along a nondegenerate ray does not change
that ray.  This is exactly the branch-sensitive Ch05 fact required for the
`l9_4_1_aux` comparison, now packaged as an iff. -/
theorem out_iff_of_between_target_tarski {O D A U : Point}
    (hODA : Bet O D A) (hOD : O ≠ D) :
    Out O U A ↔ Out O U D := by
  have hOA : O ≠ A := by
    intro h
    have hOD' : O = D :=
      between_identity O D (by simpa [← h] using hODA)
    exact hOD hOD'
  have hDA : Out O D A :=
    ⟨hOD.symm, hOA.symm, Or.inl hODA⟩
  constructor
  · intro h
    exact out_trans_tarski h (out_swap_tarski hDA)
  · intro h
    exact out_trans_tarski h hDA

/-- A point reflection carries *strict* rays to strict rays.  Nondegenerate
ray endpoints are preserved using Tarski congruence identity, while the two
possible betweenness orders are transported by the reflection theorem. -/
theorem out_reflection_preserves_tarski
    {M O A B O' A' B' : Point}
    (hO : MulMidpoint M O O')
    (hA : MulMidpoint M A A')
    (hB : MulMidpoint M B B')
    (hOut : Out O A B) : Out O' A' B' := by
  have hOA : Cong O A O' A' :=
    mul_reflection_preserves_cong
      (mul_midpoint_reverse hO) (mul_midpoint_reverse hA)
  have hOB : Cong O B O' B' :=
    mul_reflection_preserves_cong
      (mul_midpoint_reverse hO) (mul_midpoint_reverse hB)
  have hA'O' : A' ≠ O' := by
    intro h
    have heq : O = A :=
      cong_identity O A O' (by simpa [h] using hOA)
    exact hOut.1 heq.symm
  have hB'O' : B' ≠ O' := by
    intro h
    have heq : O = B :=
      cong_identity O B O' (by simpa [h] using hOB)
    exact hOut.2.1 heq.symm
  refine ⟨hA'O', hB'O', ?_⟩
  rcases hOut.2.2 with hOAB | hOBA
  · exact Or.inl (mul_reflection_preserves_bet hO hA hB hOAB)
  · exact Or.inr (mul_reflection_preserves_bet hO hB hA hOBA)

/-- The nondegenerate branch of GeoCoq Ch09 `l9_4_1_aux` is a ray theorem
once the two midpoint pairs have been obtained by the right-angle
crossing lemma `l8_24`.  In particular, the comparison point D may be
strictly between R and A: substituting D for A is justified by the
proved ray-target equivalence, not by silently changing an endpoint. -/
theorem out_transport_of_crossing_midpoints_tarski
    {M R S D C U C' A : Point}
    (hRS : MulMidpoint M R S)
    (hDC : MulMidpoint M D C)
    (hUC' : MulMidpoint M U C')
    (hRDA : Bet R D A) (hRD : R ≠ D) :
    Out R U A ↔ Out S C C' := by
  rw [out_iff_of_between_target_tarski hRDA hRD]
  constructor
  · intro h
    have h' : Out S C' C :=
      out_reflection_preserves_tarski hRS hUC' hDC h
    exact out_swap_tarski h'
  · intro h
    have h' : Out S C' C := out_swap_tarski h
    exact out_reflection_preserves_tarski
      (mul_midpoint_reverse hRS)
      (mul_midpoint_reverse hUC')
      (mul_midpoint_reverse hDC) h'

/-- The coincident-foot branch of GeoCoq Ch09 `l9_4_1_aux`, stated at
its exact neutral-geometry interface: A and C lie on opposite rays from
R, while U and V are a point-reflected pair with center R.  The equivalence
uses Ch05 ray comparability and reflection rather than any angle measure. -/
theorem out_opposite_midpoint_transport_tarski
    {R A C U V : Point}
    (hARC : Bet A R C) (hRA : R ≠ A) (hRC : R ≠ C)
    (hMid : MulMidpoint R U V) :
    Out R U A ↔ Out R C V := by
  obtain ⟨E, hAE, _⟩ := mul_reflection_exists_unique R A
  have hAEne : A ≠ E := mul_reflection_distinct hAE hRA
  have hRE : R ≠ E := mul_midpoint_center_ne_right hAE hAEne
  have hEC : Out R E C := by
    rcases ray_bet_comparable_after_station hRA.symm hAE.1 hARC with
        hREC | hRCE
    · exact ⟨hRE.symm, hRC.symm, Or.inl hREC⟩
    · exact ⟨hRE.symm, hRC.symm, Or.inr hRCE⟩
  have hRR : MulMidpoint R R R :=
    ⟨bet_start R R, congr_refl R R⟩
  constructor
  · intro h
    have hVE : Out R V E :=
      out_reflection_preserves_tarski hRR hMid hAE h
    exact out_swap_tarski (out_trans_tarski hVE hEC)
  · intro h
    have hVE : Out R V E :=
      out_trans_tarski (out_swap_tarski h) (out_swap_tarski hEC)
    exact out_reflection_preserves_tarski hRR
      (mul_midpoint_reverse hMid) (mul_midpoint_reverse hAE) hVE

/-- Points on the two strict rays cut by an interval A--R--C keep R
between them.  All four weak-betweenness branches are discharged by
Ch03/Ch05 lemmas already derived from Tarski Pasch. -/
theorem out_out_crosses_origin_tarski
    {R A C U V : Point}
    (hARC : Bet A R C)
    (hUA : Out R U A) (hVC : Out R V C) :
    Bet U R V := by
  have hURC : Bet U R C := by
    rcases hUA.2.2 with hRUA | hRAU
    · exact bet_exchange (bet_symm hRUA) hARC
    · exact bet_outer_trans (bet_symm hRAU) hARC hUA.2.1
  rcases hVC.2.2 with hRVC | hRCV
  · exact bet_inner_trans hURC hRVC
  · exact bet_extend hURC (bet_outer_trans hURC hRCV (Ne.symm hVC.2.1))

/-- GeoCoq Ch08 `l8_6`: if C lies between A and D and both AC and DC
make right angles at B with BC, then the vertex B coincides with C.
The argument compares the two reflections of C about B, and does not
invoke angle arithmetic or line separation. -/
theorem right_angle_crossing_vertex_tarski
    {A B C D : Point}
    (hPerA : TarskiPer A B C)
    (hPerD : TarskiPer D B C)
    (hACD : Bet A C D) : B = C := by
  by_cases hAD : A = D
  · subst D
    have hAC : A = C := between_identity A C hACD
    subst A
    rcases tarski_per_collinear_legs_degenerate_tarski
        hPerA (col_left C B) with h | h
    · exact h.symm
    · exact h.symm
  · obtain ⟨C', hMid, hAC⟩ := hPerA
    obtain ⟨C'', hMid', hDC⟩ := hPerD
    obtain ⟨Z, _, huniq⟩ := mul_reflection_exists_unique B C
    have hEq : C' = C'' :=
      (huniq C' hMid).trans (huniq C'' hMid').symm
    have hDCC' : Cong D C D C' := by
      simpa only [← hEq] using hDC
    have hCol : Col A D C := Or.inr (Or.inl (bet_symm hACD))
    have hCC' : Cong C C C C' :=
      col_equidistant_of_two_stations hAD hCol hAC hDCC'
    have hCEq : C = C' :=
      cong_identity C C' C (cong_symm hCC')
    have hCBC : Bet C B C := by
      simpa only [← hCEq] using hMid.1
    exact (between_identity C B hCBC).symm

/-- If the endpoints on opposite sides of a Tarski line have the same
perpendicular foot R, their crossing of that line is *exactly R*.
The vertex is forced by the just-proved l8_6 analogue, not by an
analytic orthogonal projection or a separated-side axiom. -/
theorem oppositeSides_common_perpendicular_foot_tarski
    {P Q A C R : Point}
    (hTS : OppositeSides P Q A C)
    (hR : Col P Q R)
    (hPerA : TarskiPerp P Q A R)
    (hPerC : TarskiPerp P Q C R) :
    Bet A R C := by
  have hPQ : P ≠ Q := noncol_ne_first_second hTS.1
  obtain ⟨T, hT, hATC⟩ := hTS.2.2
  obtain ⟨_, _, hRightA⟩ :=
    tarski_perpendicular_foot_right_all_tarski hPQ hR hPerA
  obtain ⟨_, _, hRightC⟩ :=
    tarski_perpendicular_foot_right_all_tarski hPQ hR hPerC
  have hTPQ : Col T P Q := col_rotate (col_rotate hT)
  have hPerART : TarskiPer A R T :=
    tarski_per_swap_legs_tarski (hRightA T hTPQ)
  have hPerCRT : TarskiPer C R T :=
    tarski_per_swap_legs_tarski (hRightC T hTPQ)
  have hRT : R = T :=
    right_angle_crossing_vertex_tarski hPerART hPerCRT hATC
  simpa only [← hRT] using hATC

/-- Opposite sides are preserved when each endpoint is moved anywhere
along its own strict ray from the *known* crossing R.  Unlike the general
`l9_5`, the crossing point is supplied; no hidden line-separation theorem
is used. -/
theorem oppositeSides_transport_rays_crossing_tarski
    {P Q A C R U V : Point}
    (hTS : OppositeSides P Q A C)
    (hR : Col P Q R)
    (hARC : Bet A R C)
    (hUA : Out R U A) (hVC : Out R V C) :
    OppositeSides P Q U V := by
  have hPQ : P ≠ Q := noncol_ne_first_second hTS.1
  have hUoff : ¬ Col P Q U := by
    intro hUbase
    have hline : ∀ Z : Point, Col P Q Z ↔ Col R U Z :=
      col_line_extensionality_tarski
        hPQ hUA.1.symm hR hUbase
    exact hTS.1 ((hline A).mpr (out_implies_col hUA))
  have hVoff : ¬ Col P Q V := by
    intro hVbase
    have hline : ∀ Z : Point, Col P Q Z ↔ Col R V Z :=
      col_line_extensionality_tarski
        hPQ hVC.1.symm hR hVbase
    exact hTS.2.1 ((hline C).mpr (out_implies_col hVC))
  exact ⟨hUoff, hVoff, R, hR,
    out_out_crosses_origin_tarski hARC hUA hVC⟩

/-- GeoCoq Ch09 `l9_4_2_aux`, complete coincident-foot branch. -/
theorem oppositeSides_samefoot_perp_ray_tarski
    {P Q A C R U V : Point}
    (hTS : OppositeSides P Q A C)
    (hR : Col P Q R)
    (hPerA : TarskiPerp P Q A R)
    (hPerC : TarskiPerp P Q C R)
    (hUA : Out R U A) (hVC : Out R V C) :
    OppositeSides P Q U V := by
  exact oppositeSides_transport_rays_crossing_tarski
    hTS hR
    (oppositeSides_common_perpendicular_foot_tarski
      hTS hR hPerA hPerC)
    hUA hVC

/-- Replacing the endpoint names of a nondegenerate base line changes
neither its opposite-side relation nor the crossing witness. -/
theorem oppositeSides_change_base_iff_tarski
    {P Q R S U V : Point}
    (hPQ : P ≠ Q) (hRS : R ≠ S)
    (hR : Col P Q R) (hS : Col P Q S) :
    OppositeSides P Q U V ↔ OppositeSides R S U V := by
  have hline : ∀ Z : Point, Col P Q Z ↔ Col R S Z :=
    col_line_extensionality_tarski hPQ hRS hR hS
  constructor
  · rintro ⟨hUoff, hVoff, T, hT, hUTV⟩
    exact ⟨(fun hz => hUoff ((hline U).mpr hz)),
      (fun hz => hVoff ((hline V).mpr hz)),
      T, (hline T).mp hT, hUTV⟩
  · rintro ⟨hUoff, hVoff, T, hT, hUTV⟩
    exact ⟨(fun hz => hUoff ((hline U).mp hz)),
      (fun hz => hVoff ((hline V).mp hz)),
      T, (hline T).mpr hT, hUTV⟩

/-- Perpendicularity is invariant when the first named line is replaced
by another pair of distinct points on the same Tarski line. -/
theorem perpendicular_change_base_tarski
    {P Q R S A F : Point}
    (hPQ : P ≠ Q) (hRS : R ≠ S)
    (hR : Col P Q R) (hS : Col P Q S)
    (hPerp : TarskiPerp P Q A F) :
    TarskiPerp R S A F := by
  obtain ⟨W, hAt⟩ := hPerp
  have hline : ∀ Z : Point, Col P Q Z ↔ Col R S Z :=
    col_line_extensionality_tarski hPQ hRS hR hS
  exact ⟨W, tarski_perp_at_transport_line_names_tarski
    hAt hRS hAt.2.1 hline (fun _ => Iff.rfl)⟩

/-- The second perpendicular line can likewise be renamed when its
endpoint is moved to another non-foot point on the original line. -/
theorem perpendicular_change_second_endpoint_tarski
    {P Q C F D : Point}
    (hCF : C ≠ F) (hDF : D ≠ F)
    (hCol : Col C F D)
    (hPerp : TarskiPerp P Q C F) :
    TarskiPerp P Q D F := by
  obtain ⟨W, hAt⟩ := hPerp
  have hline : ∀ Z : Point, Col C F Z ↔ Col D F Z :=
    col_line_extensionality_tarski
      hCF hDF hCol (col_right C F)
  exact ⟨W, tarski_perp_at_transport_line_names_tarski
    hAt hAt.1 hDF (fun _ => Iff.rfl) hline⟩

/- The full GeoCoq Ch09 `l9_4_1_aux` ray correspondence: the reflected
auxiliary point and the two perpendicular feet determine the same strict
ray relation.  The R=S branch is l8_6 plus the opposite-midpoint ray
lemma; the R≠S branch is the proved l8_24 construction followed by strict
ray transfer under central reflection. -/
/-- Degenerate midpoint: if a point bisects RR, it is R. -/
theorem midpoint_same_endpoint_tarski {M R : Point}
    (h : MulMidpoint M R R) : M = R :=
  (between_identity R M h.1).symm

/-- The exact inner-Pasch crossing in GeoCoq Ch08 `l8_24`.
Its result is an incidence intersection, *before* any right-angle
congruence or common-midpoint conclusion.  It uses neither coordinates,
an existing field, Euclid's postulate, nor continuity. -/
theorem midpoint_perp_crossing_pasch_tarski
    {S R C A C' T : Point}
    (hSR : S ≠ R)
    (hT : Col S R T)
    (hCross : Bet C T A)
    (hC' : Bet R C' A) :
    ∃ X : Point, Col S R X ∧ Col C C' X ∧
      Bet T X R ∧ Bet C' X C := by
  obtain ⟨X, hTXR, hC'XC⟩ :=
    inner_pasch C R A T C' hCross hC'
  exact ⟨X,
    col_segment_closed_tarski hSR hT (col_right S R) hTXR,
    Or.inr (Or.inl hC'XC), hTXR, hC'XC⟩

/-- GeoCoq Ch08 `l8_24`: equal perpendicular legs, a transversal crossing,
and an internally copied leg force a *common midpoint* of the base segment
and the transversal's opposite-side segment.  Its two essential ingredients
are the previously established neutral-Tarski right-triangle congruence
(`tarski_per_cong_tarski`) and diagonal-midpoint criterion (`l7_21`). -/
theorem perpendicular_crossing_common_midpoint_tarski
    {S R C A C' T : Point}
    (hPerC : TarskiPerp C S S R)
    (hPerA : TarskiPerp A R S R)
    (hT : Col S R T)
    (hCTA : Bet C T A)
    (hRC'A : Bet R C' A)
    (hCong : Cong S C R C') :
    ∃ M : Point, MulMidpoint M S R ∧ MulMidpoint M C C' := by
  obtain ⟨W, hAt⟩ := hPerC
  have hSR : S ≠ R := hAt.2.1
  have hPerSRCS : TarskiPerp S R C S :=
    tarski_perp_swap_lines_tarski ⟨W, hAt⟩
  obtain ⟨hCS, hCoff, hRightC⟩ :=
    tarski_perpendicular_foot_right_all_tarski
      hSR (col_left S R) hPerSRCS
  have hPerSRAR : TarskiPerp S R A R :=
    tarski_perp_swap_lines_tarski hPerA
  obtain ⟨hAR, _, hRightA⟩ :=
    tarski_perpendicular_foot_right_all_tarski
      hSR (col_right S R) hPerSRAR
  obtain ⟨X, hSX, hCX, hTXR, hC'XC⟩ :=
    midpoint_perp_crossing_pasch_tarski hSR hT hCTA hRC'A
  have hPerRSC : TarskiPer R S C :=
    hRightC R (col_left R S)
  have hPerSRA : TarskiPer S R A :=
    hRightA S (col_swap_last (col_left S R))
  have hRC'Acol : Col R A C' :=
    Or.inr (Or.inl (bet_symm hRC'A))
  have hPerSRC' : TarskiPer S R C' :=
    tarski_per_change_third_collinear_tarski
      hPerSRA hAR.symm hRC'Acol
  have hCXC' : Bet C X C' := bet_symm hC'XC
  have hSC'_CR : Cong S C' C R :=
    tarski_per_cong_tarski
      hSR hCS.symm hPerRSC hPerSRC' hCong hSX hCXC'
  have hCR_C'S : Cong C R C' S :=
    cong_reverse_right (cong_symm hSC'_CR)
  have hNoncolSCR : ¬ Col S C R := by
    intro h
    exact hCoff (col_swap_last h)
  have hCC' : C ≠ C' := by
    intro h
    have hCX : C = X :=
      between_identity C X (by simpa [← h] using hCXC')
    exact hCoff (by simpa [← hCX] using hSX)
  have hM := tarski_l7_21_diagonals_midpoint
    hNoncolSCR hCC' hCong hCR_C'S
    (col_swap_last hSX) (Or.inl hCXC')
  exact ⟨X, hM.1, hM.2⟩

theorem perpendicular_midpoint_ray_transport_aux_tarski
    {P Q A C R S M U C' : Point}
    (hLe : TarskiSegmentLe S C R A)
    (hTS : OppositeSides P Q A C)
    (hR : Col P Q R) (hPerA : TarskiPerp P Q A R)
    (hS : Col P Q S) (hPerC : TarskiPerp P Q C S)
    (hMidRS : MulMidpoint M R S)
    (hMidUC' : MulMidpoint M U C') :
    Out R U A ↔ Out S C C' := by
  by_cases hRS : R = S
  · subst S
    have hMR : M = R := midpoint_same_endpoint_tarski hMidRS
    subst M
    have hARC : Bet A R C :=
      oppositeSides_common_perpendicular_foot_tarski
        hTS hR hPerA hPerC
    have hRA : R ≠ A := by
      intro h
      exact hTS.1 (by simpa [← h] using hR)
    have hRC : R ≠ C := by
      intro h
      exact hTS.2.1 (by simpa [← h] using hR)
    exact out_opposite_midpoint_transport_tarski
      hARC hRA hRC hMidUC'
  · have hPQ : P ≠ Q := noncol_ne_first_second hTS.1
    have hSR : S ≠ R := Ne.symm hRS
    obtain ⟨D, hRDA, hSCD⟩ := hLe
    have hRD : R ≠ D := by
      intro h
      have hSC : S = C :=
        cong_identity S C R (by simpa [← h] using hSCD)
      exact hTS.2.1 (by simpa [← hSC] using hS)
    have hTS' : OppositeSides S R A C :=
      (oppositeSides_change_base_iff_tarski
        hPQ hSR hS hR).mp hTS
    obtain ⟨T, hT, hATC⟩ := hTS'.2.2
    have hPerSRAR : TarskiPerp S R A R :=
      perpendicular_change_base_tarski hPQ hSR hS hR hPerA
    have hPerSRCS : TarskiPerp S R C S :=
      perpendicular_change_base_tarski hPQ hSR hS hR hPerC
    obtain ⟨M', hM'SR, hM'CD⟩ :=
      perpendicular_crossing_common_midpoint_tarski
        (tarski_perp_swap_lines_tarski hPerSRCS)
        (tarski_perp_swap_lines_tarski hPerSRAR)
        hT (bet_symm hATC) hRDA hSCD
    have hMM' : M = M' :=
      mul_midpoint_center_unique_tarski
        (mul_midpoint_reverse hMidRS) hM'SR
    have hMCD : MulMidpoint M C D := by
      simpa only [← hMM'] using hM'CD
    exact out_transport_of_crossing_midpoints_tarski
      hMidRS (mul_midpoint_reverse hMCD) hMidUC' hRDA hRD

/-- GeoCoq Ch09 `l9_4_1`, removing the length-comparison assumption by
the synthetic segment-order dichotomy and symmetry of opposite sides. -/
theorem perpendicular_midpoint_ray_transport_tarski
    {P Q A C R S M U C' : Point}
    (hTS : OppositeSides P Q A C)
    (hR : Col P Q R) (hPerA : TarskiPerp P Q A R)
    (hS : Col P Q S) (hPerC : TarskiPerp P Q C S)
    (hMidRS : MulMidpoint M R S)
    (hMidUC' : MulMidpoint M U C') :
    Out R U A ↔ Out S C C' := by
  rcases tarski_segment_le_cases S C R A with hLe | hLe
  · exact perpendicular_midpoint_ray_transport_aux_tarski
      hLe hTS hR hPerA hS hPerC hMidRS hMidUC'
  · have hRev : Out S C' C ↔ Out R A U :=
      perpendicular_midpoint_ray_transport_aux_tarski
        hLe (oppositeSides_symm_tarski hTS)
        hS hPerC hR hPerA
        (mul_midpoint_reverse hMidRS)
        (mul_midpoint_reverse hMidUC')
    constructor
    · intro hRU
      exact out_swap_tarski (hRev.mpr (out_swap_tarski hRU))
    · intro hSC
      exact out_swap_tarski (hRev.mp (out_swap_tarski hSC))

/-- Moving from an off-line point A along a strict ray whose origin lies
on the base never enters the base line. -/
theorem out_endpoint_off_base_tarski
    {P Q O A U : Point}
    (hPQ : P ≠ Q) (hO : Col P Q O)
    (hAoff : ¬ Col P Q A) (hOut : Out O U A) :
    ¬ Col P Q U := by
  intro hU
  have hline : ∀ Z : Point, Col P Q Z ↔ Col O U Z :=
    col_line_extensionality_tarski hPQ hOut.1.symm hO hU
  exact hAoff ((hline A).mpr (out_implies_col hOut))

/-- A midpoint centered on the base line makes its two off-line
endpoints opposite-sided, by the existing Tarski betweenness witness. -/
theorem oppositeSides_midpoint_crossing_tarski
    {R S M U V : Point}
    (hRS : R ≠ S) (hM : Col R S M)
    (hMid : MulMidpoint M U V)
    (hUoff : ¬ Col R S U) :
    OppositeSides R S U V := by
  have hUM : U ≠ M := by
    intro h
    exact hUoff (by simpa [h] using hM)
  have hUV : U ≠ V :=
    mul_reflection_distinct hMid hUM.symm
  have hMV : M ≠ V :=
    mul_midpoint_center_ne_right hMid hUV
  have hVoff : ¬ Col R S V := by
    intro hVbase
    have hline : ∀ Z : Point, Col R S Z ↔ Col M V Z :=
      col_line_extensionality_tarski hRS hMV hM hVbase
    exact hUoff ((hline U).mpr (Or.inr (Or.inr hMid.1)))
  exact ⟨hUoff, hVoff, M, hM, hMid.1⟩

/-- GeoCoq Ch09 `l9_4_2_aux`, from perpendicular feet and two rays to
the preservation of opposite sides.  This is the full segment-comparison
branch; its proof invokes only `l8_24`, `l9_4_1`, `l9_3` and prior neutral
Tarski geometry.  In particular it does not use the later `l9_5`. -/
theorem two_sides_perp_ray_transport_aux_tarski
    {P Q A C R S U V : Point}
    (hLe : TarskiSegmentLe S C R A)
    (hTS : OppositeSides P Q A C)
    (hR : Col P Q R) (hPerA : TarskiPerp P Q A R)
    (hS : Col P Q S) (hPerC : TarskiPerp P Q C S)
    (hU : Out R U A) (hV : Out S V C) :
    OppositeSides P Q U V := by
  by_cases hRS : R = S
  · subst S
    exact oppositeSides_samefoot_perp_ray_tarski
      hTS hR hPerA hPerC hU hV
  · have hPQ : P ≠ Q := noncol_ne_first_second hTS.1
    have hSR : S ≠ R := Ne.symm hRS
    obtain ⟨D, hRDA, hSCD⟩ := hLe
    have hTSsr : OppositeSides S R A C :=
      (oppositeSides_change_base_iff_tarski
        hPQ hSR hS hR).mp hTS
    obtain ⟨T, hT, hATC⟩ := hTSsr.2.2
    have hPerSRAR : TarskiPerp S R A R :=
      perpendicular_change_base_tarski hPQ hSR hS hR hPerA
    have hPerSRCS : TarskiPerp S R C S :=
      perpendicular_change_base_tarski hPQ hSR hS hR hPerC
    obtain ⟨M, hMSR, _hMCD⟩ :=
      perpendicular_crossing_common_midpoint_tarski
        (tarski_perp_swap_lines_tarski hPerSRCS)
        (tarski_perp_swap_lines_tarski hPerSRAR)
        hT (bet_symm hATC) hRDA hSCD
    obtain ⟨U', hMUU', _⟩ := mul_reflection_exists_unique M U
    have hUoff : ¬ Col S R U :=
      out_endpoint_off_base_tarski hSR (col_right S R)
        hTSsr.1 hU
    have hMline : Col S R M :=
      Or.inr (Or.inl (bet_symm hMSR.1))
    have hTU_U' : OppositeSides S R U U' :=
      oppositeSides_midpoint_crossing_tarski
        hSR hMline hMUU' hUoff
    have hOutSCU' : Out S C U' :=
      (perpendicular_midpoint_ray_transport_tarski
        hTS hR hPerA hS hPerC
        (mul_midpoint_reverse hMSR) hMUU').mp hU
    have hOutSU'V : Out S U' V :=
      out_trans_tarski (out_swap_tarski hOutSCU')
        (out_swap_tarski hV)
    have hTVU : OppositeSides S R V U :=
      oppositeSides_ray_replace_of_midpoint_tarski
        (oppositeSides_symm_tarski hTU_U')
        hMline (mul_midpoint_reverse hMUU')
        (col_left S R) hOutSU'V
    exact (oppositeSides_change_base_iff_tarski
      hPQ hSR hS hR).mpr (oppositeSides_symm_tarski hTVU)

/-- GeoCoq Ch09 `l9_4_2`: the two ray replacements preserve opposite
sides without any length-order hypothesis, by synthetic comparison. -/
theorem two_sides_perp_ray_transport_tarski
    {P Q A C R S U V : Point}
    (hTS : OppositeSides P Q A C)
    (hR : Col P Q R) (hPerA : TarskiPerp P Q A R)
    (hS : Col P Q S) (hPerC : TarskiPerp P Q C S)
    (hU : Out R U A) (hV : Out S V C) :
    OppositeSides P Q U V := by
  rcases tarski_segment_le_cases S C R A with hLe | hLe
  · exact two_sides_perp_ray_transport_aux_tarski
      hLe hTS hR hPerA hS hPerC hU hV
  · exact oppositeSides_symm_tarski
      (two_sides_perp_ray_transport_aux_tarski
        hLe (oppositeSides_symm_tarski hTS)
        hS hPerC hR hPerA hV hU)

/-- GeoCoq Ch09 `l9_5`: moving one endpoint on its strict ray from a
point of the separating line preserves the opposite-side condition.
The proof is fully synthetic: project A,C,B perpendicularly to the
base, reflect A about the midpoint of the first two feet, apply l9_4_1
and l9_4_2 twice, and apply l9_3 once.  None of these lemmas depends on
this theorem or on outer Pasch. -/
theorem oppositeSides_ray_replace_tarski
    {P Q A C R B : Point}
    (hTS : OppositeSides P Q A C)
    (hR : Col P Q R)
    (hOut : Out R A B) :
    OppositeSides P Q B C := by
  have hPQ : P ≠ Q := noncol_ne_first_second hTS.1
  have hBoff : ¬ Col P Q B :=
    out_endpoint_off_base_tarski hPQ hR hTS.1
      (out_swap_tarski hOut)
  obtain ⟨A0, hA0, hPerA⟩ :=
    perpendicular_foot_exists_tarski hTS.1
  obtain ⟨C0, hC0, hPerC⟩ :=
    perpendicular_foot_exists_tarski hTS.2.1
  obtain ⟨B0, hB0, hPerB⟩ :=
    perpendicular_foot_exists_tarski hBoff
  obtain ⟨M, hMidFt⟩ := midpoint_existence_tarski A0 C0
  obtain ⟨D, hMidAD, _⟩ := mul_reflection_exists_unique M A
  have hMline : Col P Q M :=
    col_segment_closed_tarski hPQ hA0 hC0 hMidFt.1
  have hAA0 : A ≠ A0 := by
    intro h
    exact hTS.1 (by simpa [h] using hA0)
  have hCC0 : C ≠ C0 := by
    intro h
    exact hTS.2.1 (by simpa [h] using hC0)
  have hBB0 : B ≠ B0 := by
    intro h
    exact hBoff (by simpa [h] using hB0)
  have hOutC0DC : Out C0 D C :=
    (perpendicular_midpoint_ray_transport_tarski
      (oppositeSides_symm_tarski hTS)
      hC0 hPerC hA0 hPerA
      (mul_midpoint_reverse hMidFt)
      (mul_midpoint_reverse hMidAD)).mpr
        (out_self_tarski hAA0)
  have hC_C0_D : Col C C0 D :=
    col_rotate (col_rotate (out_implies_col hOutC0DC))
  have hPerD : TarskiPerp P Q D C0 :=
    perpendicular_change_second_endpoint_tarski
      hCC0 hOutC0DC.1 hC_C0_D hPerC
  have hTSAD : OppositeSides P Q A D :=
    two_sides_perp_ray_transport_tarski
      hTS hA0 hPerA hC0 hPerC
      (out_self_tarski hAA0) hOutC0DC
  have hTSBD : OppositeSides P Q B D :=
    oppositeSides_ray_replace_of_midpoint_tarski
      hTSAD hMline hMidAD hR hOut
  exact two_sides_perp_ray_transport_tarski
    hTSBD hB0 hPerB hC0 hPerD
    (out_self_tarski hBB0) (out_swap_tarski hOutC0DC)

/-- GeoCoq Ch09 `outer_pasch` (Tarski's Satz 9.6): the outer-Pasch
intersection is constructed using the already derived `l9_5`, inner Pasch,
and uniqueness of the intersection of two distinct lines. The degenerate
collinear cases are dealt with using Ch05 betweenness alone. -/
theorem outer_pasch_tarski {A B C P Q : Point}
    (hACP : Bet A C P) (hBQC : Bet B Q C) :
    ∃ X : Point, Bet A X B ∧ Bet P Q X := by
  by_cases hcol : Col P Q C
  · by_cases hPQC : Bet P Q C
    · refine ⟨A, bet_start A B, ?_⟩
      exact bet_extend hPQC (bet_symm hACP)
    · have hPQ : P ≠ Q := by
        intro heq
        exact hPQC (by simpa [heq] using (bet_start P C))
      have hCQ : C ≠ Q := by
        intro heq
        exact hPQC (by simpa [heq] using (bet_end P C))
      have hout : Out Q P C := by
        rcases hcol with h | h | h
        · exact False.elim (hPQC h)
        · exact ⟨hPQ, hCQ, Or.inr h⟩
        · exact ⟨hPQ, hCQ, Or.inl (bet_symm h)⟩
      refine ⟨B, bet_end A B, ?_⟩
      rcases hout.2.2 with hQPC | hQCP
      · exact bet_symm (bet_inner_trans hBQC hQPC)
      · have hBCP : Bet B C P :=
          bet_outer_trans hBQC hQCP hout.2.1.symm
        exact bet_symm (bet_extend hBQC hBCP)
  · by_cases hBQ : B = Q
    · refine ⟨B, bet_end A B, ?_⟩
      simpa [hBQ] using (bet_end P Q)
    · have hPQ : P ≠ Q := noncol_ne_first_second hcol
      have hPC : P ≠ C := noncol_ne_first_third hcol
      have hCB : C ≠ B := by
        intro heq
        have hBQ' : B = Q :=
          between_identity B Q (by simpa [heq] using hBQC)
        exact hBQ hBQ'
      have hBoff : ¬ Col P Q B := by
        intro hBline
        have hline : ∀ T : Point, Col P Q T ↔ Col B Q T :=
          col_line_extensionality_tarski hPQ hBQ hBline (col_right P Q)
        exact hcol ((hline C).mpr (Or.inl hBQC))
      have hTS : OppositeSides P Q C B :=
        ⟨hcol, hBoff, Q, col_right P Q, bet_symm hBQC⟩
      have hAP : A ≠ P := by
        intro heq
        have hPCeq : P = C :=
          between_identity P C (by simpa [heq] using hACP)
        exact hPC hPCeq
      have hout : Out P C A :=
        ⟨hPC.symm, hAP, Or.inl (bet_symm hACP)⟩
      obtain ⟨_, _, X, hXline, hAXB⟩ : OppositeSides P Q A B :=
        oppositeSides_ray_replace_tarski hTS (col_left P Q) hout
      obtain ⟨T, hCTB, hXTP⟩ :=
        inner_pasch P B A C X (bet_symm hACP) (bet_symm hAXB)
      have hTline : Col P Q T :=
        col_segment_closed_tarski hPQ hXline (col_left P Q) hXTP
      have hTQ : T = Q :=
        line_intersection_unique_tarski hcol hCB
          hTline (col_right P Q)
          (Or.inr (Or.inl (bet_symm hCTB))) (Or.inr (Or.inl hBQC))
      refine ⟨X, hAXB, ?_⟩
      simpa only [hTQ] using (bet_symm hXTP)

/-- GeoCoq Ch09 `OS`: two points are on the same side of a line if a
third point lies on the opposite side from each of them. This is a
definition in the original single-sorted language of Tarski geometry. -/
def SameSides (P Q A B : Point) : Prop :=
  ∃ C : Point, OppositeSides P Q A C ∧ OppositeSides P Q B C

/-- GeoCoq Ch09 `l9_8_1`: sharing an opposite-side point is a witness
for the same-side relation, without invoking any additional axiom. -/
theorem sameSides_of_common_opposite_tarski {P Q A B C : Point}
    (hAC : OppositeSides P Q A C)
    (hBC : OppositeSides P Q B C) :
    SameSides P Q A B :=
  ⟨C, hAC, hBC⟩

/-- Symmetry of the internally defined same-side relation. -/
theorem sameSides_symm_tarski {P Q A B : Point}
    (h : SameSides P Q A B) : SameSides P Q B A := by
  obtain ⟨C, hAC, hBC⟩ := h
  exact ⟨C, hBC, hAC⟩

/-- GeoCoq Ch09 `not_two_sides_id`: no point can lie on the opposite
side of a line from itself. Betweenness identity is sufficient. -/
theorem oppositeSides_irrefl_tarski {P Q A : Point} :
    ¬ OppositeSides P Q A A := by
  rintro ⟨hAoff, _, X, hXline, hAXA⟩
  have hAX : A = X := between_identity A X hAXA
  exact hAoff (by simpa [← hAX] using hXline)

/-- GeoCoq Ch09 `one_side_reflexivity`: each point outside a line is
on the same side as itself. The required opposite-side witness is a
reflection about a point of the line. -/
theorem sameSides_refl_off_line_tarski {P Q A : Point}
    (hA : ¬ Col P Q A) : SameSides P Q A A := by
  have hAP : A ≠ P := (noncol_ne_first_third hA).symm
  obtain ⟨C, _, hAC⟩ :=
    not_par_two_sides_tarski
      (A := P) (B := Q) (C := A) (D := P) (I := P)
      hAP (col_left P Q) (col_right A P) hA
  exact ⟨C, hAC, hAC⟩

/-- Two opposite-side segments crossing the *same* point X of the
reference line have their other endpoints on a common strict ray from
X. This is Ch05 segment comparability, with no side-order axiom. -/
theorem oppositeSides_shared_crossing_transport_tarski
    {P Q U V W D X : Point}
    (hUW : OppositeSides P Q U W)
    (hUD : OppositeSides P Q U D)
    (hVD : OppositeSides P Q V D)
    (hX : Col P Q X)
    (hUXD : Bet U X D) (hVXD : Bet V X D) :
    OppositeSides P Q V W := by
  have hDX : D ≠ X := by
    intro h
    exact hUD.2.1 (by simpa [h] using hX)
  have hUX : U ≠ X := by
    intro h
    exact hUD.1 (by simpa [h] using hX)
  have hVX : V ≠ X := by
    intro h
    exact hVD.1 (by simpa [h] using hX)
  have hDUX : Bet D X U := bet_symm hUXD
  have hDVX : Bet D X V := bet_symm hVXD
  have hout : Out X U V := by
    rcases ray_bet_comparable_tarski hDX hDUX hDVX with hDUV | hDVU
    · exact ⟨hUX, hVX, Or.inl (bet_exchange hDUX hDUV)⟩
    · exact ⟨hUX, hVX, Or.inr (bet_exchange hDVX hDVU)⟩
  exact oppositeSides_ray_replace_tarski hUW hX hout

/-- GeoCoq Ch09 `l9_8_2`: if U and W lie on opposite sides of PQ,
and U and V lie on the same side of PQ, then V and W lie on
opposite sides. The proof invokes primitive inner Pasch and the
derived ray-transport `l9_5` after handling the crossing degeneracies. -/
theorem oppositeSides_sameSides_transport_tarski
    {P Q U V W : Point}
    (hUW : OppositeSides P Q U W)
    (hUV : SameSides P Q U V) :
    OppositeSides P Q V W := by
  obtain ⟨D, hUD, hVD⟩ := hUV
  have hUD_orig := hUD
  have hVD_orig := hVD
  obtain ⟨hUoff, _, X, hXline, hUXD⟩ := hUD
  obtain ⟨hVoff, _, Y, hYline, hVYD⟩ := hVD
  have hPQ : P ≠ Q := noncol_ne_first_second hUoff
  obtain ⟨M, hXMV, hYMU⟩ :=
    inner_pasch U V D X Y hUXD hVYD
  by_cases hMY : M = Y
  · have hXYV : Bet X Y V := by simpa [hMY] using hXMV
    have hXY : X = Y := by
      by_contra hne
      have hline : ∀ Z : Point, Col P Q Z ↔ Col X Y Z :=
        col_line_extensionality_tarski hPQ hne hXline hYline
      exact hVoff ((hline V).mpr (Or.inl hXYV))
    exact oppositeSides_shared_crossing_transport_tarski
      hUW hUD_orig hVD_orig hXline hUXD (by simpa [← hXY] using hVYD)
  · by_cases hMX : M = X
    · have hYXU : Bet Y X U := by simpa [hMX] using hYMU
      have hXY : X = Y := by
        by_contra hne
        have hline : ∀ Z : Point, Col P Q Z ↔ Col Y X Z :=
          col_line_extensionality_tarski hPQ (Ne.symm hne) hYline hXline
        exact hUoff ((hline U).mpr (Or.inl hYXU))
      exact oppositeSides_shared_crossing_transport_tarski
        hUW hUD_orig hVD_orig hXline hUXD (by simpa [← hXY] using hVYD)
    · have hUY : U ≠ Y := by
        intro h
        exact hUoff (by simpa [h] using hYline)
      have hVX : V ≠ X := by
        intro h
        exact hVoff (by simpa [h] using hXline)
      have hOutYUM : Out Y U M := ⟨hUY, hMY, Or.inr hYMU⟩
      have hMW : OppositeSides P Q M W :=
        oppositeSides_ray_replace_tarski hUW hYline hOutYUM
      have hOutXMV : Out X M V := ⟨hMX, hVX, Or.inl hXMV⟩
      exact oppositeSides_ray_replace_tarski hMW hXline hOutXMV

/-- GeoCoq Ch09 `one_side_transitivity`: same-side is transitive,
using `l9_8_2` and one shared opposite-side point. -/
theorem sameSides_trans_tarski {P Q U V W : Point}
    (hUV : SameSides P Q U V) (hVW : SameSides P Q V W) :
    SameSides P Q U W := by
  obtain ⟨D, hUD, hVD⟩ := hUV
  have hWD : OppositeSides P Q W D :=
    oppositeSides_sameSides_transport_tarski hVD hVW
  exact ⟨D, hUD, hWD⟩

/-- GeoCoq Ch09 `l9_9`: opposite and same sides are exclusive. -/
theorem oppositeSides_not_sameSides_tarski {P Q U V : Point}
    (hUV : OppositeSides P Q U V)
    (hSame : SameSides P Q U V) : False := by
  have hVV : OppositeSides P Q V V :=
    oppositeSides_sameSides_transport_tarski hUV hSame
  exact oppositeSides_irrefl_tarski hVV

/-! ### Ch06 collinearity and zero laws of the internal multiplication -/

/-- Transfer collinearity between two points of a nondegenerate line,
proved by Tarski incidence rather than postulated as a field axiom. -/
theorem colTransitivityGoal_tarski :
    ColTransitivityGoal (Point := Point) := by
  intro P Q A B hPQ hA hB
  by_cases hPA : P = A
  · subst A
    exact Or.inl (bet_start P B)
  · have hline :
        ∀ S : Point, Col P Q S ↔ Col P A S :=
      col_line_extensionality_tarski
        hPQ hPA (col_left P Q) hA
    exact (hline B).mp hB

/-- Multiplication by zero on the left has only the zero output,
even before the graph is known to be a total operation. -/
theorem mulGraph_zero_left_unique_tarski
    (f : Frame Point) (y z : AxisPoint f)
    (hMul : MulGraph f (axisZero f) y z) :
    z = axisZero f := by
  rcases hMul with
    ⟨_, hz⟩ | ⟨_, W, hWaxis, _, hLast⟩
  · exact hz
  · have hWJO : Col f.J f.O W := col_swap hWaxis
    have hsame : ∀ S : Point, Col f.J f.O S ↔ Col W z.1 S :=
      parallel_same_of_intersection
        hLast hWJO (col_left W z.1)
    have hzJO : Col f.J f.O z.1 :=
      (hsame z.1).mpr (col_right W z.1)
    have hzOJ : Col f.O f.J z.1 := col_swap hzJO
    exact Subtype.ext
      (frame_axes_intersection_only_origin_tarski f z.1 z.2 hzOJ)

/-- Total geometric multiplication specializes to a left-zero graph. -/
theorem mulGraph_zero_left_of_total_tarski
    (f : Frame Point) (hTotal : MulTotal f) (y : AxisPoint f) :
    MulGraph f (axisZero f) y (axisZero f) := by
  obtain ⟨z, hz, _⟩ := hTotal (axisZero f) y
  have hz0 : z = axisZero f :=
    mulGraph_zero_left_unique_tarski f y z hz
  simpa only [hz0] using hz

/-- For any defined geometric product, the output is zero precisely
when at least one input is zero. -/
theorem mulGraph_eq_zero_iff_tarski
    (f : Frame Point) (x y z : AxisPoint f)
    (hMul : MulGraph f x y z) :
    z = axisZero f ↔ x = axisZero f ∨ y = axisZero f := by
  constructor
  · intro hz
    by_cases hx : x = axisZero f
    · exact Or.inl hx
    by_cases hy : y = axisZero f
    · exact Or.inr hy
    have hx0 : x.1 ≠ f.O := by
      intro h
      exact hx (Subtype.ext h)
    have hy0 : y.1 ≠ f.O := by
      intro h
      exact hy (Subtype.ext h)
    have hnz : z.1 ≠ f.O :=
      mulGraph_output_nonzero_of_inputs_nonzero
        f (colTransitivityGoal_tarski (Point := Point))
        x y z hMul hx0 hy0
    exact False.elim (hnz (congrArg Subtype.val hz))
  · intro h
    rcases h with hx | hy
    · subst x
      exact mulGraph_zero_left_unique_tarski f y z hMul
    · subst y
      exact mul_zero_right_unique f x z hMul

/-- Left-zero law for the internally interpreted scalar product. -/
theorem axisMulOf_zero_left_tarski
    (f : Frame Point) (hMul : MulTotal f) (y : AxisPoint f) :
    axisMulOf f hMul (axisZero f) y = axisZero f := by
  exact mulGraph_zero_left_unique_tarski
    f y (axisMulOf f hMul (axisZero f) y)
    (axisMulOf_spec f hMul (axisZero f) y)

/-- The interpreted scalar product has no zero divisors. -/
theorem axisMulOf_eq_zero_iff_tarski
    (f : Frame Point) (hMul : MulTotal f) (x y : AxisPoint f) :
    axisMulOf f hMul x y = axisZero f ↔
      x = axisZero f ∨ y = axisZero f := by
  exact mulGraph_eq_zero_iff_tarski
    f x y (axisMulOf f hMul x y) (axisMulOf_spec f hMul x y)

/-- The synthetic GeoCoq product diagram and the internal multiplication
graph are equivalent with no additional collinearity hypothesis. -/
theorem geoCoqProd_iff_mulGraph_tarski
    (f : Frame Point) (x y z : AxisPoint f) :
    GeoCoqProd f x y z ↔ MulGraph f x y z := by
  exact geoCoqProd_iff_mulGraph_of_colTrans
    f (colTransitivityGoal_tarski (Point := Point)) x y z

/-! ### Synthetic addition: existence of its first projection -/

/-- The first two projections for adding a nonzero scalar can be
constructed from midpoint existence and the Tarski parallelogram lemma. -/
theorem add_first_projection_exists_tarski
    (f : Frame Point) (x : AxisPoint f) (hx : x.1 ≠ f.O) :
    ∃ T : Point,
      Parallel f.O f.J x.1 T ∧ Parallel f.O f.I f.J T := by
  have hOx : f.O ≠ x.1 := hx.symm
  have hOI_Ox : ∀ S : Point,
      Col f.O f.I S ↔ Col f.O x.1 S :=
    col_line_extensionality_tarski f.O_ne_I hOx
      (col_left f.O f.I) x.2
  have hNoncol : ¬ Col f.O f.J x.1 := by
    intro h
    have hJOx : Col f.O x.1 f.J := col_swap_last h
    exact f.noncol ((hOI_Ox f.J).mpr hJOx)
  obtain ⟨M, hMidJx⟩ := midpoint_existence_tarski f.J x.1
  obtain ⟨T, hMidOT, _⟩ := mul_reflection_exists_unique M f.O
  obtain ⟨hOJ_Tx, hJT_xO⟩ :=
    midpoint_diagonals_parallelogram_tarski
      hNoncol hMidJx hMidOT
  have hJT_Ox : Parallel f.J T f.O x.1 :=
    parallel_reverse_right hJT_xO
  have hJT_OI : Parallel f.J T f.O f.I :=
    parallel_retarget_right_of_line_eq hJT_Ox
      f.O_ne_I (fun S => (hOI_Ox S).symm)
  exact ⟨T, parallel_reverse_right hOJ_Tx,
    parallel_symm hJT_OI⟩

/-- Addition on the right by the geometric zero is always constructible,
without assuming `AddTotal` or a field law. -/
theorem add_zero_right_tarski
    (f : Frame Point) (x : AxisPoint f) :
    AddGraph f x (axisZero f) x := by
  by_cases hx : x.1 = f.O
  · exact Or.inl ⟨hx, Subtype.ext hx⟩
  · obtain ⟨T, hV, hH⟩ :=
      add_first_projection_exists_tarski f x hx
    refine Or.inr ⟨hx, T, hV, hH, ?_⟩
    simpa only [axisZero] using parallel_reverse_both hV

/-- The right-zero field-law goal follows already from the synthetic
addition construction; it requires neither Playfair nor totality. -/
theorem addRightZeroLaw_tarski (f : Frame Point) : AddRightZeroLaw f := by
  intro a
  exact add_zero_right_tarski f a

end TarskiField

#print axioms TarskiField.double_reflection_candidate_tarski
#print axioms TarskiField.midpoint_triangle_noncol_tarski
#print axioms TarskiField.double_reflection_triangle_tarski
#print axioms TarskiField.mul_reflection_preserves_cong
#print axioms TarskiField.mul_reflection_preserves_bet
#print axioms TarskiField.mul_reflection_preserves_col
#print axioms TarskiField.centered_reflection_parallel_tarski
#print axioms TarskiField.midpoint_diagonals_parallelogram_tarski
#print axioms TarskiField.triangle_midpoint_parallelogram_tarski
#print axioms TarskiField.playfair_parallel_segment_no_crossing_tarski
#print axioms TarskiField.playfair_transversal_meets_base_once_tarski
#print axioms TarskiField.mul_reflection_preserves_midpoint
#print axioms TarskiField.triangle_midpoint_reflection_bridge_tarski
#print axioms TarskiField.oppositeSides_crossing_unique_tarski
#print axioms TarskiField.playfair_parallel_line_not_opposite_sides_tarski
#print axioms TarskiField.triangle_midpoint_off_RB_tarski
#print axioms TarskiField.triangle_midpoint_reflected_pair_tarski
#print axioms TarskiField.playfair_euclid_wedge_nondegenerate_tarski
#print axioms TarskiField.playfair_euclid_wedge_opposite_sides_tarski
#print axioms TarskiField.triangle_reflected_P_off_XB_tarski
#print axioms TarskiField.diagonal_common_midpoint_parallel_tarski
#print axioms TarskiField.triangle_mid_par_of_common_midpoint_tarski
#print axioms TarskiField.mul_midpoint_center_unique_tarski
#print axioms TarskiField.triangle_reflected_wrong_pair_impossible_tarski
#print axioms TarskiField.triangle_reflected_common_midpoint_of_par_cong_mid_tarski
#print axioms TarskiField.parallel_through_off_line_of_midpoint_tarski
#print axioms TarskiField.midpoint_of_equidistant_crossing_tarski
#print axioms TarskiField.krippen_l7_22_tarski
#print axioms TarskiField.perpendicular_foot_exists_tarski
#print axioms TarskiField.tarski_per_cong_tarski
#print axioms TarskiField.tarski_midpoint_existence_aux_tarski
#print axioms TarskiField.midpoint_existence_tarski
#print axioms TarskiField.parallel_through_off_line_tarski
#print axioms TarskiField.colTransitivityGoal_tarski
#print axioms TarskiField.mulGraph_zero_left_unique_tarski
#print axioms TarskiField.mulGraph_zero_left_of_total_tarski
#print axioms TarskiField.mulGraph_eq_zero_iff_tarski
#print axioms TarskiField.axisMulOf_zero_left_tarski
#print axioms TarskiField.axisMulOf_eq_zero_iff_tarski
#print axioms TarskiField.geoCoqProd_iff_mulGraph_tarski
#print axioms TarskiField.add_first_projection_exists_tarski
#print axioms TarskiField.add_zero_right_tarski

/-!
## Mathematical proof manuscript: coordinatization and real closure

This is the **informal derivation to be translated**, attached to the one
canonical file so that the primitive definitions and the target statements
cannot drift apart.  It is an explanatory proof document, not Lean evidence.
No theorem is added to `Plane`, and no real-coordinate model is used.

### 0. Exact hypothesis and conclusion

Fix a model `Point` of `Plane`, and assume the first-order Tarski continuity
scheme `ContinuousPlane Point` (A13).  A13 is itself a Tarski axiom scheme:
it is not Dedekind completeness of an external set of real numbers.
Choose a noncollinear frame `f = (O,I,J)` supplied by `lower_dim`.
The intended conclusion is exactly `RealClosedAxisGoal f` above.

The carrier `F` consists of the *existing points* of line `OI`, each paired
with a proof of collinearity.  The operations on this carrier are `AddGraph`
and `MulGraph`, namely the parallel projection constructions already defined
in the file.  Neither operation is postulated to satisfy an algebraic law.

### A. Incidence and projection, prior to arithmetic

A1. `Bet`-symmetry, its nested transitivity laws, and the uniqueness of a
point lying simultaneously on two distinct lines follow from inner Pasch,
betweenness identity, segment construction, and line extensionality.  Their
proofs are already represented in this file by `bet_symm`, `bet_exchange`,
`bet_nested`, `bet_extend`, `col_line_extensionality_tarski`, and
`line_intersection_unique_tarski`.

A2. Given a nondegenerate line `AB` and `P` outside it, construct the
reflection of `P` in `A`, then reflect that image in `B`.  The two reflection
centres are midpoints of successive sides of a noncollinear triangle.
The middle-line theorem, together with Euclid's parallel postulate,
produces a line through `P` parallel to `AB`.  If two different such
lines existed, Playfair's uniqueness theorem would identify them.
The actual geometric construction and the final incidence inference are
the already proved `midpoint_existence_tarski` and
`parallel_through_off_line_tarski`, with their preceding synthetic lemmas.

A3. Define `Par(AB,CD)` as coincidence of their sets of collinear points
or the absence of any common point, requiring nondegenerate endpoints.
If parallel lines share a point, they coincide by definition.  Through any
point there is exactly one line of a specified direction: use A2 for
existence and the Euclidean uniqueness of parallels for uniqueness.
If lines of distinct directions did not meet, each would be parallel to
the other, so their directions would agree.  Thus distinct directions
through arbitrary given points have exactly one intersection; uniqueness
of the intersection is A1.  Parallel-transitivity follows by uniqueness
of the line of a fixed direction through a given point, including
coincident-line cases.  These are purely affine consequences of `Plane`.

### B. Total, single-valued geometric addition and multiplication

B1. Given axis points `x,y`, if `x=O`, define the sum to be `y`.
For `x != O`, draw through `x` the unique line parallel to `OJ` and
through `J` the unique line parallel to `OI`.  Their directions differ
because `O,I,J` are noncollinear; by A3 they meet in a unique point `T`.
Draw through `T` the unique line parallel to `Jy` and intersect it with
`OI`.  The directions `Jy` and `OI` differ because `J` lies outside `OI`.
This gives a unique axis point `z`, exactly the nonzero clause of
`AddGraph f x y z`.  All possible degeneracies have been accounted for:
`Jy` is a genuine line even when `y=O`, and the `x=O` clause is explicit.
Therefore `AddTotal f`; its witness is the value of the composition of
three unique parallel projections.

B2. Given axis points `x,y`, if `y=O`, the unique product is `O`.
For `y != O`, draw through `y` the unique line parallel to `IJ`.
It meets `OJ` uniquely at `W`, because `IJ` and `OJ` have different
directions.  Draw through `W` the unique line parallel to `Jx`.
It meets `OI` uniquely at `z`, because `Jx` and `OI` have different
directions.  This is exactly `MulGraph f x y z`, proving `MulTotal f`.
The zero-left uniqueness and absence of zero divisors are already reduced
to the same incidence lemmas in `mulGraph_zero_left_unique_tarski` and
`mulGraph_eq_zero_iff_tarski`; the remaining existence follows from A3.

B3. `x+0=x` has an existing direct geometric proof
`add_zero_right_tarski`; `0+x=x` is `add_zero_left`.  To obtain the
additive inverse of `x`, extend the segment `xO` by its own length,
constructing `x'` with `Bet x O x'` and `Cong x O O x'`.
The resulting flat parallelogram makes `AddGraph f x x' O` true.
When `x=O`, take `x'=O`.  For the multiplicative unit, `mul_one_right`
uses the point `J` as the first projection; the left-unit identity follows
by reversing the projection parallel to `IJ` and taking its endpoint `y`.

B4. If `x!=O`, intersect the line through `I` parallel to `Jx` with
the axis `OJ` at `W`, and intersect the line through `W` parallel to `IJ`
with `OI` at `y`.  Both intersections exist by A3.  The defining last
projection is now `Parallel J x W I`, so `MulGraph f x y I`.
The condition `x!=O` excludes exactly the case in which the first
intersection would lie at a forbidden parallel direction.  Thus the
nonzero elements have multiplicative inverses, without a division axiom.

### C. Field identities by synthetic geometry

C1. The sum construction is the effect of adding two successive affine
translations on the ruler.  For nondegenerate `O,x,y,z`, its geometric
characterization is the flat-parallelogram pair
`Cong O x y z` and `Cong O y x z`.  The reverse implication is obtained
from parallelogram uniqueness; the exceptional coincident/opposite cases
are treated by segment extension and the unique midpoint.  Exchanging
`x` and `y` exchanges the two congruences, proving additive
commutativity.  Four successive projections form a parallelogram grid;
the outer vertex determined by `x,y,z` is independent of how the first
two translations are grouped, by uniqueness of the common intersection
of the translated lines.  Hence `(x+y)+z=x+(y+z)`.  GeoCoq Ch14_sum
proves these two geometric statements as `sum_iff_cong`, `sum_comm`,
and `sum_assoc`, deriving them from the Tarski congruence and parallel
lemmas, rather than from any previously given additive group.

C2. Multiplication commutativity is the Pappus configuration produced
by the two projection diagrams for `xy` and `yx`.  Both scalar inputs
are on `OI`; the two first-projection points are on `OJ`.
The first two parallel connections follow from the defining projections.
The affine Pappus conclusion is precisely the third parallel connection,
which makes the output of `xy` a valid output of `yx`.
By uniqueness in B2 the outputs coincide.  If either input is `O`, B2
and the zero law replace the nondegenerate Pappus argument.
The exact instantiated statement is the existing
`pappus_product_swap_parallel`; the unrestricted geometric source is
GeoCoq Ch13_5_Pappus_Pascal, `l13_11`, itself derived from Tarski
congruence and perpendicularity.  This source proof must be translated,
not assumed as an extra field axiom.

C3. For `(xy)z=x(yz)`, combine the three first-projection points and
the two candidate last-projection points into the four-pair Desargues
configuration.  Three pairs of corresponding connecting lines are
parallel by the `MulGraph` hypotheses.  The affine Desargues conclusion
supplies the fourth parallel pair, turning one candidate into a product
for the other bracketing.  Uniqueness in B2 identifies them.
If any factor is `O`, the proved absorbing-zero laws resolve the case.
The specific synthetic implication is `AffineDesarguesFourPairs` and
its application is `desargues_associates_product_projection`.
GeoCoq Ch13_6_Desargues_Hessenberg derives this form from Pappus,
and Ch14_prod `prod_assoc` performs the corresponding multiplication
argument.  Again, this is an identified prior *geometric theorem*, not
a license to introduce an algebraic axiom.

C4. Distributivity follows because a fixed nonzero multiplication factor
acts on the two-axis affine grid by a parallel projection.  Apply the
projection to the parallelogram defining the sum of `b,c`; it preserves
the parallel sides, carries the projections of `b` and `c` to their
respective products, and carries the far vertex to the product of the
sum.  Uniqueness of the parallelogram vertex gives
`a(b+c)=ab+ac`.  For `a=O`, all terms are `O`, by B2.
GeoCoq Ch14_prod establishes the geometric result as `distr_l`/`distr_r`.

C5. B1-B4 and C1-C4 yield the group and field equations for the
uniquely defined operations on `AxisPoint f`.  There is no ambient `R`,
coordinate pair, or imported field operation in this derivation.
The `fieldF` theorem of GeoCoq's arithmetization is an independent
formal precedent for this very combination of synthetic lemmas.

### D. Order from the chosen oriented ray

D1. A scalar is positive if it is different from `O` and lies on the
ray `OI`.  The three possible positions of an axis point are: at `O`,
beyond `O` in the direction of `I`, or on the opposite ray.
This is the order trichotomy on a line from Tarski betweenness laws.
The opposite of a point on either nonzero ray lies on the other ray,
as follows from the midpoint construction in B3.

D2. Define `a<b` if `b=a+d` for a positive `d` (the existing `AxisLt`).
The flat-parallelogram characterization of addition shows that this is
the same orientation as moving right along `OI`.  In particular,
`a<b` and `Bet a X b` entail `a<=X<=b` on the axis: the two subsegments
are oriented the same way.  This proves `AxisDirectedBetOrder` from
incidence and addition, as opposed to assuming it as a new plane axiom.

D3. For positive `a,b`, the sum `a+b` is on the positive ray: the
parallelogram construction concatenates oriented positive distances.
The positive first projection of `b` lies on the positive ray `OJ`;
projecting it along the direction `Ja` produces an output on the positive
ray `OI` when `a` is positive.  Thus `ab>0`.
The inverse of a positive point is positive by the same projection
orientation.  A positive point and the additive inverse of a positive
point are on opposite rays, hence cannot sum to `O` unless one is `O`.
These are the positive-cone laws, exactly the geometric content of
GeoCoq Ch14_order (`prod_pos_pos` and `compatibility_of_sum_with_order`).
Consequently the internal field is a linearly ordered field.

### E. From A13 to the least upper bound of a DEFINABLE cut

E1. Let `Xi(X)` be a first-order formula, with a fixed ordered interval
`L<R` on the internally constructed axis, such that every `Xi` point
lies in `[L,R]`, and assume **some Xi point lies strictly right of L**.
Define the first-order formula `Upsilon(Y)` to say
`forall X, Xi(X) -> Bet L X Y`.  This is precisely
`upperBoundsFormula`: its bound variable is inserted by `Formula.rename`,
and `upperBoundsFormula_eval` proves the semantic equivalence.
Since `Xi` lies in `[L,R]`, the endpoint `R` satisfies `Upsilon`.

E2. For every `X` satisfying `Xi` and every `Y` satisfying `Upsilon`,
the defining formula gives `Bet L X Y`.  Thus the antecedent of the
original A13 scheme holds with `A=L`; no separate connectivity or
downward-closure assumption is required *to apply A13*.
A13 produces `B` satisfying `Bet X B Y` for every such `X,Y`.
Choose `X0 in Xi` strictly right of `L`, and take `Y=R`.
Then `Bet X0 B R`, so
`B` lies on `OI` by segment collinearity and is in `[L,R]`.

E3. The point `B` is the least upper bound of `Xi` in the internally
defined order.  For each `X in Xi`, use `Y=R` to obtain `X<=B`.
For any upper bound `Y`, choose the fixed `X0 in Xi` and apply A13
to obtain `B<=Y`.  Both assertions use the oriented-betweenness lemma
of D2, including the fact that `L<X0<=B` forces the orientation
of every upper bound `Y` to be rightward.  This strict-witness
condition is essential: if `Xi={L}`, the proposed `Upsilon` would
contain all points because `Bet L L Y` holds for every `Y`, and the
claimed order bound would be false.  The polynomial cut in G1
has a strict witness by the local negativity lemma F2 at `L`.
Every ingredient of `Xi` and `Upsilon`
is a finite Tarski-language formula, which is exactly the scope of A13.

### F. Polynomial sign permanence over ANY ordered field

F1. Let `p` be a finite polynomial with coefficients in the interpreted
field.  For a fixed scalar `b`, polynomial division by the monic linear
factor gives the algebraic identity
`p(x)-p(b)=(x-b)q_b(x)`, with `q_b` again a finite polynomial.
This identity is proved coefficientwise by distributivity and induction
on the Horner list; it needs no topological or completeness assumption.

F2. Write `q_b(X)=sum_{i=0}^m d_i X^i`.  On `|x-b|<=1`, one has
`|x|<=|b|+1=:H`, with `H>=1`.  Hence
`|q_b(x)|<=sum_i |d_i| H^i < M`, where
`M:=1+sum_i |d_i| H^i` is positive.
For `p(b)!=0`, let `delta:=min(1,|p(b)|/(2*M))`.
Then `delta>0`, and for `|x-b|<delta`,
`|p(x)-p(b)| <= |x-b|M < |p(b)|/2`.
Therefore `p(x)` has exactly the sign of `p(b)` throughout this
interval.  This is a finite ordered-field inequality, valid even in
non-Archimedean real-closed fields.  It is the precise lemma needed at
the cut boundary; no real-number continuity theorem is imported.

### G. Polynomial intermediate value theorem from A13

G1. Assume `L<R`, `p(L)<0`, `p(R)>0`.  Define the first-order
definable negative prefix
`Xi(X) := L<=X<=R and (forall T, L<=T<=X -> p(T)<0)`.
It contains `L` and is bounded above by `R`.
The quantifier over `T` and each Horner operation are expanded into
finite Tarski formulas; the earlier `polynomialNegativeFormula`,
`polynomialLowerCutFormula`, and semantic equivalences represent these
expansions.  Apply E1-E3 and let `b=sup Xi`.

G2. If `p(b)>0`, apply F2 to find an open interval
`(b-delta,b+delta)` of positive values.  First `b>L`: apply F2
to `p(L)<0`, choose `c` with `L<c<min(R,L+delta_L)`, and use
the negative-sign estimate to prove `c in Xi`; then `c<=b`.
Since `b` is the least upper bound and the axis
is densely ordered, for any `c<b` there exists `x in Xi` with
`c<x<=b`.  Choose `c` in `(max(L,b-delta),b)`.  Such an `x`
would satisfy `p(x)<0` (the defining prefix includes its endpoint)
and `p(x)>0` by F2, contradiction.

G3. If `p(b)<0`, by F2 there is an interval around `b` on which
`p<0`.  For every `t<b` with `L<=t`, choose an element `x in Xi`
with `t<x<=b` by the least-upper-bound property.  The prefix
condition for `x` yields `p(t)<0`.  The value at `b` is negative as
assumed.  To see `b<R`, apply F2 at `R` to obtain a left
neighbourhood of `R` where `p>0`.  No `Xi` point can enter
that neighbourhood, so its left endpoint (strictly below `R`)
is already an upper bound.  Hence the least upper bound `b<R`.
Choose
`c` with `b<c<min(R,b+delta)`.  Then every `t in [L,c]`
has `p(t)<0` (either `t<b` or `t` is in the sign-stable interval),
so `c in Xi`, contradicting that `b` is an upper bound.

G4. Order trichotomy excludes both `p(b)>0` and `p(b)<0`, forcing
`p(b)=0`.  This proves the polynomial intermediate value theorem
*for the internally interpreted field* from Tarski A13.  The entire
proof uses a definable supremum, not a pre-existing completion.

### H. Positive square roots and odd-degree polynomial roots

H1. If `a=0`, take `r=0`.  For `a>0`, let `p(X)=X^2-a`.
Then `p(0)<0`.  Choose `R=a+1`: since
`(a+1)^2-a = a^2+a+1>0`, we have `p(R)>0`.
Apply G1-G4 to obtain `r` with `0<r<R` and `r^2=a`.
In particular `r>=0`.  The graph/function correspondence of B2
turns this into `PositiveSquareRootProperty f`.

H2. Let `p(X)=a_n X^n+...+a_0` have odd degree `n=2k+1`
and `a_n!=0`.  Set `S=sum_{i<n}|a_i/a_n|` and choose
`T=2+S`; then `T>1` and `T>S`.  Because
`sum_{i<n}|a_i|T^i <= |a_n| S T^(n-1)
                       < |a_n| T^n`, the leading term strictly
dominates all lower terms at `T`.  Thus `p(T)` has the sign of
`a_n`.  Since `n` is odd, the leading term of `p(-T)` has the
opposite sign, and it again dominates the remainder.
Therefore `p(-T)` and `p(T)` have opposite signs.
After interchanging endpoints/sign of `p` if necessary, apply G1-G4.
The root is a witness for `OddPolynomialRootProperty f`, and the
earlier proved Horner semantics translates it into the exact `HornerGraph`
conclusion without changing the polynomial or introducing a new sort.

H3. D, H1, and H2 jointly establish that the internally interpreted
ordered field is real closed in the elementary (square-root + odd-degree
root) characterization.  This is exactly the content intended by
`RealClosedAxisGoal`, with each algebraic operation still the geometric
construction defined on actual points of `OI`.

### I. Geometry and later epsilon-delta limits

No point of the original Tarski model has been replaced.  The field carrier
is the definable subset `AxisPoint f` of those same points; hence its order
and operations are interpreted *inside* the geometric model.
For a geometric parameter `epsilon>0`, the inequalities `|t|<delta`
and `|F(t)-L|<epsilon` are statements about constructed axis points.
They are expressible using the internally obtained ordered-field laws.
Continuity of a polynomial or a rational expression with nonzero
denominator follows from the finite estimates in F1-F2.  No choice of
the real numbers, Archimedean axiom, or circular-arc approximation is
required.  Subsequent angle arguments remain outside this foundation.

### J. Precise translation boundaries (proof provenance)

The mathematical proof of G-H is explicit above and reduces to A13,
ordered-field algebra, and first-order definability already encoded.
The remaining long synthetic proofs C1-C4 (especially the Pappus and
Desargues geometric theorems) have existing formal Coq derivations from
Tarski's primitives; their **Coq proof bodies** are to be translated into
the declarations presently named `AffinePappusParallel`,
`AffineDesarguesFourPairs`, and the relational field-law goals.
These names in the current Lean file are *propositions*, not proofs.
Likewise the geometric order compatibility in D2-D3 is not discharged
merely by this narrative.  A successful future Lean derivation must
eliminate every one of these obligations without introducing axioms.

References for *proof derivations*, not external imported assumptions:
GeoCoq Ch13_5_Pappus_Pascal (`l13_10`, `l13_11`);
Ch13_6_Desargues_Hessenberg (`l13_19`);
Ch14_sum (`sum_exists`, `sum_iff_cong`, `sum_comm`, `sum_assoc`);
Ch14_prod (`prod_exists`, `prod_comm`, `prod_assoc`, `distr_l`);
Ch14_order (`prod_pos_pos`, `compatibility_of_sum_with_order`).

### K. Expanded incidence proof of additive translation and distributivity

K1. A general geometric translation with displacement represented by
`(O,V)` is defined by the *directed* parallelogram `O,V,Q,P`:
`OV` and `PQ` are parallel/equal in direction, and `OP` and `VQ`
are parallel/equal in direction.  In the noncollinear case, the unique
`Q` is the intersection of the corresponding two lines; in the
collinear case it is obtained by transporting a directed segment
along the common line.  A direction is determined by betweenness
orientation, not merely by unoriented segment congruence.
Existence and uniqueness in the collinear case are precisely the
ordered segment-extension and opposite-point lemmas already derived
from segment construction and five-segment uniqueness.

K2. In `AddGraph f x y z`, the auxiliary `T` satisfies
`Parallel O J x T` and `Parallel J T O x`.  Thus `O,J,T,x`
is a genuine nondegenerate parallelogram.  The final relation
`Parallel J y T z`, together with `Parallel J T y z`
(because `JT` and `yz` have the common axis direction `OI`),
forms `J,y,z,T`.  By the parallelogram composition lemma, the
resulting *flat* quadrilateral `O,y,z,x` has its opposite
directed sides equal.  In the directed-translation notation,
`z = translation_by(O,y)(x)`.

Conversely, if `z` is that directed translation of `x` by `(O,y)`,
the first parallelogram `O,J,T,x` constructed in B1 has a unique
vertex `T`.  Translate the second parallelogram backwards along
its `yT` side: the opposite direction gives `Parallel J y T z`.
Thus the translation criterion and `AddGraph` are equivalent.
This is the missing explicit bridge from the one-projection `AddGraph`
to GeoCoq Ch14's two-projection `Sum` construction.

K3. To compose displacements `(O,u)` and `(O,v)`, place two copies
of their parallelograms at a common starting point `P`.
The endpoint of `translation_by(O,v)(translation_by(O,u)(P))`
is the unique point lying simultaneously on the line through the
`u`-translated point parallel to `Ov` and the line through the
`v`-translated point parallel to `Ou`.  Reversing `u,v` exchanges
these two lines and leaves the intersection unchanged.  For a flat
grid, use K1's unique directed segment transport instead.
This proves the commuting law for parallel translations.
The composition itself displaces `P` by the translated copy of
the displacement of `O` under `u` followed by `v`.
That displacement is the point `u+v` of the flat axis sum.
Hence `translation_by(O,u) ∘ translation_by(O,v)` equals
`translation_by(O,u+v)` as transformations of the geometric plane.
Associativity of function composition now gives
`translation_by(O,(u+v)+w) = translation_by(O,u+(v+w))`;
evaluate both sides at `O` and use uniqueness to obtain
`(u+v)+w=u+(v+w)`.  This is the geometric content of the
GeoCoq Ch14_sum proof through `plg_pseudo_trans` and
`plg_uniqueness`, including its explicit zero/flat branches.

K4. The statement that parallel projection preserves a sum needs
an explicit *incidence argument*; it does NOT follow solely from
`Parallel` being an equivalence relation.  Write `π` for parallel
projection from `OI` to `OJ` along the direction `IJ`.  Given
`AddGraph b c d`, form projected points `b',c',d'` with
`Parallel I J b b'`, `Parallel I J c c'`, and `Parallel I J d d'`.
The geometric addition construction produces the flat
parallelogram `O,b,d,c`.  Build the extra off-axis vertex `E`
of the parallelogram with sides `O-b'` and the previously
constructed `b'-c'` translation line.  Apply parallelogram
composition (`plg_pseudo_trans`) to the two quadrilaterals
that share the diagonal of the addition grid.  It follows that
`c'd'` and the corresponding auxiliary side are parallel.
The uniqueness of the projection line through `d` forces this
quadrilateral's fourth vertex to be exactly `d'`.  Hence
the second-axis addition graph also holds for `(b',c',d')`.
When `b=O` or `c=O`, the projection of the origin is the origin,
and the graph's zero law gives the same conclusion.  When a
would-be parallelogram is flat, use the degenerate conclusion of
`plg_pseudo_trans` and `plg_uniqueness`, rather than asserting
that a strict parallelogram exists.  This is the content of
GeoCoq Ch14_sum's *proved* `proj_preserves_sum` (whose Coq body
explicitly splits the `b=O` and `c=O` cases).

K5. To use K4 for multiplication, the coordinate axis on the
second projection changes.  For fixed `a`, the geometric product
is a composition
`OI --(parallel IJ)--> OJ --(parallel Ja)--> OI`.
The first projection sends the sum `(b,c,b+c)` on `OI` to a
sum on `OJ`, by K4.  The next projection is performed with
reference direction `Ja`, so the second-axis sum must first be
proved independent of the chosen auxiliary point by
`sum_y_axis_change`.  Project the resulting sum back to `OI`
along `Ja`, again using K4.  The returned sum is initially
described in a frame with a different *unit* on its horizontal
axis; `sum_x_axis_unit_change` identifies that sum with the
original `AddGraph f`.  Consequently the three original product
graphs imply `AddGraph f ab ac a(b+c)`.  Uniqueness supplies
`LeftDistributiveLaw`.  If `a=O`, use the independently proved
zero laws instead of projecting in the collapsed direction `JO`.
The verified GeoCoq Ch14_prod proof of `distr_l` invokes in this
order `proj_preserves_sum`, `sum_y_axis_change`,
`proj_preserves_sum`, and `sum_x_axis_unit_change` (after the
zero-factor case).  Merely asserting that both projections
preserve addition without these compatibility theorems would
hide a real proof obligation.

K6. Thus the immediate Lean interfaces to prove, without an
ambient ring, are `AddGraph` versus GeoCoq `Sum` (K2), the
parallelogram-composition lemma (K3), preservation of the sum
by parallel projection (K4), and invariance under the two
auxiliary-grid changes (K5).  Each interface requires explicit
zero/flat/strict configurations.  No one of them can be
silently replaced by a field or vector-space identity.

### L. Exact order-compatibility deductions from synthetic parallels

L1. The nonzero positive scalars `Ps(O,I,x)` of GeoCoq Ch14_order
are our `Positive f x`: they are precisely `Out O I x`, a
Tarski-betweenness predicate.  The Coq lemma `l14_36_a` says:
if `(A,B,C)` is a geometrically constructed sum and `Out O A B`,
then `Bet O A C`.  Its proof first converts the sum to the
flat parallelogram `O,A,C,B` (`sum_cong`).  When `A=B`, it
uses flat-parallelogram segment equality and the unique midpoint
or a zero contradiction.  Otherwise, permuting the
parallelogram and transporting the betweenness along opposite
sides (`plg_bet1`) gives either `Bet A B C` or `Bet B A C`.
Together with the assumed ray order `O,A,B`, outer transitivity
then gives `Bet O A C`.  This is the missing incidence step
behind the slogan 'sum of two positive directed lengths'.

L2. The next lemma `l14_36_b` strengthens L1: in the same
situation, if `Out O A B`, all three separations
`O!=A`, `O!=C`, `A!=C` hold.  If `C=O`, the betweenness
`Bet O A O` contradicts `O!=A` by the identity axiom.  If
`C=A`, uniqueness of the geometric sum and the identity
`A+O=A` force `B=O`, contradicting `Out O A B`.
Given `Positive a` and `Positive b`, elementary ray lemmas
`l6_6`,`l6_7` give `Out O a b`.  L1 and L2 imply
`Out O I (a+b)`, by transitivity of positive rays and
`bet_out`.  This is GeoCoq's `sum_pos_pos`, and supplies
the concrete content of `PositiveAddClosed`.

L3. For positivity of products, apply the defining first
projection from the line `OI` to `OJ`:
`b -> b'` along `IJ`.  The projection preserves betweenness
(`project_preserves_bet`), because the pair of connecting
lines have a common direction and line-order is preserved
under a parallel projection.  Applying it to either of the
two possibilities in `Out O I b` yields `Out O J b'`.
The second projection `b' -> ab` from `OJ` to `OI`, parallel
to `Ja`, carries this to `Out O a ab`, again preserving
betweenness; the possible endpoint order is treated in two
separate cases.  Since `Positive a`, the ray-transfer
lemma `l6_7` implies `Out O I ab`.  Degeneracy `ab=O`
is excluded by `prod_null` together with the nonzero input
conditions.  This is the *actual* sequence in GeoCoq's
`prod_pos_pos` proof and does not use a pre-existing ordered
field, numerical slopes, or positivity of real numbers.

L4. The remaining order-compatibility step is the precise
equivalence of `AxisLt f a b` (positive `d` with geometric
`a+d=b`) and the oriented betweenness order on the whole
axis.  The forward direction uses the flat-parallelogram
identity for addition and its betweenness transport; the
reverse direction uses the segment-copy construction of the
positive directed difference `d`, then K2 to prove its
`AddGraph`.  Translation invariance is a consequence of
adding the same displacement and uniqueness; multiplication
by a positive `c` preserves inequality by distributivity
and L3.  These are distinct statements to discharge in
Lean and are not entailed by `sum_pos_pos` alone.

### M. Source-level synthetic Pappus and Desargues derivations

M1. The precise Pappus input is two different lines through O:
`not Col O A A'`, `Col O A B`, `Col O B C`,
`Col O A' B'`, `Col O B' C'`, and all indicated B,C,B',C'
different from O.  If `Parallel B C' C B'` and
`Parallel C A' A C'`, the desired line relation is
`Parallel A B' B A'`.  GeoCoq's `l13_11` is literally
the three-step proof: construct a shared perpendicular through
O to each of the two given parallel line pairs (`par_perp2`),
apply `l13_10` to transfer the common perpendicular to
`(AB',BA')`, and turn that common perpendicular back into
the desired parallel pair (`perp2_par`).  No field operations
occur in that three-step reduction.

M2. Here a *shared perpendicular* means
`Perp2 UV XY O := exists H K, Col O H K and Perp HK UV
and Perp HK XY`.  Its witness is an actual pair of points,
not a slope or a real scalar.  The proof of the difficult
`l13_10` constructs perpendicular feet L,L' for its first
shared perpendicular, M,M' for the second, and N for the
perpendicular from O to the target line AB'.  The feet exist
by perpendicular-line construction from Tarski's primitive
betweenness and congruence (GeoCoq Ch08), not by minimizing
a numerical distance.

M3. To compare the feet, let `Q_Cong l` assert that `l` is
the class of all point pairs congruent to some one segment
UV.  Let `Lcos(lb,lc,a)` mean that an actual right triangle
exists whose corresponding two side segments have classes
`lb,lc` and whose acute angle has class `a` (with the standard
well-formedness conditions).  `Eq_Lcos(la,a,lb,b)` means
that *some common projection-length class* makes both
Lcos statements true.  These are relations built wholly
from the original `Cong`, `Bet`, right-angle and angle
congruence constructions; the syllable 'cos' does not denote
a real-valued cosine function.

M4. The auxiliary `l13_10_aux1` proves that two congruent
right-angle projection configurations sharing the line OAB
have the same angle-congruence class.  To remove hidden line
order choices, it splits `Col O A B` into:
`Bet O A B`, `Bet A B O`, `Bet B O A`.  In the three
branches, the transferred feet respectively satisfy
`Bet O P Q`, `Bet P Q O`, `Bet Q O P`, by
`per23_preserves_bet` or `per13_preserves_bet`; the
corresponding ray-angle congruence follows from
`out_conga` or `l11_14`.  The auxiliary `aux2` handles
the flat/zero-angle case by `EqL` and `null_lcos`.
The auxiliary `aux3` shows `Bet A O B -> Bet A' O B'`:
apply `fourth_point A O B C`, analyze its four orders
C-A-O, A-C-O, O-C-B, O-B-C, and transport the two
perpendicular-associated betweenness relations in each.
The auxiliary `aux4` shows `Bet O A B -> Out O A' B'`:
its four orders are C-O-A, O-C-A, A-C-B, A-B-C;
the case A=B uses perpendicular transitivity and line
uniqueness to obtain A'=B'.  Finally `aux5` splits
`Out O A B` into the two orders of A and B and invokes
`aux4` with the appropriate permutation.  Thus all five
auxiliaries, not just four, feed `l13_10`.

M5. Represent the lengths of OA,OB,OC,OA',OB',OC',
OL,OL',OM,OM',ON by their `Q_Cong` classes.  Using
M4 for (B,C;L,L'), (C',B';L,L'), (C,A;M,M'),
and (A',C';M,M'), together with the projections onto
ON, yields five `Eq_Lcos` relations.  The combinatorial
middle of `l13_10` performs the following operations:
lift a common Lcos relation to `Eq_Lcos2`, commute the
two factors (`lcos2_comm`), lift to `Eq_Lcos3`, permute
its three arguments (`lcos3_permut1/2`), and compose the
relations (`lcos3_eq_trans`).  One obtains successively
equivalences of the triple classes
`(lb;l',n',m)`, `(lc';l,n',m)`, `(la;m',l,n')`,
`(lb';n,m',l)`, `(lc;m',l',n)`, `(la';m,l',n)`.
Cancel the shared factor classes by `lcos3_lcos2`,
commute the double relation, and cancel again by
`lcos2_lcos`; the output is exactly
`Eq_Lcos(lb,n',la',n)`.  Every cancellation here is an
existence/uniqueness argument for congruent projections
of actual right triangles, not cancellation in a field.

M6. `lcos_per_anga` transforms the final projection
relation into congruence of the relevant acute angles
near N.  The order-compatibility facts `aux3/aux5`
decide which ray, rather than merely which unoriented
line, carries that angle.  Copy the required length
along the selected ray ON to construct N'.  The resulting
right-triangle relations show simultaneously
`Per O N' B` and `Per O N' A'`.  The theorem
`per_per_perp` now makes ON' perpendicular to BA'.
Since the line from O through N was also perpendicular
to AB', the shared-perpendicular definition holds for
`AB',BA'`; this completes `l13_10` and hence M1.
The missing *Lean* development is the large underlying
right-angle/length/angle-class library, not a purported
need to assume a number field.

M7. For the affine Desargues four-pair lemma, assume the
corresponding vertices A/A', B/B', C/C', D/D' each
lie on the respective rays through O, with the three
appropriate pairs of connecting lines parallel.  The
goal is `CD || C'D'`.  Start by eliminating degeneracies
A=A', A=C, and A'=C' with line uniqueness and the
already parallel sides.  If the unprimed AB and CD
lines are nonparallel, construct their intersection E
by `not_par_inter_exists`.  Construct E' as the
intersection of A'B' with OE.  The latter lines cannot
be parallel: otherwise AB would coincide with OE
because E lies on both, forcing O,A,B to be collinear.
If the nonparallel pair occurs on the primed side,
interchange primed and unprimed roles first.

M8. If A,D,E are collinear, their additional memberships
E in AB and D in OB imply D=B by the uniqueness of the
line through A,B and the ray through O,B; the primed
parallel pairs then imply D'=B' and the desired
parallelism is the given `BC || B'C'`.  Otherwise the
triangles ADE and A'D'E' are both noncollinear, their
vertices are paired on common rays from O, and the
connections AD/A'D', AE/A'E' are strictly parallel.
Apply triangle Desargues `l13_15` to these two triangles:
`DE || D'E'`.  Similarly, if B,C,E are collinear,
the goal reduces directly to a known pair; otherwise
`l13_15` for triangles BCE and B'C'E' yields
`CE || C'E'`.  Both DE and CE lie on the line CD,
so the lines D'E' and C'E' are parallel to CD and
share E'; parallel-line uniqueness forces C',D',E'
collinear.  Substitute that line for C'E' to obtain
`CD || C'D'`.  This is the exact construction and
two uses of `l13_15` in GeoCoq `l13_19_aux`.

M9. The Desargues reduction M7-M8 is not yet the complete
Tarski-to-Desargues proof: its premise `l13_15` is a
nontrivial earlier result proved synthetically using
Pappus (`l13_11`), plane incidence and strict-parallel
case analysis.  Its constructive steps are expanded in
M10-M12.  Likewise the proof of M4-M6 presupposes the
primitive-based lemmas establishing `Q_Cong`, `Lcos`,
perpendicular constructions and angle-class composition.

M10. The principal triangle Desargues lemma `l13_15_1`
assumes `not Parallel OB AC`, and two corresponding
side pairs AB/A'B' and AC/A'C' are parallel.  Eliminate
the collinear triangles: strict parallelism prevents O
from lying on the corresponding lines; the two triangles
are nondegenerate.  If O,B,C are collinear, the primed
correspondents are likewise, and the two BC lines
coincide, proving the goal.  In the remaining case,
construct a line through A parallel to OB by Euclid's
parallel construction (`parallel_existence`).  Call it
XY.  Since OB is not parallel to AC and A'C' is parallel
to AC, XY intersects A'C'; call the intersection L.
Since O,B,C are noncollinear, XY also intersects OC;
call that intersection M.  Finally AB and LB' are not
parallel (if they were, the known AB/A'B' and A'C'
relationships would force a forbidden collinearity),
so they meet at N.  We have now built the actual points

    L in XY intersect A'C',
    M in XY intersect OC,
    N in AB intersect LB',
    AL || OB,  AN || A'B'.

M11. First prove `ON || LA'` by deciding whether
`AO || NL`.  If parallel, discard coincidence by the
triangle's noncollinearity and apply the affine Pappus
configuration `l13_14` to (A,O,A',A,N,L,N,B').
If nonparallel, construct P at `AO intersect NL`, and
apply the original Pappus `l13_11` to
(O,A',A,L,N,B',P).  The indicated parallel relations
then transfer to give `ON || LA'`, and the collinear
substitutions with L in A'C' give `ON || AC`.
Next show `NM || BC`: decide whether `AN || OC`.
In the parallel case use `l13_14` on
(A,N,B,A,O,C,M,O); in the nonparallel case create
P at `AN intersect OC` and apply `l13_11` on
(N,B,A,C,M,O,P).  The third relation
`NM || B'C'` is obtained by the analogous split on
`NB' || OC'`: use `l13_14` on
(B',N,B',L,O,C',M,O), or make the intersection
P at `NB' intersect OC'` and use `l13_11` on
(N,B',L,C',M,O,P).  Since both BC and B'C' are
parallel to the same nondegenerate NM line, parallel
transitivity yields `BC || B'C'`.

M12. The complementary case `Parallel OB AC` is
`l13_15_2`.  Assume the desired BC/B'C' parallelism
fails.  The nonparallel-line dichotomy reduces it to
`l13_15_2_aux`, possibly after interchanging the
primed and unprimed triangles.  Construct through B'
a line XY parallel to BC.  Because O,B,C are
noncollinear, XY intersects OC; name that point C''.
This gives `BC || B'C''`.  Now permute the input
triangles from (A,B,C) to (B,A,C): the case condition
needed by `l13_15_1` is precisely the complementary
nonparallel direction.  Apply M10-M11 to
(B,A,C; B',A',C''; O) to get `AC || A'C''`.
The given `AC || A'C'` then makes A'C'' parallel to
A'C'; their common point A' forces them to coincide.
Because C'' and C' both lie on the ray/line OC,
the intersection-uniqueness lemma forces C''=C'.
Substitution produces `BC || B'C'`, contradicting the
assumption.  The final `l13_15` merely splits the
decidable alternatives `Parallel OB AC` and its
negation, applying M12 or M10-M11 respectively.
Combined with M7-M8, this expands the Desargues
derivation through its actual Pappus subconfigurations.
Each strictness condition in M10-M12 remains a
specific synthetic proof obligation, not an implicit
coordinate calculation.

M13. M1-M12 identify the genuine Tarski proof dependencies
but do not by themselves finish an *unabridged* proof:
the source Ch13 proofs of the perpendicular-angle,
length-class, affine-parallel and intersection lemmas
must still be matched to primitive-based Lean proofs.
These named geometric facts are proofs in the independent
Coq development, whereas in the present single Lean
file the corresponding `AffinePappusParallel` and
`AffineDesarguesFourPairs` remain theorem *targets*.

M14. One more prerequisite in M11 is `l13_14`, the
*parallel-lines version of Pappus*.  It is not merely
`l13_11` with points renamed.  GeoCoq derives it as
follows: the two base lines OA and O'A' are strictly
parallel.  First dispatch the coincidences A=C and
B=C by direct line substitution.  In general position
make the two crossing pairs AC/A'C' and BC/B'C'
strictly parallel.  From them construct the
parallelograms ACC'A' and BCC'B' (`pars_par_plg`).
Each gives a midpoint of the common diagonal CC'
(`plg_to_parallelogram`, `plg_mid`).  The midpoint
uniqueness theorem `l7_17` makes the two centers
identical.  The same center bisects the diagonals
of ABB'A'; `mid_plg` turns that midpoint pairing
back into a parallelogram.  Its opposite sides are
parallel by `plg_par`, proving the third crossing pair.
Thus `l13_14` depends crucially on the *existing*
middle-point existence/uniqueness and parallelogram
theorems, precisely the same synthetic foundation
needed for our `AddGraph` arguments.

M15. The application of Pappus in M11 requires a
nondegeneracy ledger, which is not discharged by
the names of intersection points alone.  The line
XY constructed through A is represented by arbitrary
distinct endpoints; if X=L, substitute the other
endpoint when proving AL parallel to OB.  When
`Parallel AO NL` fails, the new intersection
P of AO with NL must be proved distinct from
L,O,A,N,A',B' as required by the exact seven-point
configuration of `l13_11`.  Similarly, for
`NM || BC` the intersection P of AN and OC must
be distinct from B,A,M,O,N.  For the last
`NM || B'C'` case, GeoCoq handles **C'=L**
and **L=M** separately: line uniqueness `l6_21`
then yields C'=M and finishes the parallelism
directly.  Only after excluding both equalities
does it construct P at NB' intersect OC' and
exclude coincidences with B',L,N to call `l13_11`.
These cases explain why the short informal phrase
'apply Pappus to the intersection' is insufficient
to count as the complete synthetic proof.

### N. Explicit Horner induction behind the local sign lemma

N1. The Horner representation used by `HornerGraph` is
`H_nil(x)=0`, `H_(c::cs)(x)=c+x*H_cs(x)`.  This is exactly
the coefficient-list order `[c0,c1,...,cn]`; it does not
assume beforehand that polynomials are functions on real
numbers.  Define a *second finite expression* in two
internal scalar variables by
`D_nil(x,b)=0` and
`D_(c::cs)(x,b)=H_cs(x)+b*D_cs(x,b)`.
Then prove by induction on the coefficient list that
`H_cs(x)-H_cs(b)=(x-b)*D_cs(x,b)`.
For the induction step, write H=H_cs and D=D_cs:

    H_(c::cs)(x)-H_(c::cs)(b)
      = x*H(x)-b*H(b)
      = (x-b)*H(x)+b*(H(x)-H(b))
      = (x-b)*(H(x)+b*D(x,b)).

Every equality is a field-law identity already meant to
be derived in C; no division, completeness, or analysis
is used in this factorization.

N2. For a fixed b put `Hmax=|b|+1`, so `Hmax>=1`.
For each coefficient list recursively define nonnegative
*constants* `B_nil=0`, `B_(c::cs)=|c|+Hmax*B_cs`
and `M_nil=0`, `M_(c::cs)=B_cs+|b|*M_cs`.
When `|x-b|<=1`, the triangle inequality gives
`|x|<=Hmax`.  Induction yields both
`|H_cs(x)|<=B_cs` and `|D_cs(x,b)|<=M_cs`:
for H, use `|c+x*H_cs(x)|<=|c|+Hmax*B_cs`;
for D, use
`|H_cs(x)+b*D_cs(x,b)|<=B_cs+|b|*M_cs`.
Thus the constants are explicitly obtained by finitely
many internal axis additions, multiplications, absolute
values and comparisons; no supremum of an infinite set
of polynomial values is being smuggled in.

N3. If `H_cs(b)!=0`, choose
`delta=min(1,|H_cs(b)|/(2*(1+M_cs)))`.
The ordered-field axioms imply `delta>0`.
For `|x-b|<delta`, N1 and N2 give

    |H_cs(x)-H_cs(b)|
      = |x-b|*|D_cs(x,b)|
      <= |x-b|*M_cs
      < |H_cs(b)|/2.

The last strict inequality holds even for `M_cs=0`,
because `M_cs/(1+M_cs)<1` and the denominator is
positive.  If `H_cs(b)>0`, the triangle inequality
implies `H_cs(x)>H_cs(b)/2>0`; if `H_cs(b)<0`,
apply the same argument to `-H_cs` to obtain
`H_cs(x)<H_cs(b)/2<0`.  This establishes the finite
local-sign permanence used at G2 and G3 in every
ordered field, including non-Archimedean ones.

N4. For a fixed coefficient list, the proof above is a
finite induction and can itself be expressed through
the relational graph `HornerGraph`.  Its existential
witnesses are precisely the intermediate graph values
provided by `AddTotal` and `MulTotal`; uniqueness
from `hornerGraph_exists_unique` is needed to identify
them with the same polynomial at neighboring arguments.
The E-G cut formulas then use only Tarski points for
the variable, output, and coefficient parameters.

### O. Completing the Euclidean uniqueness bridge to arithmetic

O1. The synthetic midpoint-existence theorem now appears as an
actual `Plane`-only Lean proof (`midpoint_existence_tarski`),
followed by `parallel_through_any_point_tarski`.  Therefore the
old construction theorem `both_operation_graphs_total_of_parallel_theorems`
no longer needs the hypothesis 'every point has a parallel' when
invoked in this same file.  The new Lean theorem
`both_operation_graphs_total_of_playfair_tarski` supplies that
hypothesis from the proved midpoint reflection construction,
then obtains both `AddTotal f` and `MulTotal f` from *only*
the remaining Playfair uniqueness theorem.  The similarly
unconditional-with-respect-to-existence theorem
`both_operation_graphs_functional_of_playfair_tarski` yields
`AddFunctional f` and `MulFunctional f` by uniqueness.
They are still conditional on Playfair, a synthetic theorem
to derive from the already present `Plane.euclid` axiom.

O2. GeoCoq's primitive-to-Playfair proof in
`Meta_theory/Parallel_postulates/tarski_playfair` starts
with a line AB and two candidate parallel lines CD, EF
through the same point P.  When P lies on AB, both lines
must coincide with AB because a parallel line sharing an
intersection is the same line.  For P outside AB, both
parallels are strict, i.e. entirely disjoint from AB.
Assume CD and EF differ.  Line extensionality then
provides an endpoint of EF that is outside CD.

O3. The geometrical `not_par_other_side` lemma, once derived
from the two-dimensional separation theorems below, supplies
a point C' on EF that lies on the opposite side of CD
from the selected base point A.  In particular there
exists B on CD such that `Bet A B C'`.
Reflect C' across P to obtain C, with `Bet C' P C`
and `Cong P C' P C`.  Inner Pasch in the resulting
triangle provides D with `Bet B D C` and
`Bet P D A`.  Because CD and EF are distinct,
P,B,C are noncollinear and P!=D.  All this uses
only segment construction, midpoint existence,
betweenness and inner Pasch, before applying Euclid.

O4. Apply the primitive `Plane.euclid` to
`Bet P D A` and `Bet B D C` with `P!=D`.
It constructs X,Y such that `Bet P B X`,
`Bet P C Y`, `Bet X A Y`.  The first two place
X on CD and Y on EF.  Both lines were disjoint
from AB, so X,Y are outside AB; the last relation
places them on opposite sides of AB, with crossing
point A.  GeoCoq's `l12_6` instead shows that each
of X,Y is on the same side of AB as P, because
it is joined to P on a strict parallel line.
Transitivity of the same-side relation makes X,Y
same-side, contradicting their opposite-side
relation (`l9_9`).  Hence CD and EF cannot differ,
proving Playfair uniqueness from the *existing*
Tarski Euclid axiom.  In the Lean file the later
half of this argument is partly present as
`playfair_euclid_wedge_opposite_sides_tarski`;
the initial opposite-side witness and same-side
composition have yet to be transplanted.

O5. Once O2-O4 has been made unconditional in Lean,
substitute the resulting Playfair uniqueness theorem
into the two new lemmas of O1.  Unlike earlier
conditional developments, the obtained
`AddTotal f ∧ MulTotal f` then follows from the
original `Plane` data alone.  This is the exact
next interface for constructing the internal field;
no assumption about the existence of a field,
number coordinates, or real-valued geometry occurs.

O6. The neutral preliminary lemma `not_par_two_sides_tarski`
is now implemented in Lean, independently of Playfair. Let
CD be a nondegenerate line meeting AB at I, with C outside
AB. Since C is outside AB while I is on AB, C != I. Tarski
segment construction produces the reflection Y of C across
I, so `Bet C I Y`. Distinctness of C and I implies C != Y
and I != Y. Both C and I lie on CD, so line extensionality
places Y on CD. If Y were on AB, line extensionality
applied to I and Y would put C on AB, contrary to choice.
Thus `OppositeSides A B C Y` with crossing point I.
This proves the specific line-crossing construction that
GeoCoq uses before its `not_par_other_side` lemma. The
additional three-way plane-separation theorem needed to
choose *which* of C and Y is opposite a third external point
is a separate unproved obligation, not hidden in this lemma.

O7. For a fixed nondegenerate base line L=AB define TS_L(U,V)
to mean `U,V not in L` and the segment UV has an interior
point in L. Define OS_L(U,V) by the *geometric* existential
relation `exists W, TS_L(U,W) and TS_L(V,W)` (the two
segments UW and VW meet L). This is the same-side predicate
used in GeoCoq, which is defined in terms of betweenness;
it is not a numerical sign comparison. The plane-separation
theorem `l9_8_2` asserts

    TS_L(U,W) and OS_L(U,V) -> TS_L(V,W).

It implies TS_L(U,V) and OS_L(U,V) cannot both hold:
substitute W=V to get TS_L(V,V). The latter provides
`Bet V T V` with T in L, so T=V by Tarski betweenness
identity, contrary to V outside L. It also implies
transitivity of OS: from OS_L(U,V) choose W with
TS_L(U,W), TS_L(V,W); combining OS_L(V,Z) with
TS_L(V,W) yields TS_L(Z,W), hence OS_L(U,Z).

O8. The remaining synthetic plane separation theorem is
`not_two_sides_one_side`: if U and V are outside L and
not TS_L(U,V), then OS_L(U,V). It is a genuine result
of Tarski's 2-dimensional axioms, rather than classical
logic alone. GeoCoq's complete derivation begins by
constructing the perpendicular foot F of U on AB using
the Gupta `l8_18_existence` theorem (our proved
`perpendicular_foot_exists_tarski`). If F is the chosen
endpoint A of the base line, reverse the endpoint labels.
Otherwise apply the perpendicular-through-point
construction `l8_21` at F to obtain points P,T such that
FP is perpendicular to AF, T lies on AF, and Bet V T P.
Thus TS_L(V,P). The upper-dimension axiom makes U,F,P
collinear: both FU and FP are perpendicular to AF at F,
and distinct perpendiculars at F would give three
noncollinear points equidistant from the same two
reflected noncoincident points, violating `upper_dim`.
Since U,F,P are collinear, the line-order lemma
`or_bet_out` gives either Bet U F P or Out F U P.
In the first branch, F is a crossing of UP with L,
so TS_L(U,P); together with TS_L(V,P), P witnesses
OS_L(U,V). In the ray branch, transport of crossings
along Out F U P shows from TS_L(V,P) that TS_L(U,V),
contradicting the hypothesis. The required ray-transport
is itself a neutral Pasch/side lemma of GeoCoq Ch09.
The exact mathematical construction has now been
identified; the upper-dimension/perpendicular sublemmas
and ray-transport branch still require Lean translations.

O9. With O7-O8 and the *already proved* crossing construction
O6, the lemma `not_par_other_side` has a short complete
reduction. Suppose C,Y lie on the intersecting line CD and
TS_L(C,Y); let P be any point outside L. By excluded middle,
either TS_L(P,C), in which case choose C, or not. In the
latter case O8 yields OS_L(P,C). Apply O7's `l9_8_2` to
TS_L(C,Y) and OS_L(C,P) to obtain TS_L(P,Y), and choose Y.
Thus the requested point lies on CD and is opposite to P.
The only remaining assumptions in this reduction are the
two explicit synthetic lemmas of O7-O8, themselves targets
for the Tarski/Pasch translation.

O10. The remaining neutral side-transport lemma `l9_8_2`
can be reduced to finitely many betweenness configurations.
Assume TS_L(U,W) and OS_L(U,V). Choose D witnessing
OS, and crossing points T,X,Y on the base line with

    Bet U T W,  Bet U X D,  Bet V Y D.

Apply inner Pasch in the triangle UVD to the middle
points X and Y, obtaining M with Bet Y M U and
Bet X M V (up to the interchangeable orientation of
the primitive inner-Pasch variables). The original Ch09
proof splits into exactly the following geometric cases.

If M differs from both X and Y, `Bet Y M U` yields
`Out Y U M`, and `Bet X M V` yields `Out X M V`.
The ray-crossing lemma `l9_5` states that if a crossing
segment starts from U, then replacing U by another
point on the same ray from a base-line point preserves
crossing. First apply it with ray centre Y, transferring
TS_L(U,W) to TS_L(M,W). Apply it again with centre X,
transferring TS_L(M,W) to TS_L(V,W), as required.

If M=Y, the second Pasch relation gives Bet X Y V;
since X,Y lie on the base line and V does not, line
intersection uniqueness forces X=Y. If M=X, the first
Pasch relation gives Bet Y X U; likewise U lies off
the base line, so X=Y. It remains to handle X=Y.
Now `Bet U X D` and `Bet V X D` imply U,V lie on
the same ray originating at X and opposite to D:
`D!=X` by off-line D, and the common-endpoint segment
order lemma `l5_1` compares U and V on that ray;
the two possible orders both give `Out X U V`, using
`bet_exchange` to orient the nested betweenness.
Apply `l9_5` with centre X once to TS_L(U,W), obtaining
TS_L(V,W). The cases of equal off-line endpoints are
excluded by the impossibility of TS_L(U,U), proved
from `Bet U T U -> T=U` and U outside L.

This is an explicit case reduction of the 230-line
GeoCoq argument for `l9_8_2`. It is **conditional on
the separate ray-crossing lemma `l9_5`**. GeoCoq's
proof of `l9_5` uses perpendicular feet of three
points, midpoint reflection, and the congruence-based
transport lemmas `l9_4_1`/`l9_4_2`; these still have
to be translated to derive `l9_8_2` from the exact
Lean `Plane` signature without skipping a theorem.

O11. Assuming the fully proved results O8 and O10, the
last side-theoretic part of Playfair closes as follows.
If P and X belong to a strict parallel line disjoint
from AB, a crossing T in AB with Bet P T X would also
belong to PX by segment closure, a contradiction.
Therefore ¬TS_L(P,X), while both P and X are off AB;
O8 gives OS_L(P,X). Similarly OS_L(P,Y) for the
other strict parallel. By O7's derived transitivity,
OS_L(X,Y). Tarski's Euclid axiom has produced
Bet X A Y with A on AB, so TS_L(X,Y). This conflicts
with O7's exclusivity of TS and OS. Consequently the
two parallels coincide, which is the exact Playfair
statement required by B1-B2. The remaining work is
to discharge O8/O10 synthetically from `Plane`, not
to hypothesize Playfair as a new geometric axiom.

### P. The full definable-cut argument, with every endpoint case

The following proof uses exactly the ordered-field laws of C-D
**after they have been derived inside the Tarski model**. It does
not postulate order completeness for arbitrary subsets. The only
existence principle for a bound of an infinite definable set is
the point-valued A13 scheme. All symbols in this section denote
points on the already constructed axis OI, with their *internal*
addition, multiplication, and order.

P1. Let L<R and let a finite Horner polynomial p satisfy
p(L)<0<p(R). N1-N3 give, for every scalar b with p(b)!=0,
a scalar epsilon_b>0 such that, for all t on OI,

    |t-b| < epsilon_b  ->  sign(p(t))=sign(p(b)).

This follows from the explicitly inductive identity
p(t)-p(b)=(t-b)*D_p(t,b), and the finite bound on D_p
on |t-b|<=1. The division used in epsilon_b is by the
strictly positive internal scalar 2*(1+M_p(b)); its inverse
exists by B4 and has the required sign by D3. In
particular no continuity assumption about p has been
introduced beyond a proved field inequality.

P2. Define Xi(x) by

    L<=x<=R and forall t (L<=t<=x -> p(t)<0).

This is precisely `polynomialLowerCutFormula`, once its
evaluation equivalence and finite Horner graph functionality
have been proved. To produce a **strict** left witness,
take epsilon_L from P1 and put

    d=min(epsilon_L/2,(R-L)/2),  c=L+d.

The ordered-field laws yield d>0, so L<c<R. If
L<=t<=c, then 0<=t-L<=d<epsilon_L and p(t)<0.
Thus Xi(c). Every Xi element lies between L and R,
so R is an upper bound; Xi is nonempty and contains
an element strictly beyond L. This strictness prevents
the degenerate-bound defect of the singleton {L}.

P3. Define Upsilon(y) by

    forall x (Xi(x) -> Bet(L,x,y)).

It is syntactically a first-order formula: `Formula.rename`
shifts the free indices under the quantifier, and
`upperBoundsFormula_eval` proves that it expresses exactly
the displayed predicate. The witness R belongs to Upsilon,
because for Xi(x) one has L<=x<=R and hence Bet(L,x,R)
by the internally proved betweenness/order correspondence.
For all Xi(x) and Upsilon(y), Bet(L,x,y) holds by the
definition of Upsilon. Apply the original Tarski A13
with A=L; obtain a point B such that

    forall x,y (Xi(x) and Upsilon(y) -> Bet(x,B,y)).

Insert x=c from P2 and y=R to get Bet(c,B,R). The
segment-closure theorem places B on OI, and the directed
betweenness theorem yields L<c<=B<=R. No field element
has been added to the model: B is a point supplied by A13.

P4. B is the least internal upper bound of Xi. Indeed, for
each Xi(x), insert y=R into A13 to obtain Bet(x,B,R).
Both x and B are in [L,R], so the directed order lemma
implies x<=B. Let y be any order-theoretic upper bound
of Xi, i.e. x<=y for all Xi(x). Since Xi(c) and L<c,
we have L<c<=y, so Bet(L,x,y) for all Xi(x); thus
Upsilon(y). Insert x=c into A13 to obtain Bet(c,B,y).
As L<c<=B, the orientation forces B<=y. Therefore

    forall x (Xi(x) -> x<=B),
    forall y ((forall x (Xi(x)->x<=y)) -> B<=y).

This proof also shows uniqueness: if B' satisfied both
properties, B<=B' by leastness of B, and B'<=B by
leastness of B'; antisymmetry gives B=B'. The step
`Bet(c,B,y) -> B<=y` is justified only after the
strict witness c>L has fixed the direction of the line.

P5. Suppose p(B)>0. Then B>=c>L. Put

    d=min((B-L)/2,epsilon_B/2),  t=B-d.

We have d>0, L<t<B and |t-B|=d<epsilon_B, so
p(t)>0 by P1. Because t<B and B is the least upper
bound, t cannot be an upper bound of Xi; otherwise
B<=t, contrary to t<B. Hence there exists x with
Xi(x) and t<x. Since x<=B, we have L<t<x<=R.
Xi(x) then implies p(t)<0. This contradicts p(t)>0.
Thus p(B)>0 is impossible, including the endpoint
case B=R; B=L was already excluded in P3.

P6. Suppose p(B)<0. First show B<R. P1 at R gives
epsilon_R>0 with p(t)>0 when |t-R|<epsilon_R.
Put d=min((R-L)/2,epsilon_R/2) and t=R-d.
Then L<t<R and p(t)>0. No x in Xi can satisfy
x>=t, because then t belongs to [L,x] and Xi(x)
would force p(t)<0. Consequently t is an upper bound
of Xi, and P4 yields B<=t<R.

Next, every u with L<=u<B has p(u)<0. Otherwise,
u is not an upper bound (since u<B), so some x in
Xi satisfies u<x; and Xi(x) implies p(u)<0,
contradiction. The value at u=B is negative by the
present assumption. Choose

    d'=min((R-B)/2,epsilon_B/2),  z=B+d'.

Now B<z<R and p(u)<0 for every B<=u<=z by P1.
If L<=u<=z, either u<B or B<=u. In the first case
use the preceding supremum argument; in the second
use the local sign estimate. Hence p(u)<0 throughout
[L,z], i.e. Xi(z). Since z>B, this contradicts
the upper-bound property of B. Thus p(B)<0 is
impossible, including the endpoint case B=L; B=R
was explicitly excluded before constructing z.

P7. The internal linear order satisfies exactly one of
p(B)<0, p(B)=0, 0<p(B). P5 and P6 eliminate the two
strict possibilities; hence p(B)=0. Via the already
established `HornerGraph`/formula semantic equivalence,
the geometric point B is a witness for the corresponding
root predicate. The proof uses **one** A13 application and
finitely many uses of derived field and order laws.

P8. For a>0 define the finite polynomial p(t)=t*t-a
entirely with `ScalarExpr` and `HornerGraph`. At L=0,
p(L)=-a<0. At R=a+1>0,
p(R)=a*a+a+1>0, since positive sums and products
are positive. P1-P7 produce B with 0<=B<=R and
B*B=a; `AxisNonneg` follows from 0<=B. For a=0,
take B=0 and invoke the proved zero-product relation.
This is exactly `PositiveSquareRootProperty`, with the
no-negative-a premise expressed by the positive ray.

P9. For odd n=2k+1, a_n!=0, define

    S=sum_(0<=i<n) |a_i/a_n|,  T=S+2.

The internal field gives T>S, T>1. For every i<n,
`T^i <= T^(n-1)`, so

    |sum_(i<n) a_i*T^i|
      <= |a_n|*S*T^(n-1)
      <  |a_n|*T^n.

At -T the absolute value of the lower-degree sum is
bounded by the same number, because `|-T|=T`.
Since n is odd, `a_n*(-T)^n=-a_n*T^n`, so the two
values p(-T),p(T) have opposite strict signs. If
a_n>0 choose L=-T, R=T; if a_n<0 apply P1-P7 to
the polynomial -p on the same interval, whose value
at L is negative and at R positive. A zero of -p
is a zero of p. This proves `OddPolynomialRootProperty`
for the same coefficient list, including n=1 and
all possible vanishing intermediate coefficients.

P10. The conclusion is the *internal* real-closedness
property, conditional only on the prior successful
synthetic derivations of the field and order laws C-D
and the formula/Horner semantic equivalence. The
formal Lean targets left by P1-P9 are those precise
dependencies; neither an ambient real field nor a
second independent number sort appears in the proof.

### Q. Backward multiplication projection: a synthetic inverse, now in Lean

Q1. The theorem `mulInverseLaw_of_playfair_tarski` above closes a genuine
field-law clause, **conditional only on geometric Playfair uniqueness**;
it does not assume `MulTotal`, multiplication commutativity or another
field-law clause. Let x be any existing scalar point other than O. Since
J and x are distinct, construct through I a line IU parallel to Jx.
The direction Jx is distinct from OJ: otherwise the lines Jx and OJ
meet at J, hence coincide, and x belongs both to OJ and OI, implying
x=O. Since IU has direction Jx and this direction is transverse to OJ,
their intersection W exists. It is unique by incidence. Replacing the
auxiliary endpoint U with W is justified by the two-point
line-extensionality theorem. Thus Jx is parallel to IW and W lies
on OJ. If W=O, IW would be the axis OI, forcing Jx parallel to OI,
although both lines contain x and J is outside OI. So W differs from O.

Q2. Construct through W a line WV parallel to IJ. Its direction is
transverse to OI: otherwise IJ would be parallel to OI, contradicting
their common point I and the noncollinearity of O,I,J. Intersect WV
with OI at Y. Since W≠O lies on OJ, W cannot equal Y, and changing the
auxiliary endpoint V to Y preserves the parallel relation. Therefore
IJ is parallel to WY and to YW. If Y=O, then IJ is parallel to OW;
because O,W,J are collinear and O≠W, this would make IJ parallel to OJ,
again contradicting their meeting at J and the frame noncollinearity.
Consequently Y≠O.

Q3. The quadruple of facts Y≠O, W∈OJ, IJ∥YW, Jx∥WI is precisely the
**nonzero branch of `MulGraph f x Y I`**. Hence Y is an actual geometric
inverse of x. The only future obligation to remove the geometric
Playfair hypothesis is the single Tarski `euclid`→Playfair theorem,
whose side-of-line subproof is developed in O and R. This constructive
inverse proof requires neither Pappus nor Desargues nor A13.

### R. Exact GeoCoq Ch09 `l9_5` proof, before Euclid-to-Playfair

R1. Write `TS(PQ,U,V)` for `OppositeSides P Q U V`, i.e. both U and V
are outside line PQ and some T on PQ satisfies Bet(U,T,V).
Write `Out(R,U,V)` for the ray condition from the *existing Tarski
betweenness* definition. The transport statement `l9_5` is:

    TS(PQ,A,C), Col(P,Q,R), Out(R,A,B)  ==>  TS(PQ,B,C).

In particular, B is outside PQ. To see this, if B lay on PQ, then
R and B would both lie on PQ, with B≠R by Out; thus RB is exactly the
line PQ by neutral line extensionality. But Out(R,A,B) implies A lies
on RB, contrary to A outside PQ. This is a *strict* use of Out; merely
asserting Col(R,A,B) without B≠R is insufficient.

R2. By the already constructed perpendicular-foot existence theorem,
choose foot points A0,C0,B0 on PQ of A,C,B, respectively. These three
feet are distinct from their off-line points, so the rays
Out(A0,A,A), Out(C0,C,C), Out(B0,B,B) hold, by Bet(T,T,T) and the
off-line inequalities. Construct M with Mid(M,A0,C0) and D with
Mid(M,A,D), using the internal midpoint-existence theorem. The
midpoint M lies on PQ, by the line-segment closure theorem derived
from Tarski incidence. Symmetrize both midpoint relations when the
argument order requires it: Mid(M,C0,A0) and Mid(M,D,A).

R3. Apply GeoCoq's *previously proved* Ch09 `l9_4_1` to
TS(PQ,C,A), feet C0,A0, Mid(M,C0,A0), Mid(M,D,A). Its exact conclusion
is the equivalence

    Out(C0,D,C)  <->  Out(A0,A,A).

The right side is true by R2, so obtain Out(C0,D,C). The converse
orientation Out(C0,C,D) follows directly from symmetry of the ray
condition (the two endpoints are on the same strict ray from C0).
The ray condition also yields D≠C0 and Col(C0,C,D). From
Perp(PQ,C,C0) and this collinearity, the geometric perpendicular
collinearity-transfer lemma gives Perp(PQ,D,C0). Thus the same point
C0 is a valid perpendicular foot for D.

R4. First apply Ch09 `l9_4_2` to TS(PQ,A,C), feet A0,C0, and the two
rays Out(A0,A,A), Out(C0,D,C). It concludes TS(PQ,A,D). Apply the
earlier Ch09 `l9_3` to this two-sided relation, the base-line points
M,R, Mid(M,A,D), and Out(R,A,B). It concludes TS(PQ,B,D). Finally
apply `l9_4_2` a *second* time, now to TS(PQ,B,D), using B0,C0 as
the feet and Out(B0,B,B), Out(C0,C,D) as the two ray conditions.
The conclusion is exactly TS(PQ,B,C). No continuity, Euclid axiom,
numeric axis, midpoint theorem from arithmetic, or independent line
separation postulate has entered this derivation.

R5. The synthetic dependency order is precise:

    neutral Bet/Cong/Pasch and midpoint existence
      -> perpendicular-foot existence (`l8_18_existence`)
      -> Ch09 `l9_3`, `l9_4_1`, `l9_4_2`
      -> Ch09 `l9_5`
      -> Ch09 outer Pasch, `l9_8_2`, same-side propagation
      -> Euclid-to-Playfair
      -> unique affine projections, and Q1-Q3 multiplication inverse.

In the original GeoCoq ordering `l9_4_2_aux` uses `l9_4_1` and `l9_3`,
but neither uses `l9_5`. This absence of backward dependencies is
essential: GeoCoq's later `outer_pasch` explicitly uses `l9_5` and
cannot be invoked inside its proof. The Lean translation of R3-R4
remains dependent on constructing the three exact *synthetic* Ch09
bridge lemmas in the current `Plane` vocabulary; `l9_5` itself is
not falsely marked as already typechecked.

R6. Expand the first of those three bridges from GeoCoq Ch09 `l9_3`.
Its premises are TS(PQ,A,C), M∈PQ, Mid(M,A,C), R∈PQ and Out(R,A,B),
and its conclusion is TS(PQ,B,C). The supplied midpoint *itself*
gives Bet(A,M,C) and M∈PQ. Thus its use as the existing crossing
witness is immediate: unlike the GeoCoq proof, the Lean reconstruction
does not need to name an arbitrary T from the TS premise and then
prove T=M by `l6_21`. The strict ray condition proves B outside PQ
as in R1. Only a crossing witness for segment BC remains.

R7. First ray-order case: Bet(R,A,B). Reflect B in M, obtaining B',
so Mid(M,B,B'), and reflect R in M, obtaining R', so Mid(M,R,R').
The reflection of A in M is C by Mid(M,A,C). The already proved
reflection order lemma GeoCoq Ch07 `l7_15`, applied to Bet(R,A,B),
gives Bet(B',C,R'). The midpoint of BB' also supplies Bet(B,M,B').
Apply **inner** Pasch to those two betweenness relations, with the
triangle whose vertices are B,B',R' and the two internal points
M,C. It constructs X satisfying Bet(M,X,R') and Bet(C,X,B).
The latter reverses to Bet(B,X,C), as required. M and R are on PQ,
so R' also lies on PQ by reflection collinearity. If M≠R',
`col_segment_closed_tarski` puts X on PQ because Bet(M,X,R').
If M=R', the betweenness identity forces X=M, which already lies
on PQ. Thus X is a valid two-sides crossing witness in either case.

R8. Second ray-order case: Bet(R,B,A). We already have Bet(A,M,C).
Apply inner Pasch directly to these two relations. It supplies X
such that Bet(B,X,C) and Bet(M,X,R). M,R lie on PQ; if M≠R,
the Tarski segment-closure theorem yields X∈PQ. If M=R,
betweenness identity gives X=M∈PQ. The cases X=M or X=R when
M≠R are included because Tarski's Bet is non-strict. Together with
B,C outside PQ, this proves TS(PQ,B,C) in the second ray case too.

R9. The `l9_3` derivation in R6-R8 uses only the neutral midpoint,
reflection, Pasch, and incidence lemmas already situated earlier in
the source proof, with no call to `l9_5` or its descendant outer-Pasch
theorem. This fixes the complete mathematical interface needed by R4:
the **specified** midpoint M, already certified to lie on PQ, is
directly used in both inner-Pasch constructions. The Lean theorem
`oppositeSides_ray_replace_of_midpoint_tarski` implements these two
branches without the surplus `l6_21` dependency. Its use of
`col_segment_closed_tarski` includes all endpoints, while the
R=M case in the reflection branch is discharged by `cong_identity`.

R10. Prove the previously missing **GeoCoq Ch08 l8_24** as a standalone
neutral-geometry lemma, before using any Ch09 transport result. Its
arguments are perpendiculars CS to SR and AR to SR, a point T on SR
with Bet(C,T,A), a copied point D with Bet(R,D,A) and SC congruent RD.
The perpendicular assumptions give S!=R, C!=S, A!=R, and C outside SR.
Apply primitive inner Pasch to the triangle (C,R,A) with internal
points T on CA and D on RA. This produces X with Bet(T,X,R) and
Bet(D,X,C). Since T and R are on SR, the already established segment
closure puts X on SR; Bet(D,X,C) also puts X on CD. The right-angle
characterization at S and R gives Per(R,S,C) and Per(S,R,A).
As D lies on RA and R!=A, right-angle transport along its second leg
gives Per(S,R,D). Apply the previously proved neutral-Tarski
`tarski_per_cong_tarski`, with initial congruence SC congruent RD,
intersection X on SR, and Bet(C,X,D). Its conclusion is the *other*
opposite-side congruence SD congruent CR. C,S,R are noncollinear,
because C lies outside SR; moreover C!=D, for otherwise Bet(C,X,C)
would force X=C on SR. Thus the proven Ch07 `l7_21` diagonal criterion
applies to the quadrilateral (S,C,R,D), with opposite side pairs
SC congruent RD and CR congruent DS, and intersection X of SR and CD.
It yields **Mid(X,S,R) and Mid(X,C,D)**. This is the full proof of
`perpendicular_crossing_common_midpoint_tarski`, with all degenerate
cases excluded explicitly and no extra midpoint-existence hypothesis.

R11. Establish GeoCoq Ch08 **l8_6** by reducing two right angles to
the primitive congruence-identity axiom. Suppose Per(A,B,T),
Per(C,B,T), and Bet(A,T,C). If A=C, between-identity forces A=T;
the right angle Per(T,B,T) with its collinear legs then forces B=T
by the previously proved right-angle degeneracy theorem. Otherwise,
reflect T about B to T'. Both right angles assert AT congruent AT'
and CT congruent CT'. Since A!=C and T is on the line AC, the
two-station equidistance theorem gives Cong(T,T,T,T'), so T=T'.
The midpoint condition Mid(B,T,T') then gives Bet(T,B,T), hence B=T.
This establishes `right_angle_crossing_vertex_tarski`. For opposite-
sided A,C, let T be a crossing of AC with PQ. When A and C have the
same perpendicular foot R on PQ, the perpendicular-at-foot property
gives Per(A,R,T) and Per(C,R,T); l8_6 now says R=T. Consequently
Bet(A,R,C), including the allowable endpoint cases. This is proved in
`oppositeSides_common_perpendicular_foot_tarski`, not assumed by
putting R at the crossing in the statement.

R12. Prove the strict-ray algebra used by Ch09 *before* the transport
arguments. `Out(O,A,B)` contains both A!=O and B!=O and exactly one
of Bet(O,A,B), Bet(O,B,A). Its symmetry swaps the two disjuncts.
For transitivity Out(O,A,B) and Out(O,B,C), split these two
disjunctions, giving four cases. The outward--outward case uses
Bet extension; outward--inward uses the order comparison of two
points inside segment OB; inward--outward uses the proved Ch05
comparison of two points on the same ray past B; inward--inward
uses Bet extension in the reversed order. In each case retain
A!=O and C!=O. Thus Out(O,A,C). If Bet(O,D,A) and O!=D, then
O!=A by between-identity, and the strict rays OD and OA coincide:
Out(O,U,A) iff Out(O,U,D). Finally, a reflection about M preserves
Out: the two reflected endpoints remain distinct from the reflected
origin because corresponding segments are congruent and Tarski's
congruence-identity excludes collapse; each Bet disjunct transports
under the already proved reflection-preserves-Bet lemma. These give
`out_trans_tarski`, `out_iff_of_between_target_tarski` and
`out_reflection_preserves_tarski`. This separation is important: the
Ch09 argument now uses an explicit ray theorem rather than an
unwritten appeal to orientation or diagram intuition.

R13. Finish **Ch09 l9_4_1_aux**. Its target is the equivalence
Out(R,U,A) iff Out(S,C,C'), assuming TS(PQ,A,C), R and S the
perpendicular feet of A and C, Mid(M,R,S), Mid(M,U,C'), and the
length comparison SC <= RA. First suppose R=S. The midpoint law
Mid(M,R,R) forces M=R; by R11 the common foot lies between A,C.
Reflect A across R to E. Both E and C lie on the ray from R opposite
to A (use the established Ch05 order comparison), and U,C' are
reflections about R. Reflection of strict rays gives
Out(R,U,A) iff Out(R,C',E), which equals Out(R,C',C) by ray
transitivity and its reverse, hence Out(R,C,C') by ray symmetry.
Next suppose R!=S. Unfold the length comparison to obtain D with
Bet(R,D,A) and Cong(S,C,R,D). D cannot equal R: otherwise
SC has zero length, implying S=C on PQ, contrary to C off PQ.
Since S and R are distinct points of PQ, replace the base name PQ
by SR in both perpendicular assertions and the opposite-side
condition. Apply R10 to a crossing T of CA with SR. It produces
M' with Mid(M',S,R) and Mid(M',C,D); by uniqueness of a segment's
midpoint and Mid(M,R,S), M'=M. Thus the three point reflections
around M are R<->S, D<->C, U<->C'. Because Bet(R,D,A) and R!=D,
Out(R,U,A) iff Out(R,U,D) by R12, which reflects to
Out(S,C',C), equivalent to Out(S,C,C'). Both directions use
the involution and preserve strict nondegeneracy. This is exactly
`perpendicular_midpoint_ray_transport_aux_tarski`. To remove the
comparison premise, apply the previously proved total comparison
SC<=RA or RA<=SC. In the second case exchange A with C, R with S,
reverse both midpoint pairs, and swap each pair of strict-ray
endpoints. The result is `perpendicular_midpoint_ray_transport_tarski`
(GeoCoq l9_4_1). There is no invocation of l9_5 here.

R14. Finish **Ch09 l9_4_2_aux** and then l9_4_2. For R=S, R11
gives Bet(A,R,C) and R12 shows that any U on the strict ray RA
and V on the strict ray RC satisfy Bet(U,R,V). Because R belongs
to PQ, an endpoint on either ray cannot lie on PQ: if U did,
the two distinct points R,U would determine PQ and force A into
PQ, contradicting TS; the same argument works for V. Thus R is
the crossing witness for TS(PQ,U,V). For R!=S, take the D from
SC<=RA as in R13 and apply R10 to construct M, a midpoint both
of SR and of CD. Reflect U in M to U'. Out(R,U,A) proves U
outside SR; the midpoint Bet(U,M,U') with M on SR makes U,U'
opposite-sided. By R13, Out(R,U,A) implies Out(S,C,U'). Combining
its symmetric form Out(S,U',C) with the supplied Out(S,V,C),
also reversed to Out(S,C,V), ray transitivity yields Out(S,U',V).
Apply the already proved `l9_3` to TS(SR,U',U), midpoint
Mid(M,U',U), and the ray from S through U' toward V. This gives
TS(SR,V,U); swap endpoints and replace the SR base by PQ to obtain
TS(PQ,U,V). The strict opposite-side condition was never replaced
with a mere collinearity condition. Finally, remove SC<=RA by
total segment comparison and swapping A,C and R,S, then swap the
resulting opposite sides back. These steps are implemented in
`two_sides_perp_ray_transport_aux_tarski` and
`two_sides_perp_ray_transport_tarski` (GeoCoq l9_4_2).

R15. Finish the *general* **Ch09 l9_5**, not only its midpoint case.
Given TS(PQ,A,C), R on PQ and Out(R,A,B), B is outside PQ:
if B were on PQ, R!=B and line extensionality would imply that
A (which is collinear with R,B) lies on PQ. Obtain perpendicular
feet A0,C0,B0 on PQ using the proved Gupta foot-existence theorem;
each endpoint differs from its foot, so the self-rays
Out(A0,A,A), Out(C0,C,C), Out(B0,B,B) are strict. Construct
M with Mid(M,A0,C0) and D with Mid(M,A,D). Segment closure puts M
on PQ. Apply l9_4_1 to the reversed two-sides relation TS(PQ,C,A),
the feet C0,A0, the reversed midpoint pair of feet and the
reflected pair D,A. Its equivalence states
Out(C0,D,C) iff Out(A0,A,A); the latter is true, so obtain the
former. Thus D!=C0 and C,C0,D lie on one line; replacing the
named second endpoint C of the perpendicular line CC0 by D
shows that C0 is also the perpendicular foot of D. Now apply
l9_4_2 with feet A0,C0 and rays Out(A0,A,A), Out(C0,D,C):
this yields TS(PQ,A,D). Apply the *midpoint* l9_3, with M on
PQ and Mid(M,A,D), to the given Out(R,A,B): it yields
TS(PQ,B,D). Apply l9_4_2 a second time, with feet B0,C0 and
rays Out(B0,B,B), Out(C0,C,D), to get precisely TS(PQ,B,C).
That theorem is `oppositeSides_ray_replace_tarski`. It uses only
Tarski's primitive plane axioms via the preceding constructed lemmas;
in particular no real coordinate system, no side-separation axiom,
and no use of Ch09 outer Pasch or of the theorem being proved.

R16. The GeoCoq order is now witnessed by the actual theorem bodies:
Ch07 midpoint and congruence results -> Ch08 right-angle and foot
results -> l8_24 -> Ch09 l9_3 and l9_4_1 -> l9_4_2 -> l9_5.
For the remaining Euclid-to-Playfair proof, the *next* derived tools
are Ch09 outer Pasch (which may now safely call l9_5), the same-side
transfer rules, and the final Euclidean uniqueness contradiction.
Once Playfair is proved, the already constructed graph operations
and multiplication inverse in Q become unconditional. All assertions
in R10--R15 name exact Lean theorem declarations above. The newly
added Lean code still requires compiler verification; source-level
proof structure must not be misreported as a successful typecheck.

R17. Outer Pasch (GeoCoq Ch09 `outer_pasch`, Tarski's Satz 9.6),
formulated in the primitive single-sorted language. Assume
Bet(A,C,P) and Bet(B,Q,C). We seek a point X with both
Bet(A,X,B) and Bet(P,Q,X). Decide whether C is on line PQ.

If Col(P,Q,C), first consider Bet(P,Q,C). Bet(A,C,P) implies
Bet(P,C,A) by symmetry; nested segment transitivity now gives
Bet(P,Q,A). We therefore take X=A. Bet(A,A,B) is one of the
previously deduced endpoint rules, completing this branch.
If instead Col(P,Q,C) and not Bet(P,Q,C), then neither P=Q nor
C=Q is possible: the corresponding degeneracies would make
Bet(P,Q,C) true. Expanding the three clauses of Col leaves only
Bet(Q,C,P) or Bet(Q,P,C). Thus Out(Q,P,C). In the first ray
order Bet(Q,P,C), the elementary inner-transitivity rule applied
to Bet(B,Q,C) yields Bet(B,Q,P). In the second ray order
Bet(Q,C,P), outer transitivity yields Bet(B,C,P), and nesting
with Bet(B,Q,C) yields Bet(B,Q,P). Either way, after symmetry,
Bet(P,Q,B); take X=B, noting Bet(A,B,B). None of these cases
uses the new opposite-side machinery.

Now suppose not Col(P,Q,C). If B=Q, choose X=B as before. In
the remaining case, P!=Q by noncollinearity, and C!=B since
otherwise Bet(B,Q,C) would force B=Q. Also B lies off PQ:
if B were on PQ, the distinct points B,Q would determine the
same line as P,Q, and Bet(B,Q,C) would put C on PQ, contradiction.
Since Q is on PQ and Bet(C,Q,B), we have OppositeSides(P,Q,C,B)
with the *explicit* crossing witness Q. Moreover Bet(A,C,P)
and P!=C entail A!=P and Out(P,C,A), because reversing the
between relation gives Bet(P,C,A). Apply the previously proved
Ch09 `l9_5`, taking R=P: it changes C to A and yields
OppositeSides(P,Q,A,B). Unpack this relation to obtain a point
X on PQ with Bet(A,X,B). The primitive **inner** Pasch applied
to the two betweenness relations Bet(P,C,A) and Bet(B,X,A)
produces a point T satisfying Bet(C,T,B) and Bet(X,T,P).
Because X and P both lie on PQ, the second relation implies
Col(P,Q,T) by segment-closure of a nondegenerate line. Because
Q and T both lie on BC, and C lies off PQ, the two distinct
lines PQ and CB intersect at **at most one** point. The points
Q and T are both intersections, hence T=Q. Substitution into
Bet(X,T,P) and reversal give Bet(P,Q,X). Together with
Bet(A,X,B), this gives the required witness X. The exact Lean
declaration for every branch is `outer_pasch_tarski`.

R18. Define two points A,B to be on the same side of line PQ
(`SameSides P Q A B`) precisely when there is a point C such
that each of A,B is on the opposite side from C. This is a
first-order definition using only the already defined
`OppositeSides`; it is not a new primitive. If one C witnesses
the two opposite-side clauses, it witnesses the same-side
statement immediately (`sameSides_of_common_opposite_tarski`).
Interchanging A and B preserves the conjunction, proving
`sameSides_symm_tarski`. OppositeSides(P,Q,A,A) is impossible:
its witness X would satisfy Bet(A,X,A), which by the Tarski
betweenness-identity law forces X=A, contradicting that X lies
on PQ whereas A is off PQ (`oppositeSides_irrefl_tarski`).
Finally, for any A off PQ, A!=P and the line AP is
nondegenerate. Reflect A in P. The reflection remains on AP,
its midpoint P lies on PQ, and both reflected endpoints lie
off PQ by line extensionality; thus A and its reflection are
opposite across PQ (`not_par_two_sides_tarski`). Using this
same point as the two witnesses establishes
`SameSides(P,Q,A,A)` (`sameSides_refl_off_line_tarski`).

R19. GeoCoq Ch09 `l9_8_2`: assume TS(PQ,U,W) and OS(PQ,U,V),
where OS(PQ,U,V) means that for some D both TS(PQ,U,D) and
TS(PQ,V,D). Choose crossing points X and Y on PQ for these
last two opposite-side relations, respectively. Thus
Bet(U,X,D), Bet(V,Y,D), Col(P,Q,X), Col(P,Q,Y); U and V
are both off PQ. Primitive inner Pasch, applied to the triangle
UVD with its boundary points X,Y, produces M satisfying
Bet(X,M,V) and Bet(Y,M,U), in precisely this order.

First assume M=Y. Then Bet(X,Y,V). If X!=Y, the two distinct
points X,Y of PQ determine the same line PQ, and the last
betweenness puts V on PQ, a contradiction. Hence X=Y.
Similarly, if M=X, then Bet(Y,X,U) and the off-line condition
on U again force X=Y. In either equality case, the two rays
from the common crossing X to U and V both point away from D:
Bet(D,X,U) and Bet(D,X,V). Since D!=X, the Ch05 ray-order
comparison gives either Bet(D,U,V) or Bet(D,V,U). Applying
the elementary exchange rule yields Bet(X,U,V) or Bet(X,V,U).
As U,V are off PQ, neither equals X, so Out(X,U,V). The
already established `l9_5` changes the first endpoint of
TS(PQ,U,W) to V, giving TS(PQ,V,W). This common-crossing
argument is `oppositeSides_shared_crossing_transport_tarski`.

In the remaining case M!=Y and M!=X, Bet(Y,M,U) and the
fact that U is off PQ yield the strict ray relation Out(Y,U,M).
Apply `l9_5` to TS(PQ,U,W), obtaining TS(PQ,M,W). Next,
Bet(X,M,V) and V off PQ yield Out(X,M,V). Apply `l9_5`
once more to obtain TS(PQ,V,W). Thus all three branches
prove `oppositeSides_sameSides_transport_tarski` (GeoCoq
`l9_8_2`), without a same-side axiom and without a field.
The strict-raying directions here were checked against the
actual inner-Pasch conclusion; reversing its two outputs
would invalidate the proof.

R20. Same-side transitivity is now a direct consequence of
R19. Suppose OS(PQ,U,V) is witnessed by a point D, so
TS(PQ,U,D) and TS(PQ,V,D). Suppose also OS(PQ,V,W).
Apply R19 to TS(PQ,V,D) and OS(PQ,V,W), obtaining
TS(PQ,W,D). The original D witnesses OS(PQ,U,W). This is
`sameSides_trans_tarski`. If TS(PQ,U,V) and OS(PQ,U,V)
both held, R19 with W=V would give TS(PQ,V,V), contradicting
R18's irreflexivity theorem. This is
`oppositeSides_not_sameSides_tarski`. These are the strict
same-side laws required by the Euclid-to-Playfair argument.

R21. One useful proof extracted from the independently written
field-law draft is `AddRightZeroLaw f`: its statement expands
to `∀ a : AxisPoint f, AddGraph f a (axisZero f) a`. The
existing geometry theorem `add_zero_right_tarski f a` gives
exactly that proposition for an arbitrary axis point a, so
universal introduction discharges it without assuming
AddTotal, Playfair, or a field law. This is recorded as
`addRightZeroLaw_tarski`. The proposed declarations involving
Playfair, field distributivity, general polynomial IVT, and
real closure contained explicit `sorry` placeholders and were
not merged as proofs. The separate generic ordered-field
Horner draft was not inserted as a substitute for a one-sorted
geometric field interpretation; the internal Horner and A13
definitions already occur in the canonical file. All newly
added Lean bodies remain subject to actual typechecking.
-/

/-!
### Synthetic Euclid-to-Playfair continuation

This section develops the missing same-side dichotomy from perpendicular
constructions, then uses Tarski's Euclidean parallel axiom to prove Playfair
uniqueness.  Only the single-sorted `Plane` structure and lemmas developed
above are used.  This appended proof has been reviewed against the declared
types, but an external Lean 4 typecheck is still required.
-/

namespace TarskiField

section EuclidPlayfairAndOperations

variable {Point : Type u} [Plane Point]
open Plane

/-- Perpendicular lines with a common endpoint cannot be collinear. -/
private theorem perp_at_endpoint_noncol_tarski
    {F R P : Point} (hPerp : TarskiPerp F R P F) :
    ¬ Col F R P := by
  intro hColFRP
  obtain ⟨X, hFR, hPF, hXFR, _hXPF, hRight⟩ := hPerp
  have hPerFXP : TarskiPer F X P :=
    hRight F P
      (col_swap_last (col_left F R))
      (col_swap_last (col_left P F))
  have hPerRXP : TarskiPer R X P :=
    hRight R P (col_left R F) (col_swap_last (col_left P F))
  have hColFXP : Col F X P := by
    by_cases hFX : F = X
    · rw [hFX]
      exact col_swap_last (col_left X P)
    · have hline : ∀ S : Point, Col F R S ↔ Col F X S :=
        col_line_extensionality_tarski hFR hFX
          (col_left F R) (col_rotate hXFR)
      exact (hline P).mp hColFRP
  have hColRXP : Col R X P := by
    by_cases hRX : R = X
    · rw [hRX]
      exact col_swap_last (col_left X P)
    · have hline : ∀ S : Point, Col F R S ↔ Col R X S :=
        col_line_extensionality_tarski hFR hRX
          (col_right F R) (col_rotate hXFR)
      exact (hline P).mp hColFRP
  have hDeg1 : F = X ∨ P = X :=
    tarski_per_collinear_legs_degenerate_tarski hPerFXP hColFXP
  have hDeg2 : R = X ∨ P = X :=
    tarski_per_collinear_legs_degenerate_tarski hPerRXP hColRXP
  have hPX : P = X := by
    rcases hDeg1 with hFX | hPX
    · rcases hDeg2 with hRX | hPX
      · exact False.elim (hFR (hFX.trans hRX.symm))
      · exact hPX
    · exact hPX
  have hPerFPF : TarskiPer F P F := by
    simpa [hPX] using
      hRight F F (col_swap_last (col_left F R)) (col_left F P)
  obtain ⟨F', hMid, hCong⟩ := hPerFPF
  have hFF' : F = F' := cong_identity F F' F (cong_symm hCong)
  have hFPF : Bet F P F := by simpa [← hFF'] using hMid.1
  exact hPF (between_identity F P hFPF).symm

/-- Two points on the unique perpendicular through F lie on one line. -/
private theorem common_perp_legs_collinear_tarski
    {F R U P : Point}
    (hFR : F ≠ R)
    (hPerRFU : TarskiPer R F U)
    (hPerRFP : TarskiPer R F P) :
    Col F U P := by
  have hUFR : TarskiPer U F R := tarski_per_swap_legs_tarski hPerRFU
  have hPFR : TarskiPer P F R := tarski_per_swap_legs_tarski hPerRFP
  obtain ⟨R', hMidU, hUR⟩ := hUFR
  obtain ⟨R'', hMidP, hPR⟩ := hPFR
  have hR'eq : R'' = R' := by
    obtain ⟨_, _, huniq⟩ := opposite_exists_unique F R
    have h1 := huniq R' ⟨hMidU.1, cong_symm hMidU.2⟩
    have h2 := huniq R'' ⟨hMidP.1, cong_symm hMidP.2⟩
    exact h2.trans h1.symm
  subst R''
  have hRR' : R ≠ R' := by
    intro hEq
    have hRFR : Bet R F R := by simpa [← hEq] using hMidU.1
    exact hFR (between_identity R F hRFR).symm
  have hFR_cong : Cong F R F R' := hMidU.2
  exact Plane.upper_dim F U P R R' hRR' hFR_cong hUR hPR

/-- GeoCoq's `not_two_sides_one_side`, with perpendicularity constructed
entirely from the Tarski primitives. -/
theorem not_two_sides_one_side_tarski
    {A B U V : Point}
    (hUoff : ¬ Col A B U) (hVoff : ¬ Col A B V)
    (hNotTS : ¬ OppositeSides A B U V) :
    SameSides A B U V := by
  obtain ⟨F, hFAB, hPerpU⟩ := perpendicular_foot_exists_tarski hUoff
  have hAB : A ≠ B := noncol_ne_first_second hUoff
  have hFne : ∃ R : Point, Col A B R ∧ F ≠ R := by
    by_cases hFA : F = A
    · exact ⟨B, col_right A B, by simpa [hFA] using hAB⟩
    · exact ⟨A, col_left A B, hFA⟩
  obtain ⟨R, hRAB, hFR⟩ := hFne
  obtain ⟨P, T, hPerpP, hTFR, hVTP⟩ :=
    gupta_l8_21_tarski (A := F) (B := R) (C := V) hFR
  have hlineAB_FR : ∀ S : Point, Col A B S ↔ Col F R S :=
    col_line_extensionality_tarski hAB hFR hFAB hRAB
  have hTAB : Col A B T := (hlineAB_FR T).mpr hTFR
  have hPoffFR : ¬ Col F R P := perp_at_endpoint_noncol_tarski hPerpP
  have hPoff : ¬ Col A B P :=
    fun hPAB => hPoffFR ((hlineAB_FR P).mp hPAB)
  have hTSVP : OppositeSides A B V P :=
    ⟨hVoff, hPoff, T, hTAB, hVTP⟩
  have hPerpAtU : TarskiPerpAt F A B U F :=
    tarski_perp_foot_as_perp_at_tarski hUoff hFAB hPerpU
  have hPerpAtP : TarskiPerpAt F F R P F :=
    tarski_perp_foot_as_perp_at_tarski hPoffFR (col_left F R) hPerpP
  have hPerRFU : TarskiPer R F U :=
    hPerpAtU.2.2.2.2 R U (col_rotate (col_rotate hRAB))
      (col_swap_last (col_left U F))
  have hPerRFP : TarskiPer R F P :=
    hPerpAtP.2.2.2.2 R P (col_left R F)
      (col_swap_last (col_left P F))
  have hColFUP : Col F U P :=
    common_perp_legs_collinear_tarski hFR hPerRFU hPerRFP
  have hUF : U ≠ F :=
    fun h => hUoff (by simpa [h] using hFAB)
  have hPF : P ≠ F :=
    fun h => hPoff (by simpa [h] using hFAB)
  have hBetOrOut : Bet U F P ∨ Out F U P := by
    rcases hColFUP with hFUP | hUPF | hPFU
    · exact Or.inr ⟨hUF, hPF, Or.inl hFUP⟩
    · exact Or.inr ⟨hUF, hPF, Or.inr (bet_symm hUPF)⟩
    · exact Or.inl (bet_symm hPFU)
  rcases hBetOrOut with hUFP | hOutFUP
  · exact ⟨P, ⟨hUoff, hPoff, F, hFAB, hUFP⟩, hTSVP⟩
  · have hTSPV : OppositeSides A B P V := oppositeSides_symm_tarski hTSVP
    have hTSUV : OppositeSides A B U V :=
      oppositeSides_ray_replace_tarski hTSPV hFAB
        (out_swap_tarski hOutFUP)
    exact False.elim (hNotTS hTSUV)

/-- An intersecting line has a point on the prescribed opposite side. -/
theorem not_par_other_side_tarski
    {A B C D I P : Point}
    (hCD : C ≠ D)
    (hIAB : Col A B I) (hICD : Col C D I)
    (hCoff : ¬ Col A B C) (hPoff : ¬ Col A B P) :
    ∃ Q : Point, Col C D Q ∧ OppositeSides A B P Q := by
  obtain ⟨Y, hYCD, hTSCY⟩ :=
    not_par_two_sides_tarski hCD hIAB hICD hCoff
  by_cases hTSPC : OppositeSides A B P C
  · exact ⟨C, col_left C D, hTSPC⟩
  · have hOSPC : SameSides A B P C :=
      not_two_sides_one_side_tarski hPoff hCoff hTSPC
    have hOSCP : SameSides A B C P := sameSides_symm_tarski hOSPC
    have hTSPY : OppositeSides A B P Y :=
      oppositeSides_sameSides_transport_tarski hTSCY hOSCP
    exact ⟨Y, hYCD, hTSPY⟩

/-- Strict parallels put every two of their points on the same side. -/
theorem strict_parallel_sameSides_tarski
    {A B C D P Q : Point}
    (hpar : Parallel A B C D)
    (hPoff : ¬ Col A B P)
    (hPCD : Col C D P) (hQCD : Col C D Q) :
    SameSides A B P Q := by
  have hdisj : ∀ S : Point, ¬ (Col A B S ∧ Col C D S) :=
    playfair_strict_of_off_reference_tarski hpar hPoff hPCD
  have hQoff : ¬ Col A B Q :=
    fun hQAB => hdisj Q ⟨hQAB, hQCD⟩
  have hNotTS : ¬ OppositeSides A B P Q :=
    playfair_parallel_line_not_opposite_sides_tarski hpar hPCD hQCD
  exact not_two_sides_one_side_tarski hPoff hQoff hNotTS

/-- Playfair uniqueness derived from Tarski's synthetic Euclid axiom. -/
theorem tarski_playfair
    (A B C D E F P : Point)
    (hparCD : Parallel A B C D) (hparEF : Parallel A B E F)
    (hPCD : Col C D P) (hPEF : Col E F P) :
    ∀ S : Point, Col C D S ↔ Col E F S := by
  classical
  by_cases hPAB : Col A B P
  · have hsameCD : ∀ S, Col A B S ↔ Col C D S :=
      parallel_same_of_intersection hparCD hPAB hPCD
    have hsameEF : ∀ S, Col A B S ↔ Col E F S :=
      parallel_same_of_intersection hparEF hPAB hPEF
    intro S
    exact (hsameCD S).symm.trans (hsameEF S)
  · by_contra hdiff
    have hCD : C ≠ D := hparCD.2.1
    have hEF : E ≠ F := hparEF.2.1
    have hQ0 : ∃ Q₀ : Point, Col E F Q₀ ∧ ¬ Col C D Q₀ := by
      rcases playfair_distinct_lines_have_external_endpoint_tarski
          hCD hEF hdiff with hE | hF
      · exact ⟨E, col_left E F, hE⟩
      · exact ⟨F, col_right E F, hF⟩
    obtain ⟨Q₀, hQ0EF, hQ0offCD⟩ := hQ0
    have hPQ0 : P ≠ Q₀ := by
      intro hEq
      exact hQ0offCD (by simpa [hEq] using hPCD)
    have hEF_PQ0 : ∀ S, Col E F S ↔ Col Q₀ P S :=
      col_line_extensionality_tarski hEF hPQ0.symm hQ0EF hPEF
    have hdisjCD : ∀ S, ¬ (Col A B S ∧ Col C D S) :=
      playfair_strict_of_off_reference_tarski hparCD hPAB hPCD
    have hdisjEF : ∀ S, ¬ (Col A B S ∧ Col E F S) :=
      playfair_strict_of_off_reference_tarski hparEF hPAB hPEF
    have hAoffCD : ¬ Col C D A :=
      fun hACD => hdisjCD A ⟨col_left A B, hACD⟩
    obtain ⟨C', hC'Q0P, hTSAC'⟩ :=
      not_par_other_side_tarski (A := C) (B := D)
        (C := Q₀) (D := P) (I := P)
        hPQ0.symm hPCD (col_right Q₀ P) hQ0offCD hAoffCD
    have hC'EF : Col E F C' := (hEF_PQ0 C').mpr hC'Q0P
    obtain ⟨_, hC'offCD, B₀, hB0CD, hAB0C'⟩ := hTSAC'
    have hPC' : P ≠ C' := by
      intro hEq
      exact hC'offCD (by simpa [hEq] using hPCD)
    have hB0P : B₀ ≠ P := by
      intro hEq
      have hAPC' : Bet A P C' := by simpa [hEq] using hAB0C'
      have hPC'A : Col P C' A := col_rotate (Or.inl hAPC')
      have hEF_PC' : ∀ S, Col E F S ↔ Col P C' S :=
        col_line_extensionality_tarski hEF hPC' hPEF hC'EF
      exact hdisjEF A ⟨col_left A B, (hEF_PC' A).mpr hPC'A⟩
    obtain ⟨C1, hMidPC'C1, _⟩ := mul_reflection_exists_unique P C'
    have hPC1 : P ≠ C1 := by
      intro hEq
      have hPC'eq : P = C' :=
        cong_identity P C' P
          (by simpa [hEq] using hMidPC'C1.2)
      exact hPC' hPC'eq
    have hEF_PC' : ∀ S, Col E F S ↔ Col P C' S :=
      col_line_extensionality_tarski hEF hPC' hPEF hC'EF
    have hC1EF : Col E F C1 :=
      (hEF_PC' C1).mpr (col_swap (Or.inl hMidPC'C1.1))
    have hEF_PC1 : ∀ S, Col E F S ↔ Col P C1 S :=
      col_line_extensionality_tarski hEF hPC1 hPEF hC1EF
    have hPB0C1 : ¬ Col P B₀ C1 := by
      intro hCol
      have hB0PC1 : Col P C1 B₀ := col_swap_last hCol
      have hB0EF : Col E F B₀ := (hEF_PC1 B₀).mpr hB0PC1
      have hCD_PB0 : ∀ S, Col C D S ↔ Col P B₀ S :=
        col_line_extensionality_tarski hCD hB0P.symm hPCD hB0CD
      have hEF_PB0 : ∀ S, Col E F S ↔ Col P B₀ S :=
        col_line_extensionality_tarski hEF hB0P.symm hPEF hB0EF
      exact hdiff (fun S => (hCD_PB0 S).trans (hEF_PB0 S).symm)
    obtain ⟨D1, hB0D1C1, hPD1A⟩ :=
      Plane.inner_pasch A C1 C' B₀ P
        hAB0C' (bet_symm hMidPC'C1.1)
    obtain ⟨X, Y, hPB0X, hPC1Y, hXAY, _⟩ :=
      playfair_euclid_wedge_nondegenerate_tarski hPB0C1 hPD1A hB0D1C1
    have hCD_PB0 : ∀ S, Col C D S ↔ Col P B₀ S :=
      col_line_extensionality_tarski hCD hB0P.symm hPCD hB0CD
    have hXCD : Col C D X := (hCD_PB0 X).mpr (Or.inl hPB0X)
    have hYEF : Col E F Y := (hEF_PC1 Y).mpr (Or.inl hPC1Y)
    have hXoffAB : ¬ Col A B X :=
      fun hXAB => hdisjCD X ⟨hXAB, hXCD⟩
    have hYoffAB : ¬ Col A B Y :=
      fun hYAB => hdisjEF Y ⟨hYAB, hYEF⟩
    have hTSXY : OppositeSides A B X Y :=
      ⟨hXoffAB, hYoffAB, A, col_left A B, hXAY⟩
    have hOSPX : SameSides A B P X :=
      strict_parallel_sameSides_tarski hparCD hPAB hPCD hXCD
    have hOSPY : SameSides A B P Y :=
      strict_parallel_sameSides_tarski hparEF hPAB hPEF hYEF
    have hOSXY : SameSides A B X Y :=
      sameSides_trans_tarski (sameSides_symm_tarski hOSPX) hOSPY
    exact oppositeSides_not_sameSides_tarski hTSXY hOSXY

/-- Arithmetic graphs are total under the internal Tarski geometry. -/
theorem operation_graphs_total_tarski (f : Frame Point) :
    AddTotal f ∧ MulTotal f :=
  both_operation_graphs_total_of_playfair_tarski f tarski_playfair

/-- Arithmetic graphs are functional under the internal Tarski geometry. -/
theorem operation_graphs_functional_tarski (f : Frame Point) :
    AddFunctional f ∧ MulFunctional f :=
  both_operation_graphs_functional_of_playfair_tarski f tarski_playfair

/-- Geometric multiplication: existence, uniqueness, unit, and inversion. -/
theorem mulKernel_tarski (f : Frame Point) :
    MulTotal f ∧ MulFunctional f ∧ MulLeftOneLaw f ∧ MulInverseLaw f :=
  mulKernel_of_playfair_tarski f tarski_playfair

end EuclidPlayfairAndOperations

end TarskiField


/-!
# TarskiGeometry: Zero-`sorry` Additive Inverse & Order Laws (B3, D1, D3)

This draft builds directly on `TarskiUnifiedOneFile.lean` (v46, which includes
`tarski_playfair`, `operation_graphs_total_tarski`, `operation_graphs_functional_tarski`,
`mulKernel_tarski`, `oppositeSides_sameSides_transport_tarski`, `sameSides_trans_tarski`,
and `oppositeSides_not_sameSides_tarski`).

All proofs in this file are complete and contain **zero `sorry`s**, using only
the `Plane` axioms and theorems already present in v46:
1. `addInverseLaw_tarski` (`AddInverseLaw f`, B3)
2. `addGraph_zero_iff_midpoint_tarski` (`AddGraph f a b (axisZero f) ↔ MulMidpoint f.O a.1 b.1`)
3. `positiveTrichotomy_tarski` (`PositiveTrichotomy f`, D1)
4. `positiveProper_tarski` (`PositiveProper f`, D3)
-/

namespace TarskiField

section AddInvAndOrderDraft

variable {Point : Type u} [Plane Point]
open Plane

private theorem sameSides_symm_v46 {A B P Q : Point}
    (h : SameSides A B P Q) : SameSides A B Q P := by
  obtain ⟨W, hPW, hQW⟩ := h
  exact ⟨W, hQW, hPW⟩

/-- Helper: if `Bet J T T'` (or `Bet J T' T`) and `Cong J T J T'`, then `T = T'`. -/
private theorem bet_cong_same_origin_eq {J T T' : Point}
    (hBet : Bet J T T') (hCong : Cong J T J T') : T = T' := by
  by_cases hJT : J = T
  · have hJT' : J = T' := cong_identity J T' J (by simpa [← hJT] using (cong_symm hCong))
    exact hJT.symm.trans hJT'
  · obtain ⟨P, hTJP, hJP⟩ := segment_extension_nontrivial T J
    have hPJT : Bet P J T := bet_symm hTJP
    have hPJT' : Bet P J T' :=
      bet_extend hPJT (bet_outer_trans hPJT hBet hJT)
    exact segment_extension_unique hJP.symm hPJT hPJT' hCong

/-- Helper: `Parallel A B C D` with `B ∈ C D`? No, `Col C D X` and `¬ Col A B P` gives
    `SameSides A B P Q` via `strict_parallel_sameSides_tarski` (from v46). -/
private theorem add_first_proj_midpoint_witness
    (f : Frame Point) (a : AxisPoint f) (ha : a.1 ≠ f.O) :
    ∃ T : Point,
      Parallel f.O f.J a.1 T ∧
      Parallel f.O f.I f.J T ∧
      Cong f.J T f.O a.1 := by
  have hOI_Oa : ∀ S : Point, Col f.O f.I S ↔ Col f.O a.1 S :=
    col_line_extensionality_tarski f.O_ne_I ha.symm (col_left f.O f.I) a.2
  have hNoncol : ¬ Col f.O f.J a.1 := by
    intro h
    exact f.noncol ((hOI_Oa f.J).mpr (col_swap_last h))
  obtain ⟨M, hMidJa⟩ := midpoint_existence_tarski f.J a.1
  obtain ⟨T, hMidOT, _⟩ := mul_reflection_exists_unique M f.O
  obtain ⟨hOJ_Ta, hJT_aO⟩ :=
    midpoint_diagonals_parallelogram_tarski hNoncol hMidJa hMidOT
  have hJT_Oa : Parallel f.J T f.O a.1 := parallel_reverse_right hJT_aO
  have hJT_OI : Parallel f.J T f.O f.I :=
    parallel_retarget_right_of_line_eq hJT_Oa f.O_ne_I (fun S => (hOI_Oa S).symm)
  have hCong : Cong f.J T f.O a.1 :=
    cong_symm (cong_reverse_left
      (mul_reflection_preserves_cong hMidJa (mul_midpoint_reverse hMidOT)))
  exact ⟨T, parallel_reverse_right hOJ_Ta, parallel_symm hJT_OI, hCong⟩

/-- Helper: construct the additive inverse witness `b` as the reflection of `a` across `O`,
    and prove `AddGraph f a b (axisZero f)` unconditionally from `Plane`. -/
theorem addGraph_of_midpoint_zero_tarski
    (f : Frame Point) (a b : AxisPoint f)
    (hMid : MulMidpoint f.O a.1 b.1) :
    AddGraph f a b (axisZero f) := by
  by_cases ha : a.1 = f.O
  · have hbO : f.O = b.1 := by
      have hOb : Bet b.1 f.O b.1 := by
        have h1 : Cong f.O b.1 f.O f.O := by simpa [ha] using (cong_symm hMid.2)
        have hbfO : b.1 = f.O := (cong_identity f.O b.1 f.O h1).symm
        simpa [hbfO] using (bet_start f.O f.O)
      have h1 : Cong f.O b.1 f.O f.O := by simpa [ha] using (cong_symm hMid.2)
      exact cong_identity f.O b.1 f.O h1
    exact Or.inl ⟨ha, Subtype.ext hbO⟩
  · have hbO : b.1 ≠ f.O := by
      intro h
      have haO : a.1 = f.O :=
        (cong_identity f.O a.1 f.O (by simpa [h] using hMid.2)).symm
      exact ha haO
    obtain ⟨T, hOJ_aT, hOI_JT, hCong_JT_Oa⟩ :=
      add_first_proj_midpoint_witness f a ha
    have hOI_Ob : ∀ S : Point, Col f.O f.I S ↔ Col f.O b.1 S :=
      col_line_extensionality_tarski f.O_ne_I hbO.symm (col_left f.O f.I) b.2
    have hNoncol_bJO : ¬ Col b.1 f.J f.O := by
      intro h
      have hObJ : Col f.O b.1 f.J := col_reverse_cycle h
      exact f.noncol ((hOI_Ob f.J).mpr hObJ)
    obtain ⟨N, hMidJO⟩ := midpoint_existence_tarski f.J f.O
    obtain ⟨T', hMidbT', _⟩ := mul_reflection_exists_unique N b.1
    obtain ⟨hbJ_T'O, hJT'_Ob⟩ :=
      midpoint_diagonals_parallelogram_tarski hNoncol_bJO hMidJO hMidbT'
    have hOI_JT' : Parallel f.O f.I f.J T' :=
      parallel_symm
        (parallel_retarget_right_of_line_eq hJT'_Ob f.O_ne_I (fun S => (hOI_Ob S).symm))
    have hCong_JT'_Ob : Cong f.J T' f.O b.1 :=
      cong_symm (mul_reflection_preserves_cong hMidJO (mul_midpoint_reverse hMidbT'))
    have hCong_JT_JT' : Cong f.J T f.J T' :=
      cong_trans hCong_JT_Oa (cong_trans hMid.2 (cong_symm hCong_JT'_Ob))
    have hSameLine : ∀ S : Point, Col f.J T S ↔ Col f.J T' S :=
      tarski_playfair f.O f.I f.J T f.J T' f.J hOI_JT hOI_JT'
        (col_left f.J T) (col_left f.J T')
    have hCol_JTT' : Col f.J T T' := (hSameLine T').mpr (col_right f.J T')
    have hT_eq_T' : T = T' := by
      by_contra hTT'
      have hBet_TJ_T' : Bet T f.J T' := by
        rcases hCol_JTT' with hJTT' | hTT'J | hT'JT
        · exact False.elim (hTT' (bet_cong_same_origin_eq hJTT' hCong_JT_JT'))
        · exact False.elim (hTT' (bet_cong_same_origin_eq (bet_symm hTT'J) (cong_symm hCong_JT_JT')).symm)
        · exact bet_symm hT'JT
      have ha_off_OJ : ¬ Col f.O f.J a.1 := by
        intro h
        exact ha (frame_axes_intersection_only_origin_tarski f a.1 a.2 h)
      have hb_off_OJ : ¬ Col f.O f.J b.1 := by
        intro h
        exact hbO (frame_axes_intersection_only_origin_tarski f b.1 b.2 h)
      have hdisj_aT : ∀ S, ¬ (Col f.O f.J S ∧ Col a.1 T S) :=
        playfair_strict_of_off_reference_tarski hOJ_aT ha_off_OJ (col_left a.1 T)
      have hT_off_OJ : ¬ Col f.O f.J T := fun h => hdisj_aT T ⟨h, col_right a.1 T⟩
      have hN_OJ : Col f.O f.J N :=
        col_segment_closed_tarski f.O_ne_J (col_right f.O f.J) (col_left f.O f.J) hMidJO.1
      have hNb : N ≠ b.1 := fun h => hb_off_OJ (by simpa [h] using hN_OJ)
      have hNT' : N ≠ T' := by
        intro h
        have hNb' : N = b.1 :=
          cong_identity N b.1 N (by simpa [h] using hMidbT'.2)
        exact hNb hNb'
      have hT'_off_OJ : ¬ Col f.O f.J T' := by
        intro hT'OJ
        have hline : ∀ S, Col f.O f.J S ↔ Col N T' S :=
          col_line_extensionality_tarski f.O_ne_J hNT' hN_OJ hT'OJ
        exact hb_off_OJ ((hline b.1).mpr (Or.inr (Or.inr hMidbT'.1)))
      have hTSTT' : OppositeSides f.O f.J T T' :=
        ⟨hT_off_OJ, hT'_off_OJ, f.J, col_right f.O f.J, hBet_TJ_T'⟩
      have hOS_aT : SameSides f.O f.J a.1 T :=
        strict_parallel_sameSides_tarski hOJ_aT ha_off_OJ (col_left a.1 T) (col_right a.1 T)
      have hTS_ab : OppositeSides f.O f.J a.1 b.1 :=
        ⟨ha_off_OJ, hb_off_OJ, f.O, col_left f.O f.J, hMid.1⟩
      have hTS_T'b : OppositeSides f.O f.J T' b.1 :=
        ⟨hT'_off_OJ, hb_off_OJ, N, hN_OJ, bet_symm hMidbT'.1⟩
      have hOS_aT' : SameSides f.O f.J a.1 T' := ⟨b.1, hTS_ab, hTS_T'b⟩
      have hOS_TT' : SameSides f.O f.J T T' :=
        sameSides_trans_tarski (sameSides_symm_v46 hOS_aT) hOS_aT'
      exact oppositeSides_not_sameSides_tarski hTSTT' hOS_TT'
    have hJb_TO : Parallel f.J b.1 T f.O := by
      simpa [← hT_eq_T'] using parallel_reverse_left hbJ_T'O
    exact Or.inr ⟨ha, T, hOJ_aT, hOI_JT, hJb_TO⟩

/-- B3: Every axis point has a geometric additive inverse. -/
theorem addInverseLaw_tarski (f : Frame Point) : AddInverseLaw f := by
  intro a
  by_cases ha : a.1 = f.O
  · refine ⟨axisZero f, ?_⟩
    exact addGraph_of_midpoint_zero_tarski f a (axisZero f)
      ⟨by simpa [axisZero, ha] using bet_start f.O f.O,
       by simpa [axisZero, ha] using congr_refl f.O f.O⟩
  · obtain ⟨bPt, hMid, _⟩ := mul_reflection_exists_unique f.O a.1
    have hOI_Oa : ∀ S : Point, Col f.O f.I S ↔ Col f.O a.1 S :=
      col_line_extensionality_tarski f.O_ne_I (Ne.symm ha) (col_left f.O f.I) a.2
    have hbCol : Col f.O f.I bPt :=
      (hOI_Oa bPt).mpr (Or.inr (Or.inr (bet_symm hMid.1)))
    let b : AxisPoint f := ⟨bPt, hbCol⟩
    exact ⟨b, addGraph_of_midpoint_zero_tarski f a b hMid⟩

/-- Exact characterization of `AddGraph f a b (axisZero f)` as midpoint reflection across `O`. -/
theorem addGraph_zero_iff_midpoint_tarski
    (f : Frame Point) (a b : AxisPoint f) :
    AddGraph f a b (axisZero f) ↔ MulMidpoint f.O a.1 b.1 := by
  constructor
  · intro hAdd
    rcases hAdd with ⟨haO, hbz⟩ | ⟨haO, T, hOJ_aT, hOI_JT, hJb_TO⟩
    · have hbO : b.1 = f.O := by simpa [axisZero] using (congrArg Subtype.val hbz).symm
      rw [haO, hbO]
      exact ⟨bet_start f.O f.O, congr_refl f.O f.O⟩
    · obtain ⟨bPt', hMid', _⟩ := mul_reflection_exists_unique f.O a.1
      have hOI_Oa : ∀ S : Point, Col f.O f.I S ↔ Col f.O a.1 S :=
        col_line_extensionality_tarski f.O_ne_I haO.symm (col_left f.O f.I) a.2
      have hb'Col : Col f.O f.I bPt' :=
        (hOI_Oa bPt').mpr (Or.inr (Or.inr (bet_symm hMid'.1)))
      let b' : AxisPoint f := ⟨bPt', hb'Col⟩
      have hAdd' : AddGraph f a b' (axisZero f) :=
        addGraph_of_midpoint_zero_tarski f a b' hMid'
      rcases hAdd' with ⟨ha0, _⟩ | ⟨_, T', hOJ_aT', hOI_JT', hJb'_T'O⟩
      · exact False.elim (haO ha0)
      · have hSame_aT : ∀ S : Point, Col a.1 T S ↔ Col a.1 T' S :=
          tarski_playfair f.O f.J a.1 T a.1 T' a.1 hOJ_aT hOJ_aT'
            (col_left a.1 T) (col_left a.1 T')
        have hSame_JT : ∀ S : Point, Col f.J T S ↔ Col f.J T' S :=
          tarski_playfair f.O f.I f.J T f.J T' f.J hOI_JT hOI_JT'
            (col_left f.J T) (col_left f.J T')
        have hT'_aT : Col a.1 T T' := (hSame_aT T').mpr (col_right a.1 T')
        have hT'_JT : Col f.J T T' := (hSame_JT T').mpr (col_right f.J T')
        have ha_off_JT : ¬ Col f.J T a.1 := by
          intro haJT
          have hdisj : ∀ S, ¬ (Col f.O f.I S ∧ Col f.J T S) :=
            playfair_strict_of_off_reference_tarski hOI_JT f.noncol (col_left f.J T)
          exact hdisj a.1 ⟨a.2, haJT⟩
        have hT_eq_T' : T = T' :=
          line_intersection_unique_tarski ha_off_JT hOJ_aT.2.1
            (col_right f.J T) hT'_JT (col_right a.1 T) hT'_aT
        have hJb'_TO : Parallel f.J b'.1 T f.O := by
          simpa [axisZero, ← hT_eq_T'] using hJb'_T'O
        have hTO_Jb : Parallel T f.O f.J b.1 := parallel_symm hJb_TO
        have hTO_Jb' : Parallel T f.O f.J b'.1 := parallel_symm hJb'_TO
        have hSame_Jb : ∀ S : Point, Col f.J b.1 S ↔ Col f.J b'.1 S :=
          tarski_playfair T f.O f.J b.1 f.J b'.1 f.J hTO_Jb hTO_Jb'
            (col_left f.J b.1) (col_left f.J b'.1)
        have hb_Jb' : Col f.J b'.1 b.1 := (hSame_Jb b.1).mp (col_right f.J b.1)
        have hb'_off_OI : ¬ Col f.O f.I f.J := f.noncol
        have hb_eq_b' : b.1 = b'.1 :=
          line_intersection_unique_tarski hb'_off_OI (f.J_ne_axis_point b'.1 b'.2)
            b.2 b'.2 hb_Jb' (col_right f.J b'.1)
        simpa [hb_eq_b'] using hMid'
  · exact addGraph_of_midpoint_zero_tarski f a b

/-- D1: Trichotomy of the positive ray on the axis. -/
theorem positiveTrichotomy_tarski (f : Frame Point) : PositiveTrichotomy f := by
  intro a
  by_cases ha : a = axisZero f
  · exact Or.inl ha
  · have haO : a.1 ≠ f.O := fun h => ha (Subtype.ext h)
    have hIO : f.I ≠ f.O := f.O_ne_I.symm
    rcases a.2 with hOIa | hIaO | haOI
    · exact Or.inr (Or.inl ⟨hIO, haO, Or.inl hOIa⟩)
    · exact Or.inr (Or.inl ⟨hIO, haO, Or.inr (bet_symm hIaO)⟩)
    · obtain ⟨b, hb⟩ := addInverseLaw_tarski f a
      have hMid : MulMidpoint f.O a.1 b.1 :=
        (addGraph_zero_iff_midpoint_tarski f a b).mp hb
      have hbO : b.1 ≠ f.O := by
        intro h
        exact haO (cong_identity f.O a.1 f.O (by simpa [h] using hMid.2)).symm
      have hCmp : Bet a.1 f.I b.1 ∨ Bet a.1 b.1 f.I :=
        ray_bet_comparable_tarski haO haOI hMid.1
      have hBet : Bet f.O f.I b.1 ∨ Bet f.O b.1 f.I := by
        rcases hCmp with h | h
        · exact Or.inl (bet_exchange haOI h)
        · exact Or.inr (bet_exchange hMid.1 h)
      exact Or.inr (Or.inr ⟨b, ⟨hIO, hbO, hBet⟩, hb⟩)

/-- D3: No two positive axis points sum to zero. -/
theorem positiveProper_tarski (f : Frame Point) : PositiveProper f := by
  intro a b ha hb hab
  have hMid : MulMidpoint f.O a.1 b.1 :=
    (addGraph_zero_iff_midpoint_tarski f a b).mp hab
  have hOut_ab : Out f.O a.1 b.1 :=
    out_trans_tarski (out_swap_tarski ha) hb
  rcases hOut_ab.2.2 with hOab | hOba
  · exact ha.2.1 (bet_swap_endpoint_eq hOab hMid.1).symm
  · exact hb.2.1 (bet_swap_endpoint_eq hOba (bet_symm hMid.1)).symm

end AddInvAndOrderDraft

end TarskiField

/-!
## Full synthetic proof: algebraic negative equals the geometric opposite ray

This step of constructing the ordered scalar axis uses only the original
`Plane` axioms and the already established version-47 theorems. In
particular, addition is still the relational `AddGraph`; no field, ordered
group, real numbers, or coordinate arithmetic is assumed.

Define `AxisNegative f a` to mean that there exists an axis point `b` on the
strict positive ray `Out O I b` whose geometrically constructed sum with `a`
is `O`. We prove the exact equivalence

    AxisNegative f a  <->  a != O and Bet a O I.

**Forward direction.** Suppose `b` is positive and `AddGraph f a b O`.
By `addGraph_zero_iff_midpoint_tarski`, `O` is the midpoint of `ab`. Thus
`Bet a O b` and `Cong O a O b`. If `a=O`, the latter becomes
`Cong O O O b`, so congruence symmetry and identity force `b=O`,
contradicting positivity. Thus `a!=O`. Since `b` is positive, by the
definition of `Out` we have `b!=O` and either `Bet O I b` or `Bet O b I`.
In the first case, the *inner betweenness transitivity* theorem applied to
`Bet a O b` and `Bet O I b` yields `Bet a O I`. In the second case, since
`O!=b`, outer betweenness transitivity applied to `Bet a O b` and
`Bet O b I` gives `Bet a b I`; the extension rule applied to this and
`Bet a O b` then gives `Bet a O I`. Both positive-ray cases are exhausted.

**Reverse direction.** Suppose `a!=O` and `Bet a O I`. The version-47
additive-inverse theorem constructs an axis point `b` satisfying
`AddGraph f a b O`. The midpoint equivalence yields `Bet a O b` and
`Cong O a O b`. If `b=O`, congruence identity applied to
`Cong O a O O` forces `a=O`, contradiction. Thus `b!=O`.
Now the *ray betweenness comparability* theorem applies to the distinct
starting points `a,O` and the two segments `Bet a O I`, `Bet a O b`;
its alternatives are `Bet a I b` and `Bet a b I`. In the first alternative,
the exchange law applied to `Bet a O I` and `Bet a I b` gives `Bet O I b`.
In the second, the exchange law applied to `Bet a O b` and `Bet a b I`
gives `Bet O b I`. Both establish the ray comparison required for
`Out O I b`, because `I!=O` is a frame property and `b!=O` was proved.
The constructed `b` therefore witnesses `AxisNegative f a`.

The sign partition follows directly: `positiveTrichotomy_tarski` supplies
zero, positive, or a positive additive-inverse witness. Its three cases
cannot overlap: a positive point is nonzero by `Out`; a negative point is
nonzero by the equivalence above; and a positive point cannot be negative
because its positive inverse witness would contradict
`positiveProper_tarski`. These are logical consequences of the proved
geometric assertions, without new order axioms.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Algebraic negativity, expressed relationally before field construction. -/
def AxisNegative (f : Frame Point) (a : AxisPoint f) : Prop :=
  ∃ b : AxisPoint f, Positive f b ∧ AddGraph f a b (axisZero f)

/-- Algebraic negativity coincides exactly with the opposite open half-ray
    in the original Tarski plane. -/
theorem axisNegative_iff_opposite_ray_tarski
    (f : Frame Point) (a : AxisPoint f) :
    AxisNegative f a ↔ a.1 ≠ f.O ∧ Bet a.1 f.O f.I := by
  constructor
  · rintro ⟨b, hb, hab⟩
    have hMid : MulMidpoint f.O a.1 b.1 :=
      (addGraph_zero_iff_midpoint_tarski f a b).mp hab
    have haO : a.1 ≠ f.O := by
      intro ha
      have hOb : f.O = b.1 :=
        cong_identity f.O b.1 f.O (by
          simpa [ha] using (cong_symm hMid.2))
      exact hb.2.1 hOb.symm
    refine ⟨haO, ?_⟩
    rcases hb.2.2 with hOIb | hObI
    · exact bet_inner_trans hMid.1 hOIb
    · have habI : Bet a.1 b.1 f.I :=
        bet_outer_trans hMid.1 hObI hb.2.1.symm
      exact bet_extend hMid.1 habI
  · rintro ⟨haO, haOI⟩
    obtain ⟨b, hab⟩ := addInverseLaw_tarski f a
    have hMid : MulMidpoint f.O a.1 b.1 :=
      (addGraph_zero_iff_midpoint_tarski f a b).mp hab
    have hbO : b.1 ≠ f.O := by
      intro hb
      have hOa : f.O = a.1 :=
        cong_identity f.O a.1 f.O (by
          simpa [hb] using hMid.2)
      exact haO hOa.symm
    have hComparable :
        Bet a.1 f.I b.1 ∨ Bet a.1 b.1 f.I :=
      ray_bet_comparable_tarski haO haOI hMid.1
    have hRay : Bet f.O f.I b.1 ∨ Bet f.O b.1 f.I := by
      rcases hComparable with h | h
      · exact Or.inl (bet_exchange haOI h)
      · exact Or.inr (bet_exchange hMid.1 h)
    exact ⟨b, ⟨f.O_ne_I.symm, hbO, hRay⟩, hab⟩

theorem axisSignTrichotomy_tarski
    (f : Frame Point) (a : AxisPoint f) :
    a = axisZero f ∨ Positive f a ∨ AxisNegative f a := by
  simpa [AxisNegative] using (positiveTrichotomy_tarski f a)

theorem axisNegative_ne_zero_tarski
    (f : Frame Point) (a : AxisPoint f)
    (h : AxisNegative f a) : a ≠ axisZero f := by
  have haO : a.1 ≠ f.O :=
    ((axisNegative_iff_opposite_ray_tarski f a).mp h).1
  intro ha
  exact haO (congrArg Subtype.val ha)

theorem positive_not_axisNegative_tarski
    (f : Frame Point) (a : AxisPoint f)
    (ha : Positive f a) : ¬ AxisNegative f a := by
  rintro ⟨b, hb, hab⟩
  exact positiveProper_tarski f a b ha hb hab

end TarskiField

/-!
## Complete synthetic proofs of the next dependency reductions

The proofs below concern geometry and the internal axis only. They continue
the natural-language-first development; none assumes an existing field.

### A. A parallel quadrilateral has a common diagonal midpoint

Assume `U,V,W` are not collinear, `UV` is parallel to `WZ`, and `VW` is
parallel to `ZU`. First construct the midpoint `M` of `UW` using the
Tarski midpoint-existence theorem. Next construct the reflection `Vr` of
`V` in `M`, giving `Bet V M Vr` and `Cong M V M Vr`. Apply the already proved
midpoint-diagonals parallelogram theorem to triangle `V,U,W` with common
midpoint `M` of `UW` and `V Vr`. Its conclusions, after reversal of parallel
line endpoint order, are `Parallel U V W Vr` and `Parallel V W U Vr`.

Both `WZ` and `WVr` pass through `W` and are parallel to `UV`. Playfair's
uniqueness therefore identifies their complete sets of collinear points;
in particular `Vr` lies on `WZ`. Similarly `UZ` and `UVr` pass through `U`
and are parallel to `VW`, so `Vr` lies on `UZ`.

The lines `WZ` and `UZ` have different directions. Indeed, if `U` lay on
`WZ`, then `UV` and `WZ`, being parallel and sharing `U`, would coincide.
This would put `W` on `UV`, contradicting the initial noncollinearity.
Consequently the two distinct lines `WZ` and `UZ` intersect in exactly one
point, by the already proved two-line intersection uniqueness theorem.
Both `Vr` and `Z` belong to both lines, so `Vr=Z`. The reflection relation
then says `M` is the midpoint of `VZ`, as well as of `UW`. This handles
every configuration under the stated strict noncollinearity hypothesis;
the flat case is a separate later obligation.

As an immediate consequence, the two pairs of opposite sides are congruent.
The first midpoint relation says that reflection through `M` exchanges
`U` and `W`; reversing that relation gives the midpoint statement in the
orientation required by the already proved central-reflection congruence
theorem. Similarly the second midpoint relation says reflection through
`M` exchanges `V` and `Z`. Apply reflection preservation of segment
congruence to the segment with endpoints `U,V`: its reflected endpoints
are `W,Z`, so `Cong U V W Z`. Apply the same theorem with `V,W` as the
first segment and `Z,U` as the reflected endpoints, obtaining
`Cong V W Z U`. Both claims use only Tarski congruence and betweenness;
the nonflat hypothesis enters through existence of the common midpoint.

### B. A13 cut points belong to the geometric scalar axis

Take any frame, axis points `X,Y`, and a point `B` between them. The already
proved `colSegmentClosed_from_tarski` applies to `O=f.O`, `I=f.I` and
these three points. It yields `Col O I B`; hence `AxisSegmentClosed f`
holds without an additional premise. This proof includes `O=I` in the
general lemma (by endpoint betweenness) and `O!=I` by the previously
proved collinear-segment closure; in a frame we also have `O!=I`.

For a polynomial lower cut with endpoints `L` and `R` on the axis,
`polynomial_cut_A13_internal_scalar` already applies Tarski A13 to give a
unique cut point `B` satisfying `Bet L B R`, its upper-bound formula and
least-upper-bound property. Its sole remaining geometric hypothesis is
`AxisSegmentClosed f`, proved in the preceding paragraph. Supply that
theorem. Since `B` is between two axis points, it is itself on the axis;
the existing proof packages it as `b : AxisPoint f`. If a second axis point
had the three properties, their underlying plane points would coincide by
A13-cut uniqueness, and subtype extensionality identifies the axis points.
The result still uses the first-order A13 scheme, not completeness of an
external field or an arbitrary-subset least-upper-bound axiom.

### C. Exact multiplication-law dependencies

Take parallel nondegenerate lines `AB ∥ CD` and `CD ∥ EF`. If `AB` and
`EF` meet at `P`, symmetry makes `CD` parallel to both lines; the proved
Tarski-to-Playfair theorem, applied at their common point `P`, forces
`AB` and `EF` to have the same collinear points, so they are parallel.
If the lines never meet, the disjoint-line branch of the definition gives
their parallelism directly. This is the existing geometric proof of
`parallel_trans_of_playfair`, with its Playfair premise now supplied by
the unconditional `tarski_playfair`.

For multiplication commutativity, take `MulGraph f x y z`. The zero input
cases use the proven right-zero law, the zero-left construction, and graph
uniqueness. In the nonzero case, both inputs and the product are nonzero.
The two first projection lines of the products `x*y` and `y*x` are parallel
to `IJ`; the original final projection gives `(J,x) ∥ (wy,z)`.
Applying the affine Pappus-parallel statement to these projection points
yields `(J,y) ∥ (wx,z)`, precisely the reversed final projection. Hence
`MulGraph f y x z`. Every incidence, parallel-transitivity and graph
totality premise in this argument is already a Tarski theorem, so the only
remaining hypothesis is the exact affine Pappus statement. The full
zero/nonzero geometric case analysis is embodied in the previously checked
`mulCommLaw_of_pappus` and its supporting lemmas.

For multiplication associativity, start from four multiplication graphs
for `(a*b)*c` and `a*(b*c)`. If any input is zero, the zero-factor laws
and unique product graph give the two outputs equal. When all inputs are
nonzero, the already proved nonzero-product theorem keeps intermediate
products nonzero. The three first-projection points on `OJ`, and the
four corresponding last-projection lines, satisfy the four-pair Desargues
configuration: the first pairs are parallel by common direction `IJ`,
and the later pairs by the given product graphs. The geometric four-pair
Desargues conclusion supplies the missing final projection for
`MulGraph f (ab) c rhs`. Functional multiplication equates this with
the preexisting `lhs`. The full construction is already encoded in the
checked conditional `mulAssocLaw_of_desargues`; the only unresolved premise
after discharging the Tarski incidence and parallel facts is
`AffineDesarguesFourPairs`. Neither Pappus nor Desargues is asserted true
in the following conditional statements.

### D. Existence of the first four GeoCoq addition projections

Fix a scalar point `x` on `OI`. The lines `IJ` and `OJ` intersect at
`J` but are not identical, for otherwise the frame points would be
collinear. They are therefore not parallel. The proved Tarski theorem
constructs a line `xW` parallel to `IJ`. This line cannot be parallel
to `OJ`: transitivity of parallelism would make `IJ` and `OJ` parallel.
Hence `xW` intersects `OJ` at a point `A'`. If `x=A'`, the equality
branch of the weak projection `GeoCoqPj IJ x A'` holds. Otherwise `xW`
can be renamed `xA'` using line extensionality, and the strong branch
`Parallel IJ xA'` holds. If `x` is nonzero the equality branch is
impossible, because the only common point of `OI` and `OJ` is `O`.

Let `A'` be a nonzero point on `OJ`, and let `y` be a nonzero scalar
point on `OI`. By two-point line extensionality, `OA'` is the complete
line `OJ`, and `Oy` is the complete line `OI`. These points are not
collinear: collinearity would put `y` on both axes, forcing `y=O`.
Construct the midpoint `M` of `A'y` and reflect `O` across `M` to
obtain `C'`. Since the two diagonals `A'y` and `OC'` share their
midpoint and `O,A',y` are noncollinear, the already proved synthetic
midpoint-to-parallelogram theorem yields `OA' ∥ C'y` and
`A'C' ∥ yO`. Reverse the appropriate line orientations and use the
line identities `OA'=OJ`, `Oy=OI`: then `OJ ∥ yC'` and `OI ∥ A'C'`.
These are exactly the second and third strict GeoCoq projections.

For `x,y` both nonzero, the first construction gives `A'` on `OJ`
with `GeoCoqPj IJ x A'`. The previously proved no-origin lemma makes
`A'` nonzero. The second construction then gives `C'`, establishing
the first four conjuncts of `GeoCoqSum`. The fifth conjunct,
`GeoCoqPj JI C' z`, is a separate parallelogram-composition obligation
and is not asserted by this existence result.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Nonflat parallel quadrilateral: the two diagonals have one midpoint. -/
theorem parallelogram_diagonal_midpoint_exists_tarski
    {U V W Z : Point}
    (htri : ¬ Col U V W)
    (hUV : Parallel U V W Z)
    (hVW : Parallel V W Z U) :
    ∃ M : Point, MulMidpoint M U W ∧ MulMidpoint M V Z := by
  obtain ⟨M, hMW⟩ := midpoint_existence_tarski U W
  obtain ⟨Vr, hMVr, _⟩ := mul_reflection_exists_unique M V
  have htri' : ¬ Col V U W := fun h => htri (col_swap h)
  obtain ⟨hp1, hp2⟩ :=
    midpoint_diagonals_parallelogram_tarski
      (B := M) (P := V) (R := U) (Q := W) (S := Vr)
      htri' hMW hMVr
  have hpUV : Parallel U V W Vr := parallel_reverse_both hp1
  have hsameW : ∀ S, Col W Z S ↔ Col W Vr S :=
    tarski_playfair U V W Z W Vr W
      hUV hpUV (col_left W Z) (col_left W Vr)
  have hpVW : Parallel V W U Vr :=
    parallel_reverse_left (parallel_symm hp2)
  have hpVW1 : Parallel V W U Z := parallel_reverse_right hVW
  have hsameU : ∀ S, Col U Z S ↔ Col U Vr S :=
    tarski_playfair V W U Z U Vr U
      hpVW1 hpVW (col_left U Z) (col_left U Vr)
  have hNoncolWZU : ¬ Col W Z U := by
    intro hWZU
    have hsame : ∀ S, Col U V S ↔ Col W Z S :=
      parallel_same_of_intersection hUV (col_left U V) hWZU
    exact htri ((hsame W).mpr (col_left W Z))
  have hVrWZ : Col W Z Vr := (hsameW Vr).mpr (col_right W Vr)
  have hVrUZ : Col U Z Vr := (hsameU Vr).mpr (col_right U Vr)
  have hEq : Vr = Z :=
    line_intersection_unique_tarski
      (A := W) (B := Z) (C := U) (D := Z)
      (P := Vr) (Q := Z)
      hNoncolWZU hVW.2.1.symm hVrWZ (col_right W Z)
      hVrUZ (col_right U Z)
  exact ⟨M, hMW, by simpa [hEq] using hMVr⟩

/-- In a nonflat parallel quadrilateral, opposite sides are congruent. -/
theorem strict_parallelogram_opposite_cong_tarski
    {U V W Z : Point}
    (htri : ¬ Col U V W)
    (hUV : Parallel U V W Z)
    (hVW : Parallel V W Z U) :
    Cong U V W Z ∧ Cong V W Z U := by
  obtain ⟨M, hUW, hVZ⟩ :=
    parallelogram_diagonal_midpoint_exists_tarski htri hUV hVW
  exact ⟨
    mul_reflection_preserves_cong
      (mul_midpoint_reverse hUW) (mul_midpoint_reverse hVZ),
    mul_reflection_preserves_cong
      (mul_midpoint_reverse hVZ) hUW⟩

/-- Plane-only proof that every segment between axis points stays on it. -/
theorem axisSegmentClosed_tarski (f : Frame Point) : AxisSegmentClosed f := by
  intro X B Y hX hY hBet
  exact (colSegmentClosed_from_tarski (Point := Point))
    f.O f.I X B Y hX hY hBet

/-- The unique A13 polynomial-cut point is an internal axis point; the
    former segment-closure assumption is now a Tarski theorem. -/
theorem polynomial_cut_A13_internal_scalar_tarski
    [ContinuousPlane Point]
    (f : Frame Point) {n : Nat}
    (o i j l r : Fin n)
    (coefficients : List (Fin n)) (params : Fin n → Point)
    (hlAxis : Col f.O f.I (params l))
    (hrAxis : Col f.O f.I (params r))
    (hL : (polynomialLowerCutFormula o i j l r coefficients).eval
      (Fin.cons (params l) params)) :
    ∃! b : AxisPoint f,
      Bet (params l) b.1 (params r) ∧
      (upperBoundsFormula l
        (polynomialLowerCutFormula o i j l r coefficients)).eval
          (Fin.cons b.1 params) ∧
      ∀ Y : Point,
        (upperBoundsFormula l
          (polynomialLowerCutFormula o i j l r coefficients)).eval
            (Fin.cons Y params) →
        Bet (params l) b.1 Y := by
  exact polynomial_cut_A13_internal_scalar f
    o i j l r coefficients params hlAxis hrAxis
    (axisSegmentClosed_tarski f) hL

/-- All Tarski-plane parallel relations are transitive. -/
theorem parallelTransitivityGoal_tarski :
    ParallelTransitivityGoal (Point := Point) := by
  intro A B C D E F hABCD hCDEF
  exact parallel_trans_of_playfair
    (fun A B C D E F P h₁ h₂ hP₁ hP₂ =>
      tarski_playfair A B C D E F P h₁ h₂ hP₁ hP₂)
    hABCD hCDEF

/-- Unconditional synthetic incidence reduces commutativity to Pappus. -/
theorem mulCommLaw_of_pappus_tarski
    (f : Frame Point)
    (hPappus : AffinePappusParallel (Point := Point)) :
    MulCommLaw f := by
  exact mulCommLaw_of_pappus f
    (operation_graphs_total_tarski f).2
    colTransitivityGoal_tarski
    parallelTransitivityGoal_tarski
    hPappus

/-- Unconditional synthetic incidence reduces associativity to Desargues. -/
theorem mulAssocLaw_of_desargues_tarski
    (f : Frame Point)
    (hDesargues : AffineDesarguesFourPairs (Point := Point)) :
    MulAssocLaw f := by
  exact mulAssocLaw_of_desargues f
    (operation_graphs_total_tarski f).2
    colTransitivityGoal_tarski
    parallelTransitivityGoal_tarski
    hDesargues

/-- The first weak GeoCoq addition projection is geometrically total. -/
theorem geoCoqSum_first_projection_exists_tarski
    (f : Frame Point) (x : AxisPoint f) :
    ∃ A' : Point,
      GeoCoqPj f.I f.J x.1 A' ∧ Col f.O f.J A' := by
  have hThrough : ∀ A B P : Point, A ≠ B →
      ∃ W : Point, Parallel A B P W := by
    intro A B P hAB
    exact parallel_through_any_point_tarski hAB
  have hTrans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F := by
    intro A B C D E F h1 h2
    exact parallel_trans_of_playfair tarski_playfair h1 h2
  obtain ⟨A', hAxis, W, hParXW, hCol⟩ :=
    weak_directional_projection_exists hThrough hTrans
      f.O f.J f.I f.J x.1
      f.O_ne_J f.I_ne_J (frame_IJ_not_parallel_OJ f)
  by_cases hEq : x.1 = A'
  · exact ⟨A', Or.inr hEq, hAxis⟩
  · have hLine : ∀ S, Col x.1 W S ↔ Col x.1 A' S :=
      col_line_extensionality_tarski
        hParXW.2.1 hEq (col_left x.1 W) hCol
    exact ⟨A', Or.inl
      (parallel_retarget_right_of_line_eq hParXW hEq hLine), hAxis⟩

/-- If the scalar is nonzero, its first projection is nondegenerate. -/
theorem geoCoqSum_first_projection_strong_tarski
    (f : Frame Point) (x : AxisPoint f) (hx : x.1 ≠ f.O) :
    ∃ A' : Point,
      Parallel f.I f.J x.1 A' ∧ Col f.O f.J A' := by
  obtain ⟨A', hProj, hAxis⟩ :=
    geoCoqSum_first_projection_exists_tarski f x
  have hne : x.1 ≠ A' := by
    intro heq
    have hXOJ : Col f.O f.J x.1 := by simpa [heq] using hAxis
    exact hx (frame_axes_intersection_only_origin_tarski f x.1 x.2 hXOJ)
  rcases hProj with hPar | hEq
  · exact ⟨A', hPar, hAxis⟩
  · exact False.elim (hne hEq)

/-- A nonzero axis projection and scalar construct both middle projections. -/
theorem geoCoqSum_middle_projections_exists_tarski
    (f : Frame Point) (A' : Point)
    (hAxis : Col f.O f.J A') (hAneO : A' ≠ f.O)
    (y : AxisPoint f) (hy : y.1 ≠ f.O) :
    ∃ C' : Point,
      Parallel f.O f.I A' C' ∧ Parallel f.O f.J y.1 C' := by
  have hLineOJ : ∀ S, Col f.O f.J S ↔ Col f.O A' S :=
    col_line_extensionality_tarski f.O_ne_J hAneO.symm
      (col_left f.O f.J) hAxis
  have hLineOI : ∀ S, Col f.O f.I S ↔ Col f.O y.1 S :=
    col_line_extensionality_tarski f.O_ne_I hy.symm
      (col_left f.O f.I) y.2
  have hNoncol : ¬ Col f.O A' y.1 := by
    intro h
    have hYOJ : Col f.O f.J y.1 := (hLineOJ y.1).mpr h
    exact hy (frame_axes_intersection_only_origin_tarski f y.1 y.2 hYOJ)
  obtain ⟨M, hMidAy⟩ := midpoint_existence_tarski A' y.1
  obtain ⟨C', hMidOC, _⟩ := mul_reflection_exists_unique M f.O
  obtain ⟨hVertRaw, hHorzRaw⟩ :=
    midpoint_diagonals_parallelogram_tarski
      (B := M) (P := f.O) (R := A') (Q := y.1) (S := C')
      hNoncol hMidAy hMidOC
  have hY_OA : Parallel y.1 C' f.O A' :=
    parallel_reverse_left (parallel_symm hVertRaw)
  have hY_OJ : Parallel y.1 C' f.O f.J :=
    parallel_retarget_right_of_line_eq hY_OA f.O_ne_J
      (fun S => (hLineOJ S).symm)
  have hA_Oy : Parallel A' C' f.O y.1 :=
    parallel_reverse_right hHorzRaw
  have hA_OI : Parallel A' C' f.O f.I :=
    parallel_retarget_right_of_line_eq hA_Oy f.O_ne_I
      (fun S => (hLineOI S).symm)
  exact ⟨C', parallel_symm hA_OI, parallel_symm hY_OJ⟩

/-- The nonzero GeoCoq sum diagram has its first four geometric witnesses. -/
theorem geoCoqSum_prefix_nonzero_tarski
    (f : Frame Point) (x y : AxisPoint f)
    (hx : x.1 ≠ f.O) (hy : y.1 ≠ f.O) :
    ∃ A' C' : Point,
      GeoCoqPj f.I f.J x.1 A' ∧ Col f.O f.J A' ∧
      GeoCoqPj f.O f.I A' C' ∧
      GeoCoqPj f.O f.J y.1 C' := by
  obtain ⟨A', hFirst, hAxis⟩ :=
    geoCoqSum_first_projection_exists_tarski f x
  have hAne : A' ≠ f.O :=
    geoCoq_firstPj_not_origin f x A' hx hFirst
  obtain ⟨C', hH, hV⟩ :=
    geoCoqSum_middle_projections_exists_tarski f A'
      hAxis hAne y hy
  exact ⟨A', C', hFirst, hAxis, Or.inl hH, Or.inl hV⟩

/-!
### 幾何学的加法の射影一意性と単位点での両定義の一致：自然言語証明

**第1射影の一意性。** `x` は軸 `OI` 上の非原点点とする。`x` が
直線 `OJ` 上にも存在すれば、既証明の二軸交点一意性によって `x=O`
となり仮定に反する。したがって `x` は投影先の直線 `OJ` の外にある。
いま `A,B` はともに `OJ` 上にあり、`xA` と `xB` はいずれも
`IJ` に平行とする。二つの平行線は `x` を共有するので、Playfair
一意性により `xA` と `xB` は同一直線である。もし `A≠B` なら
`OJ` と `xA` が二点 `A,B` を共有して同一直線となり、`x∈OJ`
を含意して矛盾する。したがって `A=B`。これは既証明の
`directional_projection_unique_of_playfair` を投影先 `OJ`、
方向 `IJ`、元の点 `x` に適用したものと正確に一致する。

**第2・第3射影の共通補助点の一意性。** `A'∉OI` とし、
`OI∥A'C`, `OI∥A'D`, `OJ∥yC`, `OJ∥yD` を仮定する。
前二者の平行線 `A'C`,`A'D` は点 `A'` を共有するため、
Playfair一意性で両直線の共線点は一致する。特に `D∈A'C`。
`A'∉OI` なので `OI∥A'C` は厳密な平行であり、両直線の
共通点は存在しない。軸点 `y∈OI` は `A'C` 上にはない。
`C,D` は同じ投影先直線 `A'C` 上にあり、`yC`,`yD` は
ともに `OJ` に平行である。先に証明した斜投影の一意性定理を
投影先 `A'C`、方向 `OJ`、元の点 `y` として適用し、`C=D`。

**`I+I` における二つの加法図式の同値性。** まずGeoCoqの
第1射影 `GeoCoqPj IJ I A` と `A∈OJ` から `A=J` を導く。
弱射影の縮退枝 `I=A` なら `I∈OJ` となり、非共線な枠に
反する。強枝では `IJ∥IA` が成立し、両直線は `I` を共有する。
よって両直線の共線点は一致し、`A∈IJ`。直線 `IJ` と `OJ` は
共通点 `J` を持ち、点 `O` は `IJ` 上にない。二直線の交点一意性
より、双方に属する `A` は `J` と等しい。

`AddGraph f I I z` からGeoCoq図式を構成する向きでは、
`I≠O` により `AddGraph` の零枝は不可能であり、強枝から点
`T` と三本の平行線 `OJ∥IT`, `OI∥JT`, `JI∥Tz` を得る。
GeoCoqの補助点を `A=J`, `C=T` と選ぶ。第1射影は
`IJ∥IJ` の反射律、第2〜第4射影は上記三本の平行線で満たされる。

逆向きではGeoCoq図式の補助点 `A,C` を取り、先の証明によって
`A=J` と置き換える。第3弱射影 `GeoCoqPj OJ I C` の縮退枝
`I=C` と第2弱射影 `GeoCoqPj OI J C` の縮退枝 `J=C` を
同時に吟味する。`J=C` と仮定すると、第3弱射影の強枝は
`OJ∥IJ` を意味するが、この二直線は枠の非共線性から平行では
ない。第3弱射影の縮退枝なら `I=J` となり、やはり矛盾する。
ゆえに `C≠J` であり、第2弱射影は強枝 `OI∥JC` に限られる。
`J` は `OI` の外にあるので、この平行関係は両直線が交わらない
ことを含意する。したがって `C∉OI`。とくに `I≠C` なので
第3弱射影も強枝 `OJ∥IC` であり、`z∈OI` から `C≠z`
となるので最終弱射影も強枝 `JI∥Cz` になる。この三本を
`AddGraph` の補助点 `T=C` に用い、`I≠O` の強枝を得る。
以上で両方向を示した。ここで証明したのは特定の非零入力
`x=y=I` であり、一般の `x,y` への拡張には平行四辺形の合成が残る。
-/

/-- 非原点の軸点をIJ方向にOJへ投影した点は一意である。 -/
theorem geoCoqSum_first_projection_unique_tarski
    (f : Frame Point) (x : AxisPoint f)
    (hx : x.1 ≠ f.O) (A B : Point)
    (hA : Col f.O f.J A) (hB : Col f.O f.J B)
    (hPA : Parallel f.I f.J x.1 A)
    (hPB : Parallel f.I f.J x.1 B) : A = B := by
  have hXoff : ¬ Col f.O f.J x.1 :=
    fun h => hx
      (frame_axes_intersection_only_origin_tarski f x.1 x.2 h)
  have hLineExt : ∀ A B C D : Point,
      A ≠ B → C ≠ D → Col A B C → Col A B D →
      ∀ S, Col A B S ↔ Col C D S := by
    intro A B C D hAB hCD hC hD
    exact col_line_extensionality_tarski hAB hCD hC hD
  exact directional_projection_unique_of_playfair
    tarski_playfair hLineExt f.O f.J f.I f.J x.1 A B
    f.O_ne_J hXoff hA hB hPA hPB

/-- 2本の非退化な中間射影条件を満たす補助点は一意である。 -/
theorem geoCoqSum_middle_projections_unique_tarski
    (f : Frame Point) (A' : Point) (y : AxisPoint f)
    (hOff : ¬ Col f.O f.I A') (C D : Point)
    (hHC : Parallel f.O f.I A' C)
    (hHD : Parallel f.O f.I A' D)
    (hVC : Parallel f.O f.J y.1 C)
    (hVD : Parallel f.O f.J y.1 D) : C = D := by
  have hSame : ∀ S, Col A' C S ↔ Col A' D S :=
    tarski_playfair f.O f.I A' C A' D A'
      hHC hHD (col_left A' C) (col_left A' D)
  have hDLine : Col A' C D := (hSame D).mpr (col_right A' D)
  have hDisjoint : ∀ S,
      ¬ (Col f.O f.I S ∧ Col A' C S) :=
    playfair_strict_of_off_reference_tarski
      hHC hOff (col_left A' C)
  have hYoff : ¬ Col A' C y.1 :=
    fun h => hDisjoint y.1 ⟨y.2, h⟩
  have hLineExt : ∀ A B C D : Point,
      A ≠ B → C ≠ D → Col A B C → Col A B D →
      ∀ S, Col A B S ↔ Col C D S := by
    intro A B C D hAB hCD hC hD
    exact col_line_extensionality_tarski hAB hCD hC hD
  exact directional_projection_unique_of_playfair
    tarski_playfair hLineExt A' C f.O f.J y.1 C D
    hHC.2.1 hYoff (col_right A' C) hDLine hVC hVD

/-- 単位軸点を二つ加える場合、両加法作図は正確に同値である。 -/
theorem geoCoqSum_one_first_projection_tarski
    (f : Frame Point) (A : Point)
    (hPj : GeoCoqPj f.I f.J f.I A)
    (hAxis : Col f.O f.J A) : A = f.J := by
  have hIoff : ¬ Col f.O f.J f.I :=
    fun h => f.noncol (col_swap_last h)
  have hIA : f.I ≠ A := by
    intro heq
    exact hIoff (by simpa [heq] using hAxis)
  have hPar : Parallel f.I f.J f.I A := by
    rcases hPj with hPar | hEq
    · exact hPar
    · exact False.elim (hIA hEq)
  have hSame : ∀ S, Col f.I f.J S ↔ Col f.I A S :=
    parallel_same_of_intersection hPar
      (col_left f.I f.J) (col_left f.I A)
  have hA_IJ : Col f.I f.J A :=
    (hSame A).mpr (col_right f.I A)
  have hIJO : ¬ Col f.I f.J f.O :=
    fun h => f.noncol (col_rotate (col_rotate h))
  exact line_intersection_unique_tarski
    (A := f.I) (B := f.J) (C := f.O) (D := f.J)
    (P := A) (Q := f.J)
    hIJO f.O_ne_J hA_IJ (col_right f.I f.J)
    hAxis (col_right f.O f.J)

/-- `AddGraph I I z` とGeoCoq式の和作図の厳密な同値性。 -/
theorem addGraph_one_one_iff_geoCoqSum_tarski
    (f : Frame Point) (z : AxisPoint f) :
    AddGraph f (axisOne f) (axisOne f) z ↔
    GeoCoqSum f (axisOne f) (axisOne f) z := by
  constructor
  · intro hAdd
    rcases hAdd with ⟨hZero, _⟩ | ⟨_, T, hV, hH, hD⟩
    · exact False.elim (f.O_ne_I hZero.symm)
    · exact ⟨f.J, T,
        Or.inl (parallel_refl f.I_ne_J),
        col_right f.O f.J, Or.inl hH,
        Or.inl hV, Or.inl hD⟩
  · rintro ⟨A, C, hFirst, hAxis, hSecond, hThird, hLast⟩
    have hA : A = f.J :=
      geoCoqSum_one_first_projection_tarski f A hFirst hAxis
    subst A
    have hCneJ : C ≠ f.J := by
      intro heq
      rcases hThird with hPar | hEq
      · have hOJ_IJ : Parallel f.O f.J f.I f.J := by
          simpa [axisOne, heq] using hPar
        exact frame_IJ_not_parallel_OJ f (parallel_symm hOJ_IJ)
      · exact f.I_ne_J (by simpa [axisOne, heq] using hEq)
    have hH : Parallel f.O f.I f.J C := by
      rcases hSecond with hPar | hEq
      · exact hPar
      · exact False.elim (hCneJ hEq.symm)
    have hCoffOI : ¬ Col f.O f.I C := by
      intro hc
      have hDisj : ∀ S,
          ¬ (Col f.O f.I S ∧ Col f.J C S) :=
        playfair_strict_of_off_reference_tarski
          hH f.noncol (col_left f.J C)
      exact hDisj C ⟨hc, col_right f.J C⟩
    have hIneC : f.I ≠ C := by
      intro heq
      apply hCoffOI
      rw [← heq]
      exact col_right f.O f.I
    have hV : Parallel f.O f.J f.I C := by
      rcases hThird with hPar | hEq
      · exact hPar
      · exact False.elim (hIneC hEq)
    have hCneZ : C ≠ z.1 := by
      intro heq
      have hCaxis : Col f.O f.I C := by simpa [heq] using z.2
      exact hCoffOI hCaxis
    have hD : Parallel f.J f.I C z.1 := by
      rcases hLast with hPar | hEq
      · exact hPar
      · exact False.elim (hCneZ hEq)
    exact Or.inr ⟨f.O_ne_I.symm, C, hV, hH, hD⟩

/-!
### GeoCoq Ch13_1 `perp2_sym`：自然言語による完全証明

`TarskiPerp2 A B C D P` を、点 `X,Y` が存在して
`Col P X Y`、`TarskiPerp X Y A B`、
`TarskiPerp X Y C D` の三条件を満たすことと定義する。
これはGeoCoqの二本の直線の共通垂線を表す `Perp2` を、
既定義のTarski垂直関係により表現した定義であり、新たな公理ではない。
対称性の証明では、仮定の存在量化から点 `X,Y` を取り出す。
結論 `TarskiPerp2 C D A B P` の存在証人にも同じ点 `X,Y`
を選ぶ。最初の共線条件 `Col P X Y` はそのまま成立する。
結論の第2条件 `TarskiPerp X Y C D` は仮定の第3条件で、
結論の第3条件 `TarskiPerp X Y A B` は仮定の第2条件である。
ゆえに存在証人の三条件すべてが成立し、対称性が従う。
この補題はGeoCoqのPappus証明 `l13_10_aux4`、`l13_10_aux5`
で参照される定理の一つである。
-/

/-- GeoCoq Ch13_1, two lines with a common perpendicular through P. -/
def TarskiPerp2 (A B C D P : Point) : Prop :=
  ∃ X Y : Point,
    Col P X Y ∧ TarskiPerp X Y A B ∧ TarskiPerp X Y C D

/-- GeoCoq `perp2_sym`, obtained by exchanging its two hypotheses. -/
theorem tarski_perp2_sym_tarski {A B C D P : Point}
    (h : TarskiPerp2 A B C D P) :
    TarskiPerp2 C D A B P := by
  obtain ⟨X, Y, hPXY, hAB, hCD⟩ := h
  exact ⟨X, Y, hPXY, hCD, hAB⟩

/-!
**平行線の再指定の自然言語完全証明。** 直線 `AB` と
`CD` が平行で、別の非退化直線 `EF` が `CD` と
同じ共線点集合を持つとする。平行の定義の選言を調べる。
第1の場合、`AB` と `CD` の共線点集合が一致する。
それを `CD` と `EF` の同値関係に合成して、`AB`
と `EF` の共線点集合も一致する。従って一致線として
`AB∥EF`。第2の場合、`AB` と `CD` は共通点を
持たない。仮に `AB` と `EF` に共通点 `S` があれば、
`S∈EF` を同値関係で `S∈CD` に移せるので、
`AB` と `CD` の非交差性に矛盾する。従って
`AB` と `EF` は非交差で平行。第1の線分 `AB` の
非退化性はもとの平行関係から、第2の `EF` の
非退化性は仮定から得られるので、どちらの場合も
平行の定義の全条件が成立する。三つの直線の定義点が
一致するという仮定は使用していない。
-/

/-- Retarget a parallel line by full collinearity equivalence, without
    requiring the two descriptions to share an endpoint. -/
theorem parallel_retarget_right_of_line_extensionality_tarski
    {A B C D E F : Point}
    (hPar : Parallel A B C D)
    (hEF : E ≠ F)
    (hLine : ∀ S, Col C D S ↔ Col E F S) :
    Parallel A B E F := by
  rcases hPar with ⟨hAB, _, hSame | hDisjoint⟩
  · exact ⟨hAB, hEF,
      Or.inl (fun S => (hSame S).trans (hLine S))⟩
  · refine ⟨hAB, hEF, Or.inr ?_⟩
    intro S h
    exact hDisjoint S ⟨h.1, (hLine S).mpr h.2⟩

/-!
### GeoCoq加法図式の左右零元：自然言語による完全証明

**左零元・存在。** 任意の軸点 `y` に対し、第1補助点を `A'=O`、
第2補助点を `C'=y` と選ぶ。第1射影 `GeoCoqPj IJ O O` は
始点と終点が等しいため縮退枝で成立する。`A'∈OJ` は
端点の共線性から成立する。第3射影 `GeoCoqPj OJ y y` と
最終射影 `GeoCoqPj JI y y` も同じ縮退枝で成立する。
残る第2射影 `GeoCoqPj OI O y` を示す。もし `y=O` なら
縮退枝で成立する。もし `y≠O` なら `O,y` は軸 `OI` 上の
異なる二点なので、直線 `Oy` と `OI` は共線点集合が一致する。
したがって一致線として `OI∥Oy` が成立し、第2射影の強枝
を得る。すべての `y` について四射影の条件が満たされた。

**右零元・存在。** 任意の軸点 `x` に対し、既証明の第1射影
存在定理から `GeoCoqPj IJ x A'` かつ `A'∈OJ` となる点
`A'` を取る。`C'=A'` と置けば、第2射影
`GeoCoqPj OI A' A'` は縮退枝で成立する。第3射影
`GeoCoqPj OJ O A'` は、`A'=O` なら縮退枝、`A'≠O`
なら `A'∈OJ` と二点による直線外延性から `OJ∥OA'`
という強枝で成立する。最後に第1射影が強枝 `IJ∥xA'`
なら双方の線分の端点を反転して `JI∥A'x` を得る。
第1射影が縮退枝 `x=A'` なら等式を反転して `A'=x`
を得る。いずれも最終射影 `GeoCoqPj JI A' x` が成立する。

**左零元・一意性。** `GeoCoqSum O y z` の任意の補助点
`A,C` を取る。第1射影 `GeoCoqPj IJ O A` の強枝を
仮定すると、非退化線 `OA` は `IJ` に平行で、`O,A` は
ともに `OJ` に属する。直線外延性により `OA=OJ` となり
`IJ∥OJ` が従うが、枠の非共線性と矛盾する。よって縮退枝
`A=O` しかなく、第2射影は `GeoCoqPj OI O C` となる。
この第2射影が縮退なら `C=O∈OI`。強枝なら `OI` と
`OC` は共通点 `O` を持つ平行線なので同一直線となり
`C∈OI`。続く第3射影 `GeoCoqPj OJ y C` が強枝なら
`y,C∈OI` かつ `y≠C` であるため `yC=OI` となり、
`OJ∥OI` を強制して矛盾する。よって縮退枝 `y=C`。
最終射影 `GeoCoqPj JI y z` が強枝なら、異なる軸点
`y,z` を結ぶ直線は `OI` そのものなので `JI∥OI` と
なり、枠の `J∉OI` と矛盾する。従って最後も縮退枝
`y=z` である。軸点の外延性から `z=y` が従う。

**右零元・一意性。** `GeoCoqSum x O z` とする。`x=O`
なら先の左零一意性を適用して `z=O=x`。`x≠O` なら
第1射影 `GeoCoqPj IJ x A` の縮退枝 `x=A` は
`x∈OI∩OJ` を含意して矛盾するので強枝 `IJ∥xA`。
既証明の非原点射影補題より `A≠O`。`A∈OJ` と
二軸交点一意性から `A∉OI` が従う。第3射影
`GeoCoqPj OJ O C` の縮退枝は `C=O∈OJ`、強枝では
`OJ` と `OC` が `O` を共有する平行線となり `C∈OJ`。
第2射影 `GeoCoqPj OI A C` が強枝なら、`A,C∈OJ`
かつ `A≠C` から `AC=OJ` となり、`OI∥OJ` という
矛盾が生じる。よって縮退枝 `A=C` である。最終射影
`GeoCoqPj JI A z` で縮退枝 `A=z` は `A∉OI` かつ
`z∈OI` と矛盾する。よって強枝 `JI∥Az`。
第1強枝 `IJ∥xA` を双方の端点反転によって
`JI∥Ax` に変えると、`x,z` はいずれも `OI` 上で
`A` は `OI` の外、`Ax,Az` はいずれも `JI` に平行。
既証明の斜投影一意性を投影先 `OI`・方向 `JI`・元 `A`
に適用して `x=z` を得る。軸点外延性によって `z=x`。

左右の零元については `AddGraph` でも存在と一意性が既に
証明されているので、それぞれ同じ出力になることから、
任意の第2変数または第1変数に対して両図式の同値が従う。
-/

/-- 左零元のGeoCoq加法図式は全軸点について構成できる。 -/
theorem geoCoqSum_left_zero_tarski
    (f : Frame Point) (y : AxisPoint f) :
    GeoCoqSum f (axisZero f) y y := by
  have hSecond : GeoCoqPj f.O f.I f.O y.1 := by
    by_cases hOy : f.O = y.1
    · exact Or.inr hOy
    · have hLine : ∀ S, Col f.O f.I S ↔ Col f.O y.1 S :=
        col_line_extensionality_tarski
          f.O_ne_I hOy (col_left f.O f.I) y.2
      exact Or.inl
        (parallel_retarget_right_of_line_eq
          (parallel_refl f.O_ne_I) hOy hLine)
  exact ⟨f.O, y.1, Or.inr rfl,
    col_left f.O f.J, hSecond, Or.inr rfl, Or.inr rfl⟩

/-- 右零元のGeoCoq加法図式は全軸点について構成できる。 -/
theorem geoCoqSum_right_zero_tarski
    (f : Frame Point) (x : AxisPoint f) :
    GeoCoqSum f x (axisZero f) x := by
  obtain ⟨A', hFirst, hAxis⟩ :=
    geoCoqSum_first_projection_exists_tarski f x
  have hThird : GeoCoqPj f.O f.J f.O A' := by
    by_cases hOA : f.O = A'
    · exact Or.inr hOA
    · have hLine : ∀ S, Col f.O f.J S ↔ Col f.O A' S :=
        col_line_extensionality_tarski
          f.O_ne_J hOA (col_left f.O f.J) hAxis
      exact Or.inl
        (parallel_retarget_right_of_line_eq
          (parallel_refl f.O_ne_J) hOA hLine)
  have hLast : GeoCoqPj f.J f.I A' x.1 := by
    rcases hFirst with hPar | hEq
    · exact Or.inl (parallel_reverse_both hPar)
    · exact Or.inr hEq.symm
  exact ⟨A', A', hFirst, hAxis,
    Or.inr rfl, hThird, hLast⟩

/-- 第1投影の原点からOJへの出力は、原点以外になれない。 -/
theorem geoCoqSum_first_zero_projection_eq_origin_tarski
    (f : Frame Point) (A : Point)
    (hFirst : GeoCoqPj f.I f.J f.O A)
    (hAxis : Col f.O f.J A) : A = f.O := by
  rcases hFirst with hPar | hEq
  · have hLine : ∀ S, Col f.O A S ↔ Col f.O f.J S := by
      intro S
      exact (col_line_extensionality_tarski
        f.O_ne_J hPar.2.1 (col_left f.O f.J) hAxis S).symm
    have hBad : Parallel f.I f.J f.O f.J :=
      parallel_retarget_right_of_line_eq hPar f.O_ne_J hLine
    exact False.elim (frame_IJ_not_parallel_OJ f hBad)
  · exact hEq.symm

/-- 左零元を第1入力とするGeoCoq図式の出力は一意である。 -/
theorem geoCoqSum_left_zero_unique_tarski
    (f : Frame Point) (y z : AxisPoint f)
    (hSum : GeoCoqSum f (axisZero f) y z) : z = y := by
  obtain ⟨A, C, hFirst, hAxis, hSecond, hThird, hLast⟩ := hSum
  have hAeq : A = f.O :=
    geoCoqSum_first_zero_projection_eq_origin_tarski f A hFirst hAxis
  subst A
  have hCaxis : Col f.O f.I C := by
    rcases hSecond with hPar | hEq
    · have hSame : ∀ S, Col f.O f.I S ↔ Col f.O C S :=
        parallel_same_of_intersection hPar
          (col_left f.O f.I) (col_left f.O C)
      exact (hSame C).mpr (col_right f.O C)
    · have hCeq : C = f.O := hEq.symm
      simpa [hCeq] using (col_left f.O f.I)
  have hYCeq : y.1 = C := by
    rcases hThird with hPar | hEq
    · have hLine : ∀ S, Col y.1 C S ↔ Col f.O f.I S := by
        intro S
        exact (col_line_extensionality_tarski
          f.O_ne_I hPar.2.1 y.2 hCaxis S).symm
      have hBad : Parallel f.O f.J f.O f.I :=
        parallel_retarget_right_of_line_extensionality_tarski
          hPar f.O_ne_I hLine
      exact False.elim (frame_axes_not_parallel f (parallel_symm hBad))
    · exact hEq
  subst C
  have hYZeq : y.1 = z.1 := by
    rcases hLast with hPar | hEq
    · have hLine : ∀ S, Col y.1 z.1 S ↔ Col f.O f.I S := by
        intro S
        exact (col_line_extensionality_tarski
          f.O_ne_I hPar.2.1 y.2 z.2 S).symm
      have hBad : Parallel f.J f.I f.O f.I :=
        parallel_retarget_right_of_line_extensionality_tarski
          hPar f.O_ne_I hLine
      exact False.elim
        (frame_JX_not_parallel_OI f (axisOne f) hBad)
    · exact hEq
  exact Subtype.ext hYZeq.symm

/-- 右零元を第2入力とするGeoCoq図式の出力は一意である。 -/
theorem geoCoqSum_right_zero_unique_tarski
    (f : Frame Point) (x z : AxisPoint f)
    (hSum : GeoCoqSum f x (axisZero f) z) : z = x := by
  by_cases hx : x.1 = f.O
  · have hxeq : x = axisZero f := Subtype.ext hx
    subst x
    exact geoCoqSum_left_zero_unique_tarski f (axisZero f) z hSum
  obtain ⟨A, C, hFirst, hAxis, hSecond, hThird, hLast⟩ := hSum
  have hFirstPar : Parallel f.I f.J x.1 A := by
    rcases hFirst with hPar | hEq
    · exact hPar
    · have hXOJ : Col f.O f.J x.1 := by simpa [hEq] using hAxis
      exact False.elim
        (hx (frame_axes_intersection_only_origin_tarski f x.1 x.2 hXOJ))
  have hAneO : A ≠ f.O :=
    geoCoq_firstPj_not_origin f x A hx (Or.inl hFirstPar)
  have hAoff : ¬ Col f.O f.I A := by
    intro hAOI
    exact hAneO
      (frame_axes_intersection_only_origin_tarski f A hAOI hAxis)
  have hCOJ : Col f.O f.J C := by
    rcases hThird with hPar | hEq
    · have hSame : ∀ S, Col f.O f.J S ↔ Col f.O C S :=
        parallel_same_of_intersection hPar
          (col_left f.O f.J) (col_left f.O C)
      exact (hSame C).mpr (col_right f.O C)
    · have hCeq : C = f.O := hEq.symm
      simpa [hCeq] using (col_left f.O f.J)
  have hAC : A = C := by
    rcases hSecond with hPar | hEq
    · have hLine : ∀ S, Col A C S ↔ Col f.O f.J S := by
        intro S
        exact (col_line_extensionality_tarski
          f.O_ne_J hPar.2.1 hAxis hCOJ S).symm
      have hBad : Parallel f.O f.I f.O f.J :=
        parallel_retarget_right_of_line_extensionality_tarski
          hPar f.O_ne_J hLine
      exact False.elim (frame_axes_not_parallel f hBad)
    · exact hEq
  subst C
  have hAneZ : A ≠ z.1 := by
    intro heq
    exact hAoff (by simpa [heq] using z.2)
  have hLastPar : Parallel f.J f.I A z.1 := by
    rcases hLast with hPar | hEq
    · exact hPar
    · exact False.elim (hAneZ hEq)
  have hLineExt : ∀ A B C D : Point,
      A ≠ B → C ≠ D → Col A B C → Col A B D →
      ∀ S, Col A B S ↔ Col C D S := by
    intro A B C D hAB hCD hC hD
    exact col_line_extensionality_tarski hAB hCD hC hD
  have hxz : x.1 = z.1 :=
    directional_projection_unique_of_playfair
      tarski_playfair hLineExt f.O f.I f.J f.I A x.1 z.1
      f.O_ne_I hAoff x.2 z.2
      (parallel_reverse_both hFirstPar) hLastPar
  exact Subtype.ext hxz.symm

/-- 左零元では幾何学的加法とGeoCoq図式が全ての出力で同値。 -/
theorem addGraph_left_zero_iff_geoCoqSum_tarski
    (f : Frame Point) (y z : AxisPoint f) :
    AddGraph f (axisZero f) y z ↔
    GeoCoqSum f (axisZero f) y z := by
  constructor
  · intro h
    have hz : z = y := add_zero_left_unique f y z h
    simpa [hz] using geoCoqSum_left_zero_tarski f y
  · intro h
    have hz : z = y := geoCoqSum_left_zero_unique_tarski f y z h
    simpa [hz] using add_zero_left f y

/-- 右零元でも幾何学的加法とGeoCoq図式が全ての出力で同値。 -/
theorem addGraph_right_zero_iff_geoCoqSum_tarski
    (f : Frame Point) (x z : AxisPoint f) :
    AddGraph f x (axisZero f) z ↔
    GeoCoqSum f x (axisZero f) z := by
  constructor
  · intro h
    have hz : z = x :=
      (operation_graphs_functional_tarski f).1
        x (axisZero f) z x h (add_zero_right_tarski f x)
    simpa [hz] using geoCoqSum_right_zero_tarski f x
  · intro h
    have hz : z = x := geoCoqSum_right_zero_unique_tarski f x z h
    simpa [hz] using add_zero_right_tarski f x

/-!
### 非退化加法図式から第一の線分合同を導く：自然言語証明

`x,y,z` は軸 `OI` 上の点、`x≠O`、`y≠z` とする。
加法の強い作図の証人 `T` は `OJ∥xT`、`OI∥JT`、
`Jy∥Tz` の三条件を満たしている。`x∈OI` かつ `x≠O`
なので二点による直線外延性から直線 `Ox=OI` を得る。
`OI∥JT` を対称化し、右側の直線 `OI` を `Ox` に
置き換えると `JT∥Ox`。最初の条件の右線分の向きを
反転すると `OJ∥Tx`。点 `T` が `OJ` 上にあると仮定
した場合、`J,T` は `OI∥JT` によって異なるため、
`JT=OJ` が二点による直線外延性で従う。すると
`OI∥OJ` となり、非共線な枠の二軸が平行ではないという
既証明と矛盾する。したがって `O,J,T` は非共線。
以上の二本の平行関係と非共線性を、既証明の厳密な
平行四辺形 `O,J,T,x` の対辺合同に適用する。
第2対の合同と合同の向きの反転から `Cong O x J T` を得る。

次に `y,z∈OI` かつ `y≠z` なので直線 `zy=OI`。
したがって `OI∥JT` を対称化して直線 `zy` へ
置き換え、`JT∥zy` を得る。`Jy∥Tz` を対称化し、
右側の直線の向きを反転して `Tz∥yJ` を得る。
`OI∥JT` の一方の定義点 `J` は `OI` の外にあるので、
両直線は交わらない。特に軸点 `z` は `JT` に属さない。
よって `J,T,z` は非共線である。厳密な平行四辺形
`J,T,z,y` の対辺合同から `Cong J T z y` を得て、
右線分を反転し `Cong J T y z` とする。先の
`Cong O x J T` との合同推移律により `Cong O x y z`。
以上はTarskiの既証明の非退化平行四辺形合同を2回用いた
完全な導出であり、和の交換律や結合律は使用していない。
-/

/-- 非退化な幾何学的加法では|Ox|=|yz|が成立する。 -/
theorem addGraph_strong_opposite_cong_tarski
    (f : Frame Point) (x y z : AxisPoint f) (T : Point)
    (hx : x.1 ≠ f.O) (hyz : y.1 ≠ z.1)
    (hVert : Parallel f.O f.J x.1 T)
    (hHorz : Parallel f.O f.I f.J T)
    (hDiag : Parallel f.J y.1 T z.1) :
    Cong f.O x.1 y.1 z.1 := by
  have hLineOx : ∀ S, Col f.O f.I S ↔ Col f.O x.1 S :=
    col_line_extensionality_tarski f.O_ne_I hx.symm
      (col_left f.O f.I) x.2
  have hJT_Ox : Parallel f.J T f.O x.1 :=
    parallel_retarget_right_of_line_eq
      (parallel_symm hHorz) hx.symm hLineOx
  have hNoncolOJT : ¬ Col f.O f.J T := by
    intro hT
    have hLine : ∀ S, Col f.J T S ↔ Col f.O f.J S := by
      intro S
      exact (col_line_extensionality_tarski
        f.O_ne_J hHorz.2.1 (col_right f.O f.J) hT S).symm
    have hBad : Parallel f.O f.I f.O f.J :=
      parallel_retarget_right_of_line_extensionality_tarski
        hHorz f.O_ne_J hLine
    exact frame_axes_not_parallel f hBad
  obtain ⟨_, hCongJT_xO⟩ :=
    strict_parallelogram_opposite_cong_tarski
      hNoncolOJT (parallel_reverse_right hVert)
      (parallel_reverse_right hJT_Ox)
  have hCongOxJT : Cong f.O x.1 f.J T :=
    cong_reverse_left (cong_symm hCongJT_xO)
  have hLineZy : ∀ S, Col f.O f.I S ↔ Col z.1 y.1 S :=
    col_line_extensionality_tarski f.O_ne_I hyz.symm
      z.2 y.2
  have hJT_Zy : Parallel f.J T z.1 y.1 :=
    parallel_retarget_right_of_line_extensionality_tarski
      (parallel_symm hHorz) hyz.symm hLineZy
  have hNoncolJTz : ¬ Col f.J T z.1 := by
    intro hZ
    have hDisj : ∀ S,
        ¬ (Col f.O f.I S ∧ Col f.J T S) :=
      playfair_strict_of_off_reference_tarski
        hHorz f.noncol (col_left f.J T)
    exact hDisj z.1 ⟨z.2, hZ⟩
  obtain ⟨hCongJT_zy, _⟩ :=
    strict_parallelogram_opposite_cong_tarski
      hNoncolJTz hJT_Zy
      (parallel_reverse_right (parallel_symm hDiag))
  have hCongJT_yz : Cong f.J T y.1 z.1 :=
    cong_reverse_right hCongJT_zy
  exact cong_trans hCongOxJT hCongJT_yz

/-!
### GeoCoq `plg_uniqueness` の中点部分：自然言語完全証明

同じ3点 `A,B,C` と二つの候補 `D,D'` に対し、
`AC` と `BD` が共通中点 `M` を持ち、さらに `AC`
と `BD'` が共通中点 `N` を持つと仮定する。前者の
第1条件から `M` は線分 `AC` の中点であり、後者の
第1条件から `N` も同じ線分 `AC` の中点である。
既証明のTarski中点一意性 `mul_midpoint_center_unique_tarski`
を適用して `M=N` を得る。この等式で後者の中心を
`M` に置き換えると、`M` は `BD` と `BD'` の
両方の中点である。Tarski線分構成から既に証明した
`mul_reflection_exists_unique M B` は、中心 `M` に
関して点 `B` を反転した点が唯一であることを主張する。
その反転像を `P` とする。`M` が `BD` の中点なので
`D=P`、`M` が `BD'` の中点なので `D'=P` が
それぞれ反転像の一意性から従う。等式の推移律によって
`D=D'`。線分が零長となる場合も中点一意性と反転一意性
の既証明に含まれており、別の退化仮定を追加しない。
この命題はGeoCoqの `plg_uniqueness` で必要となる
第4頂点の決定を、対角線中点だけから導いたものである。
-/

/-- Two diagonals with common midpoints determine the fourth vertex. -/
theorem diagonal_midpoints_fourth_vertex_unique_tarski
    {A B C D D' : Point}
    (h1 : ∃ M : Point,
      MulMidpoint M A C ∧ MulMidpoint M B D)
    (h2 : ∃ N : Point,
      MulMidpoint N A C ∧ MulMidpoint N B D') :
    D = D' := by
  obtain ⟨M, hMAC, hMBD⟩ := h1
  obtain ⟨N, hNAC, hNBD'⟩ := h2
  have hMN : M = N :=
    mul_midpoint_center_unique_tarski hMAC hNAC
  subst N
  obtain ⟨P, hP, hUnique⟩ := mul_reflection_exists_unique M B
  have hDP : D = P := hUnique D hMBD
  have hD'P : D' = P := hUnique D' hNBD'
  exact hDP.trans hD'P.symm

/-!
### GeoCoq Ch11 `CongA` と `conga_refl`：自然言語完全証明

GeoCoqの角合同 `CongA A B C D E F` は、両角をなす
四本の半直線が非退化であることと、各半直線をその方向へ
伸長した点 `A',C',D',F'` の存在で定義する。
その条件はそれぞれ `Bet B A A'`、`Cong A A' E D`、
`Bet B C C'`、`Cong C C' E F`、`Bet E D D'`、
`Cong D D' B A`、`Bet E F F'`、`Cong F F' B C`
および `Cong A' C' D' F'` である。ここでの角合同は
外部の角度・実数値を使わず、原始述語 `Bet`,`Cong`
の論理式として導入する。

非退化角 `ABC`、つまり `A≠B` かつ `C≠B` に対し
`CongA A B C A B C` を証明する。まずTarskiの線分
作図公理を点 `B,A,B,A` に適用し、`Bet B A A'`
と `Cong A A' B A` を満たす点 `A'` を取る。
同じ公理を点 `B,C,B,C` に適用し、`Bet B C C'`
と `Cong C C' B C` を満たす点 `C'` を取る。
比較先の角は同じ `ABC` であるから、そちらの延長点
には `D'=A'`、`F'=C'` を選ぶ。定義が要求する
四つの非退化条件は、仮定 `A≠B`、`C≠B` を
それぞれ二度用いて満たす。八つのBet/Cong条件は
上記の二つの線分作図結果を、元の角側と比較先の角側で
それぞれ再使用すればすべて満たされる。最後の条件
`Cong A' C' A' C'` は、原始合同公理から証明済みの
`congr_refl` により成立する。これで定義の全条件を
検証したので、角合同の反射律が証明された。
-/

/-- GeoCoq's four-ray angle congruence, defined only by Tarski Bet/Cong. -/
def GeoCoqCongA (A B C D E F : Point) : Prop :=
  A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E ∧
  ∃ A' C' D' F' : Point,
    Bet B A A' ∧ Cong A A' E D ∧
    Bet B C C' ∧ Cong C C' E F ∧
    Bet E D D' ∧ Cong D D' B A ∧
    Bet E F F' ∧ Cong F F' B C ∧
    Cong A' C' D' F'

/-- GeoCoq Ch11 `conga_refl`: an angle is congruent to itself. -/
theorem geoCoqCongA_refl_tarski
    {A B C : Point} (hAB : A ≠ B) (hCB : C ≠ B) :
    GeoCoqCongA A B C A B C := by
  obtain ⟨A', hBA, hAA'⟩ := segment_construction B A B A
  obtain ⟨C', hBC, hCC'⟩ := segment_construction B C B C
  exact ⟨hAB, hCB, hAB, hCB, A', C', A', C',
    hBA, hAA', hBC, hCC', hBA, hAA', hBC, hCC',
    congr_refl A' C'⟩

/-!
**角合同の対称律の自然言語証明。** `CongA A B C D E F`
を仮定し、定義の非退化条件4つと存在証人
`A0,C0,D0,F0`、八つのBet/Cong条件、最後の
`Cong A0 C0 D0 F0` を取り出す。比較する二つの角を
交換した `CongA D E F A B C` の最初の四条件は、
元の第三・第四・第一・第二の非退化条件である。
新しい存在証人には `D0,F0,A0,C0` をこの順に選ぶ。
新しい最初の四つのBet/Cong条件は、元の後半四条件と
一字ずつ同じである。新しい後半四条件は元の前半四条件
と同じである。残る線分合同だけは向きが逆なので、
元の `Cong A0 C0 D0 F0` にTarskiからの既証明
`cong_symm` を適用して `Cong D0 F0 A0 C0` を得る。
これで新しい角合同の全ての条件が満たされ、対称律が成立する。
-/

/-- GeoCoq Ch11 `conga_sym`, by swapping angle witnesses. -/
theorem geoCoqCongA_symm_tarski
    {A B C D E F : Point}
    (h : GeoCoqCongA A B C D E F) :
    GeoCoqCongA D E F A B C := by
  rcases h with
    ⟨hAB, hCB, hDE, hFE, A0, C0, D0, F0,
      hBA, hAA, hBC, hCC, hED, hDD, hEF, hFF, hLast⟩
  exact ⟨hDE, hFE, hAB, hCB, D0, F0, A0, C0,
    hED, hDD, hEF, hFF, hBA, hAA, hBC, hCC,
    cong_symm hLast⟩

/-!
**両角の二本の腕を同時に交換する自然言語証明。**
`CongA A B C D E F` の定義から、四つの非退化条件、
証人 `A0,C0,D0,F0` と九つの関係を取り出す。
角の腕を同時に入れ替えた目標は `CongA C B A F E D`
である。非退化条件を第二・第一・第四・第三の順に
並べ替える。証人は `C0,A0,F0,D0` とし、八つの
Bet/Cong条件も元の第二・第一・第四・第三の順で
再利用する。最後の合同については、元の
`Cong A0 C0 D0 F0` に既証明の合同の両端点反転
`cong_reverse_both` を適用して
`Cong C0 A0 F0 D0` とする。これですべての条件が
満たされ、両腕交換が成立する。角合同の推移律や
実数値の角度は使わない。
-/

/-- GeoCoq `conga_comm`, simultaneous reversal of both angle arms. -/
theorem geoCoqCongA_swap_arms_tarski
    {A B C D E F : Point}
    (h : GeoCoqCongA A B C D E F) :
    GeoCoqCongA C B A F E D := by
  rcases h with
    ⟨hAB, hCB, hDE, hFE, A0, C0, D0, F0,
      hBA, hAA, hBC, hCC, hED, hDD, hEF, hFF, hLast⟩
  exact ⟨hCB, hAB, hFE, hDE, C0, A0, F0, D0,
    hBC, hCC, hBA, hAA, hEF, hFF, hED, hDD,
    cong_reverse_both hLast⟩

/-!
### GeoCoq Ch11 `cong2_conga_cong`（SAS）：自然言語完全証明

`CongA A B C D E F`、`Cong A B D E`、
`Cong B C E F` を仮定する。角合同の定義から
四つの延長点 `A0,C0,D0,F0` と対応する8つの
Bet/Cong条件および `Cong A0 C0 D0 F0` を取り出す。
まず合同の両線分の端点を反転して `Cong B A E D`
を得る。角合同の証人条件 `Cong A A0 E D` と
`Cong D D0 B A` を合同対称律・推移律でつなぐと
`Cong A A0 D D0` が従う。`Bet B A A0` と
`Bet E D D0` の二本の直線上における位置関係、
`Cong B A E D`、`Cong A A0 D D0` に、
既証明の隣接線分合同の加法補題 `segment_cong_add`
を適用すると、全長について `Cong B A0 E D0` を得る。

同様に第2辺 `Cong B C E F` と、角合同証人の
`Cong C C0 E F`、`Cong F F0 B C` を
合同対称律・推移律でつないで `Cong C C0 F F0`
を得る。`Bet B C C0`、`Bet E F F0` に
隣接線分合同補題を適用し、`Cong B C0 E F0` を得る。
ここまでの比較の全長は `BA0≅ED0` と `BC0≅EF0`、
末端部分は `AA0≅DD0` と `CC0≅FF0`、
二つの延長端点を結ぶ辺は `A0C0≅D0F0` である。

既証明の内側5線分定理 `inner_five_segment` を
`Bet B A A0`、`Bet E D D0` に対して用いる。
必要な4本の合同は順に `BA0≅ED0`、
`AA0≅DD0`、`BC0≅EF0`、`A0C0≅D0F0`
で、すべて前段で確立したので、結論
`Cong A C0 D F0` を得る。次に同じ内側5線分定理を
`Bet B C C0`、`Bet E F F0` に対して用いる。
必要な4本の合同は `BC0≅EF0`、`CC0≅FF0`、
`BA≅ED`、および先の `AC0≅DF0` の両端を
反転した `C0A≅F0D` である。従って
`Cong C A F D` を得る。最後にこの線分合同の
両端点を反転して `Cong A C D F` とする。
これで角合同と挟む二辺の合同から第三辺の合同が
従うことが、5線分公理からの既証明だけで示された。
零長線分を含む場合も内側5線分定理の既証明が処理する。
-/

/-- GeoCoq Ch11 `cong2_conga_cong`: synthetic SAS from five segments. -/
theorem geoCoqCongA_sas_tarski
    {A B C D E F : Point}
    (hAngle : GeoCoqCongA A B C D E F)
    (hABDE : Cong A B D E)
    (hBCEF : Cong B C E F) :
    Cong A C D F := by
  rcases hAngle with
    ⟨_, _, _, _, A0, C0, D0, F0,
      hBAA0, hAA0ED, hBCC0, hCC0EF,
      hEDD0, hDD0BA, hEFF0, hFF0BC, hA0C0D0F0⟩
  have hBAED : Cong B A E D := cong_reverse_both hABDE
  have hAA0DD0 : Cong A A0 D D0 :=
    cong_trans hAA0ED
      (cong_trans (cong_symm hBAED) (cong_symm hDD0BA))
  have hBA0ED0 : Cong B A0 E D0 :=
    segment_cong_add hBAA0 hEDD0 hBAED hAA0DD0
  have hCC0FF0 : Cong C C0 F F0 :=
    cong_trans hCC0EF
      (cong_trans (cong_symm hBCEF) (cong_symm hFF0BC))
  have hBC0EF0 : Cong B C0 E F0 :=
    segment_cong_add hBCC0 hEFF0 hBCEF hCC0FF0
  have hAC0DF0 : Cong A C0 D F0 :=
    inner_five_segment hBAA0 hEDD0 hBA0ED0
      hAA0DD0 hBC0EF0 hA0C0D0F0
  have hCAFD : Cong C A F D :=
    inner_five_segment hBCC0 hEFF0 hBC0EF0
      hCC0FF0 hBAED (cong_reverse_both hAC0DF0)
  exact cong_reverse_both hCAFD

/-!
**角合同の擬反射律の自然言語完全証明。** `A≠B`、
`C≠B` とする。線分作図公理を点 `B,A,B,C` に適用し、
`Bet B A A0` と `Cong A A0 B C` を満たす点 `A0`
を取る。同じ公理を点 `B,C,B,A` に適用して
`Bet B C C0` と `Cong C C0 B A` を満たす点
`C0` を取る。両腕を交換した角 `CBA` の証人には
`D0=C0`、`F0=A0` を使う。元の角 `ABC` 側の
四つのBet/Cong条件は両線分作図の結果そのものであり、
比較先の角 `CBA` 側の四条件も同じ結果を逆順に用いて
満たされる。四つの非退化条件は `A≠B`、`C≠B`
の二度の使用で成立する。残る線分合同
`Cong A0 C0 C0 A0` はTarskiの合同擬反射公理
`cong_pseudo_reflexivity` そのものである。
したがって `CongA A B C C B A` が成立する。
-/

/-- GeoCoq Ch11 `conga_pseudo_refl`, proved by segment constructions. -/
theorem geoCoqCongA_pseudo_refl_tarski
    {A B C : Point} (hAB : A ≠ B) (hCB : C ≠ B) :
    GeoCoqCongA A B C C B A := by
  obtain ⟨A0, hBA, hAA⟩ := segment_construction B A B C
  obtain ⟨C0, hBC, hCC⟩ := segment_construction B C B A
  exact ⟨hAB, hCB, hCB, hAB, A0, C0, C0, A0,
    hBA, hAA, hBC, hCC, hBC, hCC, hBA, hAA,
    cong_pseudo_reflexivity A0 C0⟩

/-!
### 加法の第2線分合同を包含角の合同へ還元：自然言語完全証明

非零軸点 `x`、軸点 `y,z`、`y≠z`、および
`AddGraph` の強い証人 `T` が満たす
`OJ∥xT`、`OI∥JT`、`Jy∥Tz` を仮定する。
さらに、角 `OJy` と `xTz` の合同
`GeoCoqCongA O J y x T z` を明示的に仮定する。
この角合同だけは、平行線に対する角の移送と図形の
同側・反対側の判定に関わる次段階の証明命題である。

第1の線分合同を作る。`x∈OI` かつ `x≠O` なので、
二点で決まる直線 `Ox` は軸 `OI` と一致する。
`OI∥JT` を反転・再指定して `JT∥xO`、
`OJ∥xT` の第2線分を反転して `OJ∥Tx`。
もし `O,J,T` が共線なら非退化な直線 `JT` が
`OJ` と一致し、`OI∥OJ` となって枠の非共線性に
反する。よって厳密な平行四辺形 `O,J,T,x` の
対辺合同定理を適用し `Cong O J T x` を得る。
右線分を反転して `Cong O J x T` を得る。

第2の合同を作る。`y,z∈OI` かつ `y≠z` なので
直線 `zy` と `OI` は一致する。これを用いて
`OI∥JT` から `JT∥zy` を得る。第三の平行線
`Jy∥Tz` の向きを交換して `Tz∥yJ` を得る。
`OI∥JT` と `J∉OI` から二直線は交点を持たず、
軸点 `z` は `JT` の外にある。したがって
`J,T,z` は非共線である。厳密な平行四辺形
`J,T,z,y` の対辺合同定理を適用すると
`Cong T z y J`。右線分反転、合同対称化により
`Cong J y T z` が従う。

最後に既証明のTarskiによるSAS定理
`geoCoqCongA_sas_tarski` に対し、包含角合同
`CongA O J y x T z`、第1辺合同 `OJ≅xT`、
第2辺合同 `Jy≅Tz` を渡す。結論は正確に
`Cong O y x z` である。角合同をこの定理の
明示前提として保持することで、加法の一般的な
第2線分合同に残る証明が一つの幾何命題として確定した。
-/

/-- Conditional reduction of the remaining sum-congruence side to one
    explicitly stated synthetic angle-congruence configuration. -/
theorem addGraph_strong_second_opposite_cong_of_angle_tarski
    (f : Frame Point) (x y z : AxisPoint f) (T : Point)
    (hx : x.1 ≠ f.O) (hyz : y.1 ≠ z.1)
    (hVert : Parallel f.O f.J x.1 T)
    (hHorz : Parallel f.O f.I f.J T)
    (hDiag : Parallel f.J y.1 T z.1)
    (hAngle : GeoCoqCongA f.O f.J y.1 x.1 T z.1) :
    Cong f.O y.1 x.1 z.1 := by
  have hLineOx : ∀ S, Col f.O f.I S ↔ Col f.O x.1 S :=
    col_line_extensionality_tarski f.O_ne_I hx.symm
      (col_left f.O f.I) x.2
  have hJT_Ox : Parallel f.J T f.O x.1 :=
    parallel_retarget_right_of_line_eq
      (parallel_symm hHorz) hx.symm hLineOx
  have hNoncolOJT : ¬ Col f.O f.J T := by
    intro hT
    have hLine : ∀ S, Col f.J T S ↔ Col f.O f.J S := by
      intro S
      exact (col_line_extensionality_tarski
        f.O_ne_J hHorz.2.1 (col_right f.O f.J) hT S).symm
    have hBad : Parallel f.O f.I f.O f.J :=
      parallel_retarget_right_of_line_extensionality_tarski
        hHorz f.O_ne_J hLine
    exact frame_axes_not_parallel f hBad
  obtain ⟨hCongOJTx, _⟩ :=
    strict_parallelogram_opposite_cong_tarski
      hNoncolOJT (parallel_reverse_right hVert)
      (parallel_reverse_right hJT_Ox)
  have hCongOJxT : Cong f.O f.J x.1 T :=
    cong_reverse_right hCongOJTx
  have hLineZy : ∀ S, Col f.O f.I S ↔ Col z.1 y.1 S :=
    col_line_extensionality_tarski f.O_ne_I hyz.symm
      z.2 y.2
  have hJT_Zy : Parallel f.J T z.1 y.1 :=
    parallel_retarget_right_of_line_extensionality_tarski
      (parallel_symm hHorz) hyz.symm hLineZy
  have hNoncolJTz : ¬ Col f.J T z.1 := by
    intro hZ
    have hDisj : ∀ S,
        ¬ (Col f.O f.I S ∧ Col f.J T S) :=
      playfair_strict_of_off_reference_tarski
        hHorz f.noncol (col_left f.J T)
    exact hDisj z.1 ⟨z.2, hZ⟩
  obtain ⟨_, hCongTzyJ⟩ :=
    strict_parallelogram_opposite_cong_tarski
      hNoncolJTz hJT_Zy
      (parallel_reverse_right (parallel_symm hDiag))
  have hCongJyTz : Cong f.J y.1 T z.1 :=
    cong_symm (cong_reverse_right hCongTzyJ)
  exact geoCoqCongA_sas_tarski hAngle hCongOJxT hCongJyTz

/-!
### 加法交換律の幾何学的核心：二つの基準点による出力一意性

**自然言語による完全証明。** `x,y,z,w` を軸 `OI` 上の点とし、
`x ≠ y` と、二つの候補 `z,w` の両方について
`Ox ≡ yz` および `Oy ≡ xz`（`w` についても同じ二つの合同）
を仮定する。まず `x ≠ y` により二点 `x,y` は異なる。
両点は `OI` にあるので、Tarskiの直線外延性から `xy` と
`OI` は同一の直線であり、従って `z` は `xy` 上にある。

合同の対称律・推移律を適用する。`Oy ≡ xz` と
`Oy ≡ xw` から `xz ≡ xw` が従う。同様に
`Ox ≡ yz` と `Ox ≡ yw` から `yz ≡ yw` が従う。
すなわち `z,w` は、異なる基準点 `x,y` の双方から等距離である。

Tarskiの五線分公理と線分構成公理から既に証明した
`col_equidistant_of_two_stations` は、`x,y` と同一直線上の
任意の点 `C` に対して `Cz ≡ Cw` が従うことを述べる。
ここで `C=z` と置くと `zz ≡ zw`。合同の対称律で
`zw ≡ zz` とし、Tarskiの合同同一性公理を適用すれば
`z=w` が得られる。`z` または `w` が `x,y` のいずれかと
一致する退化の場合も、既証明の二点距離伝播と合同同一性に
含まれているため追加の仮定を要しない。

この補題自体は加法・体の法則を前提とせず、加法作図の
二辺合同が各向きで得られれば `AddCommLaw` の
非退化部分の出力を同一化するために使える。
-/

theorem add_two_station_output_unique_tarski
    (f : Frame Point) (x y z w : AxisPoint f)
    (hxy : x ≠ y)
    (h1z : Cong f.O x.1 y.1 z.1)
    (h2z : Cong f.O y.1 x.1 z.1)
    (h1w : Cong f.O x.1 y.1 w.1)
    (h2w : Cong f.O y.1 x.1 w.1) : z = w := by
  have hxyPt : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  have hLine : ∀ S, Col f.O f.I S ↔ Col x.1 y.1 S :=
    col_line_extensionality_tarski f.O_ne_I hxyPt x.2 y.2
  have hCol : Col x.1 y.1 z.1 := (hLine z.1).mp z.2
  have hxzw : Cong x.1 z.1 x.1 w.1 :=
    cong_trans (cong_symm h2z) h2w
  have hyzw : Cong y.1 z.1 y.1 w.1 :=
    cong_trans (cong_symm h1z) h1w
  have hzzw : Cong z.1 z.1 z.1 w.1 :=
    col_equidistant_of_two_stations hxyPt hCol hxzw hyzw
  exact Subtype.ext (cong_identity z.1 w.1 z.1 (cong_symm hzzw))

/-!
### 加法の強枝では入力 `y` と出力 `z` が一致しない

**自然言語による完全証明。** `y=z` と仮定する。
加法の第3平行条件 `Jy∥Tz` は `Jy∥Ty` となる。
これら二直線は `y` を共有しているため、Tarskiの
「共通点を持つ平行直線は同一直線」から `T` が `Jy` 上にある。
従って `J,T,y` は共線。一方、第2平行条件 `OI∥JT` は
`J∉OI` を伴う真の平行である。Tarskiの平行直線非交差性
（既証明 `playfair_strict_of_off_reference_tarski`）を
`y` に適用すると、軸点であるため `y∈OI`、
上記の共線性により `y∈JT` となり矛盾する。
よって `y≠z`。退化線分の可能性も平行関係の定義が排除する。
-/

theorem addGraph_strong_target_ne_input_tarski
    (f : Frame Point) (y z : AxisPoint f) (T : Point)
    (hHorz : Parallel f.O f.I f.J T)
    (hDiag : Parallel f.J y.1 T z.1) : y.1 ≠ z.1 := by
  intro hyz
  have hline : ∀ S, Col f.J y.1 S ↔ Col T z.1 S :=
    parallel_same_of_intersection hDiag
      (col_right f.J y.1)
      (by simpa [hyz] using (col_right T z.1))
  have hJ_y_T : Col f.J y.1 T :=
    (hline T).mpr (col_left T z.1)
  have hJT_y : Col f.J T y.1 :=
    col_rotate (col_swap hJ_y_T)
  have hdisj : ∀ S, ¬ (Col f.O f.I S ∧ Col f.J T S) :=
    playfair_strict_of_off_reference_tarski
      hHorz f.noncol (col_left f.J T)
  exact hdisj y.1 ⟨y.2, hJT_y⟩

/-!
### 加法交換律の全場合を一つの角合同命題へ帰着

**自然言語による条件付き完全証明。** 与えられた
`AddGraph(x,y,z)` について、`x=O` または `y=O` の
場合は既証明の零枝交換から直ちに従う。`x=y` の場合は
二入力の交換後も同じ命題なので元の作図を返す。
残る `x≠O`,`y≠O`,`x≠y` の場合、幾何学的作図の
全域性から交換側 `AddGraph(y,x,w)` を作る。
両方とも強枝だから、それぞれ補助点 `T,T'` と
三組の平行条件を持つ。直前の命題から `y≠z`,`x≠w`。
既証明の非退化平行四辺形合同から
`Ox≡yz` と `Oy≡xw` を得る。

ここで唯一の明示前提である、加法図式に特有の
`CongA O J y x T z` と `CongA O J x y T' w` を用いる。
先にTarskiの五線分公理から証明した合角SAS命題により
それぞれ `Oy≡xz` と `Ox≡yw` を得る。
したがって出力 `z,w` は異なる二点 `x,y` について
同じ二つの距離を持つ。直前の二基準点一意性定理から `z=w`。
交換側の `w` を `z` に置き換えれば `AddGraph(y,x,z)`。

零・同一・非退化の全場合を尽くしている。
残る未証明事項はこの定理の前提 `hAngle` だけであり、
それがTarskiの公理から導けるまでは**無条件の交換律を
証明したとは主張しない**。
-/

theorem addCommLaw_of_strong_angle_tarski
    (f : Frame Point)
    (hAngle : ∀ (x y z : AxisPoint f) (T : Point),
      x.1 ≠ f.O → y.1 ≠ f.O →
      Parallel f.O f.J x.1 T →
      Parallel f.O f.I f.J T →
      Parallel f.J y.1 T z.1 →
      GeoCoqCongA f.O f.J y.1 x.1 T z.1) :
    AddCommLaw f := by
  have hTotal : AddTotal f := (operation_graphs_total_tarski f).1
  intro x y z hxy
  by_cases hx0 : x = axisZero f
  · exact add_comm_zero_branch_of_total f hTotal x y z
      (Or.inl hx0) hxy
  by_cases hy0 : y = axisZero f
  · exact add_comm_zero_branch_of_total f hTotal x y z
      (Or.inr hy0) hxy
  by_cases hsame : x = y
  · subst y
    exact hxy
  have hx : x.1 ≠ f.O := by
    intro heq
    exact hx0 (Subtype.ext heq)
  have hy : y.1 ≠ f.O := by
    intro heq
    exact hy0 (Subtype.ext heq)
  obtain ⟨w, hw, _⟩ := hTotal y x
  rcases hxy with ⟨hxo, _⟩ | ⟨_, T, hVert, hHorz, hDiag⟩
  · exact False.elim (hx hxo)
  rcases hw with ⟨hyo, _⟩ | ⟨_, T', hVert', hHorz', hDiag'⟩
  · exact False.elim (hy hyo)
  have hyz : y.1 ≠ z.1 :=
    addGraph_strong_target_ne_input_tarski f y z T hHorz hDiag
  have hxw : x.1 ≠ w.1 :=
    addGraph_strong_target_ne_input_tarski f x w T' hHorz' hDiag'
  have h1z : Cong f.O x.1 y.1 z.1 :=
    addGraph_strong_opposite_cong_tarski
      f x y z T hx hyz hVert hHorz hDiag
  have h2z : Cong f.O y.1 x.1 z.1 :=
    addGraph_strong_second_opposite_cong_of_angle_tarski
      f x y z T hx hyz hVert hHorz hDiag
      (hAngle x y z T hx hy hVert hHorz hDiag)
  have h1w : Cong f.O x.1 y.1 w.1 :=
    addGraph_strong_second_opposite_cong_of_angle_tarski
      f y x w T' hy hxw hVert' hHorz' hDiag'
      (hAngle y x w T' hy hx hVert' hHorz' hDiag')
  have h2w : Cong f.O y.1 x.1 w.1 :=
    addGraph_strong_opposite_cong_tarski
      f y x w T' hy hxw hVert' hHorz' hDiag'
  have hZW : z = w :=
    add_two_station_output_unique_tarski
      f x y z w hsame h1z h2z h1w h2w
  rw [hZW]
  exact Or.inr ⟨hy, T', hVert', hHorz', hDiag'⟩

/-!
### 加法図式の包含角：GeoCoqの二つの角定理への厳密な還元

**自然言語による条件付き完全証明。** 三つの平行関係
`OJ∥xT`, `OI∥JT`, `Jy∥Tz` を仮定する。最後に
必要な角の合同は `CongA O J y x T z` である。
ここでは以下の二つの角定理を明示前提として受け取る。

第一は、向かい側の二辺が平行で、線分 `AD` を `P` まで
延長し、二つの外側点が直線 `AD` の同側にあるときの
`CongA B A P C D P`（GeoCoq `par_preserves_conga_os`）。
第二は、同側条件の下で二つの角合同を合成して
`CongA A B C A' B' C'` を得る角合成
（GeoCoq `l11_22b`）である。この二命題の純Tarski証明は
まだ移植されておらず、この定理の引数として可視化する。

まず線分構成公理から `Bet J T Q` となる `Q` を作り、
`TQ≡JT` を得る。`JT` は平行関係から非零なので、
合同同一性により `T≠Q`。`J=Q` なら
`Bet J T J` となりBet同一性で `J=T` の矛盾、よって
`J≠Q`。軸 `OI` と `JT` は真に平行なので交点がない。
Tarskiの同側定理から、軸上の任意の二点は `JT` の
同側にあり、特に `(O,x)`, `(y,z)`, `(O,y)`,
`(x,z)` の四組について同側性が成立する。

第一の角定理を平行 `JO∥xT` と組 `(O,x)` に適用すると
`CongA O J Q x T Q` を得る。同様に `Jy∥zT` と
組 `(y,z)` に適用して `CongA y J Q z T Q`。
Tarski線分作図から証明済みの角腕交換でこれは
`CongA Q J y Q T z` となる。また `J,T,Q` が
共線で二点 `J,Q` と `T,Q` が異なるので、
OppositeSides の基準直線交換補題を同側性の二つの
証人に個別に適用して `SameSides J Q O y` と
`SameSides T Q x z` を得る。最後に第二の角合成定理へ
これら二つの同側性と二つの角合同を渡せば
`CongA O J y x T z` が成立する。

図式に固有な部分は以上で尽くされている。
無条件の角合同に必要なのは、明示したGeoCoqの
二つの大定理をTarskiのBet/Congから証明することだけである。
-/

theorem addGraph_included_angle_of_geoCoq_kernels_tarski
    (f : Frame Point) (x y z : AxisPoint f) (T : Point)
    (hVert : Parallel f.O f.J x.1 T)
    (hHorz : Parallel f.O f.I f.J T)
    (hDiag : Parallel f.J y.1 T z.1)
    (hParAng : ∀ (A B C D P : Point),
      Parallel A B C D → Bet A D P → D ≠ P →
      SameSides A D B C → GeoCoqCongA B A P C D P)
    (hAngOS : ∀ (A B C P A' B' C' P' : Point),
      SameSides B P A C → SameSides B' P' A' C' →
      GeoCoqCongA A B P A' B' P' →
      GeoCoqCongA P B C P' B' C' →
      GeoCoqCongA A B C A' B' C') :
    GeoCoqCongA f.O f.J y.1 x.1 T z.1 := by
  have hJT : f.J ≠ T := hHorz.2.1
  obtain ⟨Q, hJTQ, hTQcong⟩ := segment_construction f.J T f.J T
  have hTQ : T ≠ Q := by
    intro h
    have hzero : Cong f.J T T T := by
      apply cong_symm
      simpa [← h] using hTQcong
    exact hJT (cong_identity f.J T T hzero)
  have hJQ : f.J ≠ Q := by
    intro h
    have hh : Bet f.J T f.J := by simpa [← h] using hJTQ
    exact hJT (between_identity f.J T hh)
  have hDisj : ∀ S, ¬ (Col f.O f.I S ∧ Col f.J T S) :=
    playfair_strict_of_off_reference_tarski
      hHorz f.noncol (col_left f.J T)
  have hOffO : ¬ Col f.J T f.O :=
    fun hh => hDisj f.O ⟨col_left f.O f.I, hh⟩
  have hOffX : ¬ Col f.J T x.1 :=
    fun hh => hDisj x.1 ⟨x.2, hh⟩
  have hOffY : ¬ Col f.J T y.1 :=
    fun hh => hDisj y.1 ⟨y.2, hh⟩
  have hPar : Parallel f.J T f.O f.I := parallel_symm hHorz
  have hOSOx : SameSides f.J T f.O x.1 :=
    strict_parallel_sameSides_tarski hPar hOffO
      (col_left f.O f.I) x.2
  have hOSYz : SameSides f.J T y.1 z.1 :=
    strict_parallel_sameSides_tarski hPar hOffY y.2 z.2
  have hOSOy : SameSides f.J T f.O y.1 :=
    strict_parallel_sameSides_tarski hPar hOffO
      (col_left f.O f.I) y.2
  have hOSXz : SameSides f.J T x.1 z.1 :=
    strict_parallel_sameSides_tarski hPar hOffX x.2 z.2
  have hAng1 : GeoCoqCongA f.O f.J Q x.1 T Q :=
    hParAng f.J f.O x.1 T Q
      (parallel_reverse_left hVert) hJTQ hTQ hOSOx
  have hAng2raw : GeoCoqCongA y.1 f.J Q z.1 T Q :=
    hParAng f.J y.1 z.1 T Q
      (parallel_reverse_right hDiag) hJTQ hTQ hOSYz
  have hChangeJQ : ∀ U V : Point,
      OppositeSides f.J T U V ↔ OppositeSides f.J Q U V := by
    intro U V
    exact oppositeSides_change_base_iff_tarski
      hJT hJQ (col_left f.J T) (Or.inl hJTQ)
  have hChangeTQ : ∀ U V : Point,
      OppositeSides f.J T U V ↔ OppositeSides T Q U V := by
    intro U V
    exact oppositeSides_change_base_iff_tarski
      hJT hTQ (col_right f.J T) (Or.inl hJTQ)
  have hOSJQ : SameSides f.J Q f.O y.1 := by
    obtain ⟨W, hOW, hYW⟩ := hOSOy
    exact ⟨W, (hChangeJQ f.O W).mp hOW,
      (hChangeJQ y.1 W).mp hYW⟩
  have hOSTQ : SameSides T Q x.1 z.1 := by
    obtain ⟨W, hXW, hZW⟩ := hOSXz
    exact ⟨W, (hChangeTQ x.1 W).mp hXW,
      (hChangeTQ z.1 W).mp hZW⟩
  exact hAngOS f.O f.J y.1 Q x.1 T z.1 Q
    hOSJQ hOSTQ hAng1
    (geoCoqCongA_swap_arms_tarski hAng2raw)

/-!
### GeoCoq `Ch13_5.l13_14`：二つの平行四辺形の共通中点から平行を得る

**自然言語による完全証明。** 互いに交わらない非退化直線
`OA` と `O'A'` を固定し、`A,B,C` が前者に、
`A',B',C'` が後者にあるとする。さらに
`AC'∥A'C` と `BC'∥B'C` を仮定して
`AB'∥A'B` を示す。二直線が交わらないので、
一方の直線上の点は他方の直線上にない。

第1の場合 `A=C`。最初の平行条件は
`AC'∥A'A`。この二直線は `A` を共有するので一致し、
`C'` は直線 `A'A` 上にもある。`C',A'` はともに
第2基準直線上であるが、`A'A` と第2基準直線の
交点は `A'` に一意である。よって `C'=A'`。
もう一つの平行条件 `BA'∥B'A` を対称化し両線分を
反転すると結論を得る。

第2の場合 `A≠C` かつ `B=C`。同様に
`BC'∥B'B` の共有点 `B` から直線の一致を得る。
第2基準直線との交点一意性により `C'=B'`。
最初の平行条件がそのまま結論となる。

以後 `A≠C`、`B≠C`。このとき `A'≠C'`：
等しいと仮定すると `AA'∥A'C` は共有点 `A'`
を持つため一致し、`A,C,A'` が共線となる。
しかし相異なる `A,C` は第1基準直線全体を決めるので
`A'` が第1・第2両基準直線上にあり矛盾する。
同じ論法で `B'≠C'`。従って `AC` と `BC` は
第1基準直線、`A'C'` と `B'C'` は第2基準直線を
それぞれ決め、`AC∥A'C'`、`BC∥B'C'` は厳密な平行。

既証明のTarski平行四辺形対角中点構成を
四点 `(A,C,A',C')` に適用し、`AA'` と `CC'` の
共通中点 `M` を取る。次に `(B,C,B',C')` に適用し、
`BB'` と `CC'` の共通中点 `N` を取る。
どちらも同じ `CC'` の中点なのでTarski中点一意性から
`M=N`。従って `M` は `AA'` と `BB'` をともに二等分する。

第3の場合 `A=B`。この二つの中点条件は `A` の
中心 `M` に関する反転像が `A'` と `B'` の双方で
あることを示す。Tarskiの反転点一意性により `A'=B'`。
第1・第2基準直線の非交差性から `A≠A'`。
よって直線自身の平行と向きの反転により結論。

第4の場合 `A≠B`。相異なる `A,B` が第1直線を
決定し、`B'` はそこにないため `A,B,B'` は非共線。
既証明の「共通中点を持つ二対角線を持つ四辺形の対辺は
平行」を `(A,B,B',A')` に適用する。
`BA'∥B'A` が従い、線分反転と平行の対称律により
`AB'∥A'B`。以上の四場合で尽くされる。

この証明はTarski Bet/Congの既証明済みの中点構成、
直線一意性、平行関係のみを使い、Pappusそのもの、
Desarguesそのもの、加法・乗法の法則を仮定しない。
-/

theorem l13_14_tarski
    (O A B C O' A' B' C' : Point)
    (hBase : StrictParallel O A O' A')
    (hFirstB : Col O A B)
    (_hFirstBC : Col O B C)
    (hFirstC : Col O A C)
    (hSecondB : Col O' A' B')
    (_hSecondBC : Col O' B' C')
    (hSecondC : Col O' A' C')
    (hAC' : Parallel A C' A' C)
    (hBC' : Parallel B C' B' C) :
    Parallel A B' A' B := by
  classical
  rcases hBase with ⟨hOA, hO'A', hDisjoint⟩
  have hOffFirst (X : Point) (hX : Col O' A' X) :
      ¬ Col O A X := by
    intro hOnFirst
    exact hDisjoint X ⟨hOnFirst, hX⟩
  have hOffSecond (X : Point) (hX : Col O A X) :
      ¬ Col O' A' X := by
    intro hOnSecond
    exact hDisjoint X ⟨hX, hOnSecond⟩
  have hCross (X Y : Point)
      (hX : Col O A X) (hY : Col O' A' Y) : X ≠ Y := by
    intro hXY
    subst Y
    exact hDisjoint X ⟨hX, hY⟩
  by_cases hAC : A = C
  · subst C
    have hSame : ∀ X : Point,
        Col A C' X ↔ Col A' A X :=
      parallel_same_of_intersection hAC'
        (col_left A C') (col_right A' A)
    have hC'Line : Col A' A C' :=
      (hSame C').mp (col_right A C')
    have hA'neA : A' ≠ A :=
      (hCross A A' (col_right O A) (col_right O' A')).symm
    have hEq : C' = A' :=
      line_intersection_unique_tarski
        (A := O') (B := A') (C := A) (D := A')
        (P := C') (Q := A')
        (hOffSecond A (col_right O A)) hA'neA.symm
        hSecondC (col_right O' A')
        (col_swap hC'Line) (col_right A A')
    subst C'
    exact parallel_symm (parallel_reverse_both hBC')
  · by_cases hBC : B = C
    · subst C
      have hSame : ∀ X : Point,
          Col B C' X ↔ Col B' B X :=
        parallel_same_of_intersection hBC'
          (col_left B C') (col_right B' B)
      have hC'Line : Col B' B C' :=
        (hSame C').mp (col_right B C')
      have hB'neB : B' ≠ B :=
        (hCross B B' hFirstB hSecondB).symm
      have hEq : C' = B' :=
        line_intersection_unique_tarski
          (A := O') (B := A') (C := B) (D := B')
          (P := C') (Q := B')
          (hOffSecond B hFirstB) hB'neB.symm
          hSecondC hSecondB
          (col_swap hC'Line) (col_right B B')
      subst C'
      exact hAC'
    · have hLineAC : ∀ X : Point,
          Col O A X ↔ Col A C X :=
        col_line_extensionality_tarski hOA hAC
          (col_right O A) hFirstC
      have hLineBC : ∀ X : Point,
          Col O A X ↔ Col B C X :=
        col_line_extensionality_tarski hOA hBC
          hFirstB hFirstC
      have hA'C' : A' ≠ C' := by
        intro heq
        have hPar : Parallel A A' A' C := by
          simpa [heq] using hAC'
        have hSame : ∀ X : Point,
            Col A A' X ↔ Col A' C X :=
          parallel_same_of_intersection hPar
            (col_right A A') (col_left A' C)
        have hACA' : Col A C A' :=
          col_swap_last ((hSame C).mpr (col_right A' C))
        exact hOffFirst A' (col_right O' A')
          ((hLineAC A').mpr hACA')
      have hB'C' : B' ≠ C' := by
        intro heq
        have hPar : Parallel B B' B' C := by
          simpa [heq] using hBC'
        have hSame : ∀ X : Point,
            Col B B' X ↔ Col B' C X :=
          parallel_same_of_intersection hPar
            (col_right B B') (col_left B' C)
        have hBCB' : Col B C B' :=
          col_swap_last ((hSame C).mpr (col_right B' C))
        exact hOffFirst B' hSecondB
          ((hLineBC B').mpr hBCB')
      have hLineA'C' : ∀ X : Point,
          Col O' A' X ↔ Col A' C' X :=
        col_line_extensionality_tarski hO'A' hA'C'
          (col_right O' A') hSecondC
      have hLineB'C' : ∀ X : Point,
          Col O' A' X ↔ Col B' C' X :=
        col_line_extensionality_tarski hO'A' hB'C'
          hSecondB hSecondC
      have hNoncolAC : ¬ Col A C A' := by
        intro h
        exact hOffFirst A' (col_right O' A')
          ((hLineAC A').mpr h)
      have hNoncolBC : ¬ Col B C B' := by
        intro h
        exact hOffFirst B' hSecondB
          ((hLineBC B').mpr h)
      have hParAC : Parallel A C A' C' := by
        refine ⟨hAC, hA'C', Or.inr ?_⟩
        intro X hX
        exact hDisjoint X
          ⟨(hLineAC X).mpr hX.1,
            (hLineA'C' X).mpr hX.2⟩
      have hParBC : Parallel B C B' C' := by
        refine ⟨hBC, hB'C', Or.inr ?_⟩
        intro X hX
        exact hDisjoint X
          ⟨(hLineBC X).mpr hX.1,
            (hLineB'C' X).mpr hX.2⟩
      have hParCA' : Parallel C A' C' A :=
        parallel_reverse_both (parallel_symm hAC')
      have hParCB' : Parallel C B' C' B :=
        parallel_reverse_both (parallel_symm hBC')
      obtain ⟨M, hMidAA', hMidCC'⟩ :=
        parallelogram_diagonal_midpoint_exists_tarski
          (U := A) (V := C) (W := A') (Z := C')
          hNoncolAC hParAC hParCA'
      obtain ⟨N, hMidBB'N, hMidCC'N⟩ :=
        parallelogram_diagonal_midpoint_exists_tarski
          (U := B) (V := C) (W := B') (Z := C')
          hNoncolBC hParBC hParCB'
      have hMN : M = N :=
        mul_midpoint_center_unique_tarski hMidCC' hMidCC'N
      have hMidBB' : MulMidpoint M B B' := by
        simpa [← hMN] using hMidBB'N
      by_cases hAB : A = B
      · subst B
        obtain ⟨Z, _, hUnique⟩ :=
          mul_reflection_exists_unique M A
        have hEq : A' = B' :=
          (hUnique A' hMidAA').trans
            (hUnique B' hMidBB').symm
        subst B'
        have hAA' : A ≠ A' :=
          hCross A A' (col_right O A) (col_right O' A')
        exact parallel_reverse_right (parallel_refl hAA')
      · have hLineAB : ∀ X : Point,
            Col O A X ↔ Col A B X :=
          col_line_extensionality_tarski hOA hAB
            (col_right O A) hFirstB
        have hNoncolABB' : ¬ Col A B B' := by
          intro h
          exact hOffFirst B' hSecondB
            ((hLineAB B').mpr h)
        obtain ⟨_, hParLast⟩ :=
          midpoint_diagonals_parallelogram_tarski
            (B := M) (P := A) (R := B)
            (Q := B') (S := A')
            hNoncolABB' hMidBB' hMidAA'
        exact parallel_symm (parallel_reverse_both hParLast)


end TarskiField

#print axioms TarskiField.addInverseLaw_tarski
#print axioms TarskiField.addGraph_zero_iff_midpoint_tarski
#print axioms TarskiField.positiveTrichotomy_tarski
#print axioms TarskiField.positiveProper_tarski
#print axioms TarskiField.axisNegative_iff_opposite_ray_tarski
#print axioms TarskiField.axisSignTrichotomy_tarski
#print axioms TarskiField.axisNegative_ne_zero_tarski
#print axioms TarskiField.positive_not_axisNegative_tarski
#print axioms TarskiField.parallelogram_diagonal_midpoint_exists_tarski
#print axioms TarskiField.strict_parallelogram_opposite_cong_tarski
#print axioms TarskiField.axisSegmentClosed_tarski
#print axioms TarskiField.polynomial_cut_A13_internal_scalar_tarski
#print axioms TarskiField.parallelTransitivityGoal_tarski
#print axioms TarskiField.mulCommLaw_of_pappus_tarski
#print axioms TarskiField.mulAssocLaw_of_desargues_tarski
#print axioms TarskiField.geoCoqSum_first_projection_exists_tarski
#print axioms TarskiField.geoCoqSum_first_projection_strong_tarski
#print axioms TarskiField.geoCoqSum_middle_projections_exists_tarski
#print axioms TarskiField.geoCoqSum_prefix_nonzero_tarski
#print axioms TarskiField.geoCoqSum_first_projection_unique_tarski
#print axioms TarskiField.geoCoqSum_middle_projections_unique_tarski
#print axioms TarskiField.geoCoqSum_one_first_projection_tarski
#print axioms TarskiField.addGraph_one_one_iff_geoCoqSum_tarski
#print axioms TarskiField.tarski_perp2_sym_tarski
#print axioms TarskiField.parallel_retarget_right_of_line_extensionality_tarski
#print axioms TarskiField.addGraph_left_zero_iff_geoCoqSum_tarski
#print axioms TarskiField.addGraph_right_zero_iff_geoCoqSum_tarski
#print axioms TarskiField.addGraph_strong_opposite_cong_tarski
#print axioms TarskiField.diagonal_midpoints_fourth_vertex_unique_tarski
#print axioms TarskiField.geoCoqCongA_refl_tarski
#print axioms TarskiField.geoCoqCongA_symm_tarski
#print axioms TarskiField.geoCoqCongA_swap_arms_tarski
#print axioms TarskiField.geoCoqCongA_sas_tarski
#print axioms TarskiField.geoCoqCongA_pseudo_refl_tarski
#print axioms TarskiField.addGraph_strong_second_opposite_cong_of_angle_tarski
#print axioms TarskiField.add_two_station_output_unique_tarski
#print axioms TarskiField.addGraph_strong_target_ne_input_tarski
#print axioms TarskiField.addCommLaw_of_strong_angle_tarski
#print axioms TarskiField.addGraph_included_angle_of_geoCoq_kernels_tarski
#print axioms TarskiField.l13_14_tarski








/-!
## Synthetic order core: nonzero translation has no fixed point

This proof uses only the primitive Tarski geometry through the established
theorems about Playfair parallelism and uniqueness of line intersection.
It assumes neither an additive group nor an ordered field.

**Complete geometric proof.** Suppose the constructed sum x+d equals x.
If x is O, the zero-first-operand clause of AddGraph makes d=x=O.
Otherwise AddGraph supplies a point T satisfying OJ parallel xT and
Jd parallel Tx. Reverse the defining endpoints to obtain xT parallel Jd.
Transitivity of parallelism (proved from Tarski's Euclidean postulate)
gives OJ parallel Jd. These lines both contain J, so the parallel
coincidence lemma identifies their sets of points. Since d is on Jd,
it is on OJ. By its type as an axis scalar, d is also on OI, and the
distinct axes meet only at O. Hence d=O. Conversely, the already proved
geometric right-zero construction gives x+O=x.

The order relation AxisLt x y asserts a positive geometric displacement
d with x+d=y. Consequently AxisLt x x is impossible: the preceding theorem
makes d=O, whereas Positive excludes O.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- A geometrically constructed translation fixes an axis point exactly
when its displacement is O. No group cancellation is assumed. -/
theorem addGraph_fixed_point_iff_zero_tarski
    (f : Frame Point) (x d : AxisPoint f) :
    AddGraph f x d x ↔ d = axisZero f := by
  constructor
  · intro h
    rcases h with ⟨hxO, hxD⟩ | ⟨_, T, hOJ_xT, _, hJd_Tx⟩
    · exact hxD.symm.trans (Subtype.ext hxO)
    · have h_xT_Jd : Parallel x.1 T f.J d.1 :=
        parallel_reverse_left (parallel_symm hJd_Tx)
      have h_OJ_Jd : Parallel f.O f.J f.J d.1 :=
        parallel_trans_of_playfair tarski_playfair hOJ_xT h_xT_Jd
      have h_lines : ∀ P : Point, Col f.O f.J P ↔ Col f.J d.1 P :=
        parallel_same_of_intersection h_OJ_Jd
          (col_right f.O f.J) (col_left f.J d.1)
      have hdOJ : Col f.O f.J d.1 :=
        (h_lines d.1).mpr (col_right f.J d.1)
      exact Subtype.ext
        (frame_axes_intersection_only_origin_tarski f d.1 d.2 hdOJ)
  · intro hd
    rw [hd]
    exact add_zero_right_tarski f x

/-- Strict order induced by the constructed positive displacement
is irreflexive, before associativity or any field law is available. -/
theorem axisLt_irrefl_tarski
    (f : Frame Point) (x : AxisPoint f) : ¬ AxisLt f x x := by
  rintro ⟨d, hAdd, hPos⟩
  have hd : d = axisZero f :=
    (addGraph_fixed_point_iff_zero_tarski f x d).mp hAdd
  have hdO : d.1 = f.O := congrArg Subtype.val hd
  exact hPos.2.1 hdO

/-- A positive geometric translation always changes its axis point. -/
theorem axisLt_ne_tarski
    (f : Frame Point) {x y : AxisPoint f}
    (h : AxisLt f x y) : x ≠ y := by
  intro hxy
  subst y
  exact axisLt_irrefl_tarski f x h

#print axioms TarskiField.addGraph_fixed_point_iff_zero_tarski
#print axioms TarskiField.axisLt_irrefl_tarski
#print axioms TarskiField.axisLt_ne_tarski

end TarskiField


/-!
## Synthetic right cancellation for geometric addition

**Complete point-geometry argument.** Assume AddGraph x d z and AddGraph x e z.
When x=O the zero clause forces d=z=e. Otherwise the two constructions
have auxiliary points T,U. Both lines JT and JU are parallel to OI, meet
at J, and therefore coincide by the Tarski-proved Playfair theorem.
Both xT and xU are parallel to OJ; their common point x and the
transversality of the horizontal line JT force T=U, by the previously
proved directional-projection uniqueness theorem. Thus the last two
construction lines Jd and Je are parallel to the *same* line Tz,
and meet at J. Playfair makes Jd and Je the same line. Hence e is
collinear with J,d. As d and e both lie on OI and J lies outside OI,
uniqueness of intersection of the distinct lines OI and Jd forces d=e.
This invokes no addition associativity, no numerical coordinates and
no field cancellation law.

Combined with the previously proved functionality in the *output*
argument, this gives injectivity separately in the output and second
input of the ternary addition graph, prior to commutativity.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Geometric right cancellation: the displacement is determined by its
source and target. This is proved directly from the two projection lines,
not from a group cancellation axiom. -/
theorem addGraph_right_cancel_tarski
    (f : Frame Point) (x d e z : AxisPoint f)
    (hxd : AddGraph f x d z)
    (hxe : AddGraph f x e z) : d = e := by
  by_cases hx : x = axisZero f
  · subst x
    exact (add_zero_left_unique f d z hxd).symm.trans
      (add_zero_left_unique f e z hxe)
  · obtain ⟨T, hVertT, hHorzT, hLastD⟩ :=
      (addGraph_nonzero_iff f x d z hx).mp hxd
    obtain ⟨U, hVertU, hHorzU, hLastE⟩ :=
      (addGraph_nonzero_iff f x e z hx).mp hxe
    have hSameHorz : ∀ P : Point,
        Col f.J T P ↔ Col f.J U P :=
      tarski_playfair f.O f.I f.J T f.J U f.J
        hHorzT hHorzU (col_left f.J T) (col_left f.J U)
    have hU_on_JT : Col f.J T U :=
      (hSameHorz U).mpr (col_right f.J U)
    have hx_off_JT : ¬ Col f.J T x.1 := by
      intro hxJT
      exact (parallel_off_line_disjoint hHorzT f.noncol hxJT) x.2
    have hLine : ∀ A B C D : Point,
        A ≠ B → C ≠ D →
        Col A B C → Col A B D →
        ∀ S : Point, Col A B S ↔ Col C D S := by
      intro A B C D hAB hCD hC hD S
      exact col_line_extensionality_tarski hAB hCD hC hD S
    have hTU : T = U :=
      directional_projection_unique_of_playfair
        tarski_playfair hLine
        f.J T f.O f.J x.1 T U
        hHorzT.2.1 hx_off_JT
        (col_right f.J T) hU_on_JT hVertT hVertU
    subst U
    have hSameLast : ∀ P : Point,
        Col f.J d.1 P ↔ Col f.J e.1 P :=
      tarski_playfair T z.1 f.J d.1 f.J e.1 f.J
        (parallel_symm hLastD) (parallel_symm hLastE)
        (col_left f.J d.1) (col_left f.J e.1)
    have heOnJd : Col f.J d.1 e.1 :=
      (hSameLast e.1).mpr (col_right f.J e.1)
    have hJd : f.J ≠ d.1 := f.J_ne_axis_point d.1 d.2
    have hde : d.1 = e.1 :=
      line_intersection_unique_tarski f.noncol hJd
        d.2 e.2 (col_right f.J d.1) heOnJd
    exact Subtype.ext hde

/-- For each fixed first operand, geometric addition is one-to-one on
the displacement argument: no additive group law is required. -/
theorem addGraph_second_functional_tarski
    (f : Frame Point) (x y z u v : AxisPoint f)
    (hy : AddGraph f x y u)
    (hz : AddGraph f x z v)
    (huv : u = v) : y = z := by
  subst v
  exact addGraph_right_cancel_tarski f x y z u hy hz

/-- A geometric addition graph cannot have a positive nonzero displacement
if its input and output are equal. -/
theorem addGraph_positive_displacement_changes_point_tarski
    (f : Frame Point) (x d y : AxisPoint f)
    (hd : Positive f d) (hxy : AddGraph f x d y) : x ≠ y := by
  intro h
  subst y
  have hzero : d = axisZero f :=
    (addGraph_fixed_point_iff_zero_tarski f x d).mp hxy
  exact hd.2.1 (congrArg Subtype.val hzero)

#print axioms TarskiField.addGraph_right_cancel_tarski
#print axioms TarskiField.addGraph_second_functional_tarski
#print axioms TarskiField.addGraph_positive_displacement_changes_point_tarski

end TarskiField


/-!
## Every ordered pair of scalars has exactly one additive displacement

The existence direction is a nontrivial *synthetic geometric construction*,
not a rearrangement using an assumed additive inverse or field structure.

**Complete geometric proof.** Let x,y be points on OI. If x=O, take
the displacement y. Otherwise, first construct T as the intersection
of the line through x parallel to OJ and the line through J parallel
to OI, using the already derived midpoint-parallelogram theorem.
T is not on OI: it is on the line JT parallel to OI, and J is off
the axis. Therefore T≠y.

The line Ty is transverse to OI: otherwise, since it meets OI at y,
the definition of Tarski parallelism forces Ty and OI to coincide.
That would put T on OI, contrary to the preceding paragraph.
Through J construct a line JW parallel to Ty (Tarski's Euclidean
parallel existence theorem). Since Ty is not parallel to OI, JW is
not parallel to OI, by transitivity of parallelism. Thus JW meets
OI at some point D, by classical elimination of the definition of
nonparallel lines. J and D are distinct since J is off OI. The
two-point line-extensionality theorem identifies JW with JD, so
the same parallel construction gives JD parallel Ty. We have
therefore built the exact AddGraph witness T for x+D=y.
For uniqueness, apply the already proved synthetic
addGraph_right_cancel_tarski, which uses Playfair and intersection
uniqueness. This proves the existence and uniqueness of D for
*every* x,y, including zero and all degenerate cases.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- The synthetic additive displacement taking x to y exists and is unique,
even before commutativity or associativity of addition is established. -/
theorem addGraph_displacement_existsUnique_tarski
    (f : Frame Point) (x y : AxisPoint f) :
    ∃! d : AxisPoint f, AddGraph f x d y := by
  by_cases hx : x = axisZero f
  · subst x
    refine ⟨y, add_zero_left f y, ?_⟩
    intro d hd
    exact (add_zero_left_unique f d y hd).symm
  · have hxO : x.1 ≠ f.O := by
      intro h
      exact hx (Subtype.ext h)
    obtain ⟨T, hVert, hHorz⟩ :=
      add_first_projection_exists_tarski f x hxO
    have hTOff : ¬ Col f.O f.I T :=
      parallel_off_line_disjoint hHorz f.noncol
        (col_right f.J T)
    have hTy : T ≠ y.1 := by
      intro h
      exact hTOff (by simpa [h] using y.2)
    have hnpar : ¬ Parallel T y.1 f.O f.I := by
      intro hpar
      have hSame : ∀ S : Point, Col T y.1 S ↔ Col f.O f.I S :=
        parallel_same_of_intersection hpar
          (col_right T y.1) y.2
      exact hTOff ((hSame T).mp (col_left T y.1))
    have hThrough : ∀ A B P : Point,
        A ≠ B → ∃ W : Point, Parallel A B P W := by
      intro A B P hAB
      exact parallel_through_any_point_tarski
        (A := A) (B := B) (P := P) hAB
    have hTrans : ∀ {A B C D E F : Point},
        Parallel A B C D → Parallel C D E F → Parallel A B E F := by
      intro A B C D E F hAB hCD
      exact parallel_trans_of_playfair tarski_playfair hAB hCD
    obtain ⟨D, hDAxis, W, hJParallel, hJWD⟩ :=
      weak_directional_projection_exists hThrough hTrans
        f.O f.I T y.1 f.J f.O_ne_I hTy hnpar
    have hJD : f.J ≠ D :=
      f.J_ne_axis_point D hDAxis
    have hLine : ∀ S : Point, Col f.J W S ↔ Col f.J D S :=
      col_line_extensionality_tarski
        hJParallel.2.1 hJD (col_left f.J W) hJWD
    have hJDTy : Parallel f.J D T y.1 :=
      parallel_symm
        (parallel_retarget_right_of_line_eq
          hJParallel hJD hLine)
    let d : AxisPoint f := ⟨D, hDAxis⟩
    have hd : AddGraph f x d y :=
      Or.inr ⟨hxO, T, hVert, hHorz, hJDTy⟩
    refine ⟨d, hd, ?_⟩
    intro e he
    exact addGraph_right_cancel_tarski f x e d y he hd

/-- AddGraph's displacement vanishes if and only if input and output
coincide; the converse uses only already established output-functionality. -/
theorem addGraph_displacement_nonzero_iff_distinct_tarski
    (f : Frame Point) (x d y : AxisPoint f)
    (hAdd : AddGraph f x d y) :
    d ≠ axisZero f ↔ x ≠ y := by
  constructor
  · intro hd hxy
    subst y
    exact hd ((addGraph_fixed_point_iff_zero_tarski f x d).mp hAdd)
  · intro hxy hd
    subst d
    have hRightZero : AddGraph f x (axisZero f) x :=
      add_zero_right_tarski f x
    have hFunc : AddFunctional f :=
      (operation_graphs_functional_tarski f).1
    exact hxy (hFunc x (axisZero f) y x hAdd hRightZero).symm

#print axioms TarskiField.addGraph_displacement_existsUnique_tarski
#print axioms TarskiField.addGraph_displacement_nonzero_iff_distinct_tarski

end TarskiField


/-!
## Difference and order internal to the original Tarski point sort

Every ordered pair (x,y) of existing axis points determines one
constructed displacement d, with AddGraph f x d y. This uses the
previous **geometric** theorem; it is not an existing group subtraction.

Choose that unique d by classical definite description and denote it
by axisDisplacementOf f x y. Since the graph determines d uniquely,
every witness is propositionally equal to this choice. The difference
between identical points is O, because the right-zero construction
gives AddGraph f x O x. The difference from O to y is y, because the
zero-left construction gives AddGraph f O y y.

The original strict-order formula AxisLt f x y explicitly asserts
the *existence* of a positive displacement d from x to y. Its
witness is necessarily the unique axisDisplacementOf f x y.
Therefore the original (first-order) relation is equivalent to
positivity of the unique geometric difference. From the proven
no-fixed-point theorem, this difference is nonzero exactly when
x and y are different points. Thus there is still no imported
ordered field and no numerical coordinate subtraction; the order
is a property of synthetic point constructions.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Geometric difference: the unique Tarski-constructed displacement from
x to y, before an additive group structure has been established. -/
noncomputable def axisDisplacementOf
    (f : Frame Point) (x y : AxisPoint f) : AxisPoint f :=
  Classical.choose (addGraph_displacement_existsUnique_tarski f x y)

/-- The selected displacement satisfies the original geometric graph. -/
theorem axisDisplacementOf_spec
    (f : Frame Point) (x y : AxisPoint f) :
    AddGraph f x (axisDisplacementOf f x y) y :=
  (Classical.choose_spec
    (addGraph_displacement_existsUnique_tarski f x y)).1

/-- Any displacement realizing a geometric translation equals the chosen
one; no algebraic subtraction is postulated. -/
theorem axisDisplacementOf_eq_of_graph
    (f : Frame Point) (x y d : AxisPoint f)
    (hd : AddGraph f x d y) :
    axisDisplacementOf f x y = d :=
  ((Classical.choose_spec
    (addGraph_displacement_existsUnique_tarski f x y)).2 d hd).symm

theorem axisDisplacementOf_self_tarski
    (f : Frame Point) (x : AxisPoint f) :
    axisDisplacementOf f x x = axisZero f :=
  axisDisplacementOf_eq_of_graph f x x (axisZero f)
    (add_zero_right_tarski f x)

theorem axisDisplacementOf_zero_left_tarski
    (f : Frame Point) (y : AxisPoint f) :
    axisDisplacementOf f (axisZero f) y = y :=
  axisDisplacementOf_eq_of_graph f (axisZero f) y y
    (add_zero_left f y)

/-- The internal difference vanishes exactly for coincident points. -/
theorem axisDisplacementOf_eq_zero_iff_tarski
    (f : Frame Point) (x y : AxisPoint f) :
    axisDisplacementOf f x y = axisZero f ↔ x = y := by
  constructor
  · intro hd
    have hGraph : AddGraph f x (axisZero f) y := by
      simpa only [hd] using axisDisplacementOf_spec f x y
    have hZero : AddGraph f x (axisZero f) x :=
      add_zero_right_tarski f x
    exact (operation_graphs_functional_tarski f).1
      x (axisZero f) y x hGraph hZero |>.symm
  · intro hxy
    subst y
    exact axisDisplacementOf_self_tarski f x

/-- Strict order is exactly positivity of the unique geometrically
constructed difference; no independent order relation is inserted. -/
theorem axisLt_iff_axisDisplacementOf_positive_tarski
    (f : Frame Point) (x y : AxisPoint f) :
    AxisLt f x y ↔ Positive f (axisDisplacementOf f x y) := by
  constructor
  · rintro ⟨d, hd, hpositive⟩
    have hchoice : axisDisplacementOf f x y = d :=
      axisDisplacementOf_eq_of_graph f x y d hd
    simpa only [hchoice] using hpositive
  · intro hpositive
    exact ⟨axisDisplacementOf f x y,
      axisDisplacementOf_spec f x y, hpositive⟩

/-- The original order agrees with the positive ray when its lower
endpoint is O. -/
theorem axisLt_zero_iff_positive_tarski
    (f : Frame Point) (x : AxisPoint f) :
    AxisLt f (axisZero f) x ↔ Positive f x := by
  rw [axisLt_iff_axisDisplacementOf_positive_tarski,
    axisDisplacementOf_zero_left_tarski]

/-- The internally defined non-strict relation can be read directly
through the synthetic displacement and its oriented ray. -/
theorem axisLe_iff_eq_or_positive_displacement_tarski
    (f : Frame Point) (x y : AxisPoint f) :
    AxisLe f x y ↔ x = y ∨ Positive f (axisDisplacementOf f x y) := by
  exact or_congr Iff.rfl
    (axisLt_iff_axisDisplacementOf_positive_tarski f x y)

#print axioms TarskiField.axisDisplacementOf_spec
#print axioms TarskiField.axisDisplacementOf_eq_zero_iff_tarski
#print axioms TarskiField.axisLt_iff_axisDisplacementOf_positive_tarski
#print axioms TarskiField.axisLt_zero_iff_positive_tarski

end TarskiField


/-!
## Geometric translations are bijections, before the field laws

Fix an origin scalar x. The previously proved AddTotal produces, for
each displacement d, a unique target y with AddGraph f x d y.
Call this operation T_x(d). By the pure Tarski line-intersection
argument addGraph_right_cancel_tarski, T_x is injective:
if T_x(d)=T_x(e), both graphs have the same x and target, hence d=e.
By addGraph_displacement_existsUnique_tarski, T_x is also surjective:
for every target y, construct the unique geometric displacement
D_x(y) and use its AddGraph proof to obtain T_x(D_x(y))=y.
The original graph's uniqueness also gives D_x(T_x(d))=d.
Therefore T_x and D_x are inverse permutations of the actual axis
points. This is a *torsor-like translation fact* obtained before
commutativity, associativity, a field, or even additive inverses as
algebraic operations are available.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Geometric addition by a fixed first scalar is a bijection in its second
argument; uniqueness and surjectivity come from two different synthetic
projection constructions. -/
theorem axisAddOf_left_translation_bijective_tarski
    (f : Frame Point) (hAdd : AddTotal f) (x : AxisPoint f) :
    Function.Bijective (fun d : AxisPoint f => axisAddOf f hAdd x d) := by
  constructor
  · intro d e h
    have hd : AddGraph f x d (axisAddOf f hAdd x d) :=
      axisAddOf_spec f hAdd x d
    have he : AddGraph f x e (axisAddOf f hAdd x e) :=
      axisAddOf_spec f hAdd x e
    change axisAddOf f hAdd x d = axisAddOf f hAdd x e at h
    rw [← h] at he
    exact addGraph_right_cancel_tarski
      f x d e (axisAddOf f hAdd x d) hd he
  · intro y
    obtain ⟨d, hd, _⟩ := addGraph_displacement_existsUnique_tarski f x y
    exact ⟨d, (addGraph_iff_axisAddOf_eq f hAdd x d y).mp hd⟩

/-- Forward followed by reverse geometric translation gives the target,
without invoking subtraction from any ambient group. -/
theorem axisAddOf_axisDisplacementOf_tarski
    (f : Frame Point) (hAdd : AddTotal f)
    (x y : AxisPoint f) :
    axisAddOf f hAdd x (axisDisplacementOf f x y) = y :=
  (addGraph_iff_axisAddOf_eq f hAdd x
    (axisDisplacementOf f x y) y).mp
    (axisDisplacementOf_spec f x y)

/-- Reverse followed by forward geometric translation recovers the unique
displacement. -/
theorem axisDisplacementOf_axisAddOf_tarski
    (f : Frame Point) (hAdd : AddTotal f)
    (x d : AxisPoint f) :
    axisDisplacementOf f x (axisAddOf f hAdd x d) = d :=
  axisDisplacementOf_eq_of_graph f x (axisAddOf f hAdd x d) d
    (axisAddOf_spec f hAdd x d)

/-- Specialization: bijective translations are consequences purely of the
Tarski plane axioms, with no unproved hAdd parameter. -/
theorem axisTranslation_bijective_tarski
    (f : Frame Point) (x : AxisPoint f) :
    Function.Bijective
      (fun d : AxisPoint f =>
        axisAddOf f (operation_graphs_total_tarski f).1 x d) :=
  axisAddOf_left_translation_bijective_tarski
    f (operation_graphs_total_tarski f).1 x

#print axioms TarskiField.axisAddOf_left_translation_bijective_tarski
#print axioms TarskiField.axisAddOf_axisDisplacementOf_tarski
#print axioms TarskiField.axisDisplacementOf_axisAddOf_tarski
#print axioms TarskiField.axisTranslation_bijective_tarski

end TarskiField


/-!
## Formal boundary argument for A13's polynomial prefix

This is a pure ordered-field theorem, intended to be instantiated *only
after* the constructed geometric axis has been proved an ordered field.
It imports neither real-number completeness nor analytic continuity.

The hypotheses hLocalPos and hLocalNeg are exact algebraic estimates
established for finite polynomials by factorization
p(X)-p(b)=(X-b)q_b(X), the finite coefficient bound, and the explicit
delta described in proofs/RealClosedAxis_A13_IVT_full_proof.md.
The least-upper-bound hypotheses are to be supplied by the *single*
first-order Tarski A13 instance for the corresponding polynomial cut.

**Complete proof of strict cut witness.** Since p(L)<0, local sign
persistence supplies delta>0 so p(t)<0 on |t-L|<delta. Choose
epsilon=min(delta,R-L)>0 and x=L+epsilon/2. For every t in [L,x],
0<=t-L<=epsilon/2<delta, so p(t)<0. Thus x is in the prefix,
and L<x<R.

**Complete proof of root at the least upper bound b.** The strict cut
witness forces b>L. If p(b)>0, local positivity gives a positive point
y=b-min(delta,b-L)/2 lying strictly between L and b. Since any prefix
point x>=y would force p(y)<0, y is an upper bound, contradicting
the minimality of b. If p(b)<0, b<R since p(R)>0. Local negativity
gives z=b+min(delta,R-b)/2 with b<z<R and p(t)<0 on [b,z].
For t in [L,b), the least-upper-bound property means t is *not* an
upper bound, so a prefix point x>t exists and yields p(t)<0.
Combining these two intervals proves z is in the prefix; this
contradicts that b bounds all prefix points. Therefore p(b)=0.
-/

namespace TarskiField

section AbstractFiniteAlgebraicCut

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- A locally negative polynomial at the left endpoint gives an actual
strictly interior point of the definable negative prefix. No Archimedean
principle is involved in the witness construction. -/
theorem ordered_negative_prefix_strict_witness_of_local_sign
    (p : F → F) (L R : F)
    (hLR : L < R) (hpL : p L < 0)
    (hLocalNeg : ∀ b : F, p b < 0 →
      ∃ δ : F, 0 < δ ∧ ∀ t : F, |t - b| < δ → p t < 0) :
    ∃ x : F, OrderedNegativePrefix p L R x ∧ L < x := by
  obtain ⟨δ, hδpos, hδ⟩ := hLocalNeg L hpL
  let ε : F := min δ (R - L)
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min hδpos (sub_pos.mpr hLR)
  have hεR : ε ≤ R - L := min_le_right δ (R - L)
  have hεδ : ε ≤ δ := min_le_left δ (R - L)
  let x : F := L + ε / 2
  refine ⟨x, ⟨?_, ?_, ?_⟩, ?_⟩
  · dsimp [x]
    linarith
  · dsimp [x]
    linarith
  · intro t htL htx
    apply hδ t
    have htBound : t - L ≤ ε / 2 := by
      dsimp [x] at htx
      linarith
    have hAbs : |t - L| = t - L :=
      abs_of_nonneg (sub_nonneg.mpr htL)
    rw [hAbs]
    linarith
  · dsimp [x]
    linarith

/-- Definable-prefix least-upper-boundedness and algebraic sign
persistence imply an exact zero at the boundary. This is the complete
two-sided local argument, with positive strict witnesses constructed
explicitly rather than postulated as independent hypotheses. -/
theorem ordered_negative_prefix_cut_zero_of_local_sign
    (p : F → F) (L R b : F)
    (hLR : L < R)
    (hpL : p L < 0) (hpR : 0 < p R)
    (hsegment : L ≤ b ∧ b ≤ R)
    (hbound : ∀ x : F, OrderedNegativePrefix p L R x → x ≤ b)
    (hleast : ∀ y : F,
      (∀ x : F, OrderedNegativePrefix p L R x → x ≤ y) → b ≤ y)
    (hLocalPos : ∀ c : F, 0 < p c →
      ∃ δ : F, 0 < δ ∧ ∀ t : F, |t - c| < δ → 0 < p t)
    (hLocalNeg : ∀ c : F, p c < 0 →
      ∃ δ : F, 0 < δ ∧ ∀ t : F, |t - c| < δ → p t < 0) :
    p b = 0 := by
  obtain ⟨x₀, hx₀, hLx₀⟩ :=
    ordered_negative_prefix_strict_witness_of_local_sign
      p L R hLR hpL hLocalNeg
  have hLb : L < b := lt_of_lt_of_le hLx₀ (hbound x₀ hx₀)
  have hPositiveLeft : 0 < p b →
      ∃ y : F, L ≤ y ∧ y < b ∧ 0 < p y := by
    intro hpb
    obtain ⟨δ, hδpos, hδ⟩ := hLocalPos b hpb
    let ε : F := min δ (b - L)
    have hεpos : 0 < ε := by
      dsimp [ε]
      exact lt_min hδpos (sub_pos.mpr hLb)
    have hεbL : ε ≤ b - L := min_le_right δ (b - L)
    have hεδ : ε ≤ δ := min_le_left δ (b - L)
    let y : F := b - ε / 2
    refine ⟨y, ?_, ?_, ?_⟩
    · dsimp [y]
      linarith
    · dsimp [y]
      linarith
    · apply hδ y
      have hyb : y - b = -(ε / 2) := by
        dsimp [y]
        ring
      have hnonneg : 0 ≤ ε / 2 := by positivity
      rw [hyb, abs_neg, abs_of_nonneg hnonneg]
      linarith
  have hNegativeRight : p b < 0 →
      ∃ z : F, b < z ∧ z ≤ R ∧
        ∀ t : F, b ≤ t → t ≤ z → p t < 0 := by
    intro hpb
    have hbR : b < R := by
      rcases lt_or_eq_of_le hsegment.2 with h | h
      · exact h
      · rw [← h] at hpR
        linarith
    obtain ⟨δ, hδpos, hδ⟩ := hLocalNeg b hpb
    let ε : F := min δ (R - b)
    have hεpos : 0 < ε := by
      dsimp [ε]
      exact lt_min hδpos (sub_pos.mpr hbR)
    have hεRb : ε ≤ R - b := min_le_right δ (R - b)
    have hεδ : ε ≤ δ := min_le_left δ (R - b)
    let z : F := b + ε / 2
    refine ⟨z, ?_, ?_, ?_⟩
    · dsimp [z]
      linarith
    · dsimp [z]
      linarith
    · intro t hbt htz
      apply hδ t
      have htzBound : t - b ≤ ε / 2 := by
        dsimp [z] at htz
        linarith
      have hAbs : |t - b| = t - b :=
        abs_of_nonneg (sub_nonneg.mpr hbt)
      rw [hAbs]
      linarith
  exact ordered_negative_prefix_cut_value_zero
    p L R b hsegment hbound hleast hPositiveLeft hNegativeRight

#print axioms TarskiField.ordered_negative_prefix_strict_witness_of_local_sign
#print axioms TarskiField.ordered_negative_prefix_cut_zero_of_local_sign

end AbstractFiniteAlgebraicCut

end TarskiField


/-!
## Geometric negation is central reflection and an involution

Define -x without a field as the unique displacement carrying x to O.
The already established equivalence
AddGraph f x y O iff MulMidpoint O x y
identifies this operation with central reflection about O.
Reversing the midpoint condition gives
MulMidpoint O (-x) x, hence AddGraph f (-x) x O.
Uniqueness of the displacement from -x to O forces -(-x)=x.

In particular negation is a bijection of the existing axis points,
and it preserves the distance from O by midpoint congruence.
A fixed point of this reflection satisfies Bet x O x, so Tarski's
between-identity axiom forces x=O; conversely O is fixed.
Likewise x+x=O forces MulMidpoint O x x and hence x=O.
No commutative group, associativity, field, or external coordinates
are assumed anywhere in these conclusions.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- The internally constructed additive opposite is *defined* as the
unique geometric displacement taking x to O, not an algebraic Neg instance. -/
noncomputable def axisNegOf
    (f : Frame Point) (x : AxisPoint f) : AxisPoint f :=
  axisDisplacementOf f x (axisZero f)

theorem axisNegOf_spec_tarski
    (f : Frame Point) (x : AxisPoint f) :
    AddGraph f x (axisNegOf f x) (axisZero f) :=
  axisDisplacementOf_spec f x (axisZero f)

/-- Geometric negation is literally the Tarski midpoint reflection at O. -/
theorem axisNegOf_midpoint_tarski
    (f : Frame Point) (x : AxisPoint f) :
    MulMidpoint f.O x.1 (axisNegOf f x).1 :=
  (addGraph_zero_iff_midpoint_tarski f x (axisNegOf f x)).mp
    (axisNegOf_spec_tarski f x)

/-- Double reflection is the identity, before any additive-group law. -/
theorem axisNegOf_involutive_tarski
    (f : Frame Point) (x : AxisPoint f) :
    axisNegOf f (axisNegOf f x) = x := by
  have hMid : MulMidpoint f.O (axisNegOf f x).1 x.1 :=
    mul_midpoint_reverse (axisNegOf_midpoint_tarski f x)
  exact axisDisplacementOf_eq_of_graph
    f (axisNegOf f x) (axisZero f) x
    ((addGraph_zero_iff_midpoint_tarski f (axisNegOf f x) x).mpr hMid)

/-- Reflection preserves origin-to-point segment congruence. -/
theorem axisNegOf_origin_congr_tarski
    (f : Frame Point) (x : AxisPoint f) :
    Cong f.O x.1 f.O (axisNegOf f x).1 :=
  (axisNegOf_midpoint_tarski f x).2

/-- The origin is the only fixed point of geometric negation. -/
theorem axisNegOf_fixed_point_iff_zero_tarski
    (f : Frame Point) (x : AxisPoint f) :
    axisNegOf f x = x ↔ x = axisZero f := by
  constructor
  · intro h
    have hMid : MulMidpoint f.O x.1 x.1 := by
      simpa only [h] using axisNegOf_midpoint_tarski f x
    exact Subtype.ext (between_identity x.1 f.O hMid.1)
  · intro hx
    subst x
    exact axisDisplacementOf_self_tarski f (axisZero f)

/-- The origin is the only point with geometric double equal to zero. -/
theorem addGraph_double_eq_zero_iff_zero_tarski
    (f : Frame Point) (x : AxisPoint f) :
    AddGraph f x x (axisZero f) ↔ x = axisZero f := by
  constructor
  · intro h
    have hMid : MulMidpoint f.O x.1 x.1 :=
      (addGraph_zero_iff_midpoint_tarski f x x).mp h
    exact Subtype.ext (between_identity x.1 f.O hMid.1)
  · intro hx
    subst x
    exact add_zero_left f (axisZero f)

/-- Involution gives a bijection of the existing axis-point carrier. -/
theorem axisNegOf_bijective_tarski
    (f : Frame Point) :
    Function.Bijective (axisNegOf f) := by
  constructor
  · intro x y h
    have h' := congrArg (axisNegOf f) h
    simpa only [axisNegOf_involutive_tarski] using h'
  · intro y
    exact ⟨axisNegOf f y, axisNegOf_involutive_tarski f y⟩

#print axioms TarskiField.axisNegOf_spec_tarski
#print axioms TarskiField.axisNegOf_midpoint_tarski
#print axioms TarskiField.axisNegOf_involutive_tarski
#print axioms TarskiField.axisNegOf_fixed_point_iff_zero_tarski
#print axioms TarskiField.addGraph_double_eq_zero_iff_zero_tarski
#print axioms TarskiField.axisNegOf_bijective_tarski

end TarskiField


/-!
## Formal degeneracy audit for GeoCoq's sum-by-congruence shortcut

A pair of unoriented segment congruences is not sufficient to select
the desired geometric sum. At the frame's unit I one has Cong O I I O
by the *primitive* congruence symmetry axiom, yet I+I cannot be O:
I lies on the positive ray and positiveProper_tarski excludes two
positive summands with sum O. This is a coordinate-free counterexample
inside every model of the Tarski plane axioms. Any attempt to port
GeoCoq's sum_iff_cong theorem must retain its nondegeneracy guard
(O != output or first argument != second argument), or explicitly
handle the exceptional cases.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- The naive equivalence between geometric sum and two opposite-side
segment congruences has a concrete counterexample in *every* Tarski frame.
This justifies GeoCoq's degenerate-case guard. -/
theorem naive_sum_congruence_pair_counterexample_tarski
    (f : Frame Point) :
    (Cong f.O f.I f.I f.O ∧ Cong f.O f.I f.I f.O) ∧
    ¬ AddGraph f (axisOne f) (axisOne f) (axisZero f) := by
  refine ⟨⟨cong_pseudo_reflexivity f.O f.I,
    cong_pseudo_reflexivity f.O f.I⟩, ?_⟩
  intro hAdd
  exact positiveProper_tarski f (axisOne f) (axisOne f)
    (axisOne_positive f) (axisOne_positive f) hAdd

#print axioms TarskiField.naive_sum_congruence_pair_counterexample_tarski

end TarskiField


/-!
## The geometric finite-Horner map on the existing scalar axis

The relational theorem hornerGraph_exists_unique already proves that each
HornerGraph has one and only one output, using the Tarski-derived
geometric existence and uniqueness of AddGraph and MulGraph.
This section constructs an explicit recursive *function* on actual
axis points without assuming a field or using polynomial arithmetic.

Set H_x([])=O and H_x(a::rest)=Add(a,Mul(x,H_x(rest))). The addition
and multiplication in this recurrence are the already proved
geometric parallel-projection operations, not field instances.
For the empty list, the relational HornerGraph has output O by its
definition. In the cons case, the induction hypothesis provides the
previous relational value t. The totality theorem gives a unique
geometric multiplication witness u=x*t, followed by a unique
geometric addition witness z=a+u. These witnesses satisfy the
precise cons clause of HornerGraph. For uniqueness, invoke
hornerGraph_exists_unique, whose proof recursively uses the same
geometric graph functionality. Consequently the constructed
finite-Horner function is equivalent to the original relational
HornerGraph at every finite coefficient list.

All cases of the coefficient list are exhausted by [] and a::rest.
No additive associativity, commutativity, distributivity,
ordered field, continuity, external real coordinate system, or
new Tarski-plane axioms occur in this argument.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]

/-- Recursion using only the internally constructed geometric arithmetic
operations (not an imported field instance). -/
noncomputable def axisHornerOf
    (f : Frame Point) (hAdd : AddTotal f) (hMul : MulTotal f)
    (x : AxisPoint f) : List (AxisPoint f) → AxisPoint f
  | [] => axisZero f
  | a :: rest =>
      axisAddOf f hAdd a
        (axisMulOf f hMul x (axisHornerOf f hAdd hMul x rest))

/-- The explicit geometric Horner construction satisfies its relational
graph at every finite coefficient list. -/
theorem axisHornerOf_spec
    (f : Frame Point) (hAdd : AddTotal f) (hMul : MulTotal f)
    (x : AxisPoint f) (coeff : List (AxisPoint f)) :
    HornerGraph f x coeff (axisHornerOf f hAdd hMul x coeff) := by
  induction coeff with
  | nil => rfl
  | cons a rest ih =>
      change ∃ t u : AxisPoint f,
        HornerGraph f x rest t ∧
        MulGraph f x t u ∧
        AddGraph f a u (axisAddOf f hAdd a
          (axisMulOf f hMul x (axisHornerOf f hAdd hMul x rest)))
      exact ⟨axisHornerOf f hAdd hMul x rest,
        axisMulOf f hMul x (axisHornerOf f hAdd hMul x rest),
        ih, axisMulOf_spec f hMul x _, axisAddOf_spec f hAdd a _⟩

/-- The relational evaluation determines precisely the same result as
the explicit recursively constructed function. -/
theorem axisHornerOf_eq_of_graph
    (f : Frame Point) (hAdd : AddTotal f) (hMul : MulTotal f)
    (x : AxisPoint f) (coeff : List (AxisPoint f))
    (z : AxisPoint f) (hz : HornerGraph f x coeff z) :
    axisHornerOf f hAdd hMul x coeff = z := by
  obtain ⟨v, _, huniq⟩ := hornerGraph_exists_unique f hAdd hMul x coeff
  have h1 : axisHornerOf f hAdd hMul x coeff = v :=
    huniq _ (axisHornerOf_spec f hAdd hMul x coeff)
  have h2 : z = v := huniq z hz
  exact h1.trans h2.symm

theorem hornerGraph_iff_axisHornerOf_eq
    (f : Frame Point) (hAdd : AddTotal f) (hMul : MulTotal f)
    (x : AxisPoint f) (coeff : List (AxisPoint f)) (z : AxisPoint f) :
    HornerGraph f x coeff z ↔ axisHornerOf f hAdd hMul x coeff = z := by
  constructor
  · intro hz
    exact axisHornerOf_eq_of_graph f hAdd hMul x coeff z hz
  · intro hz
    rw [← hz]
    exact axisHornerOf_spec f hAdd hMul x coeff

/-- A finite Horner evaluation of real geometric points, with all geometric
existence obligations discharged unconditionally from Plane. -/
noncomputable def tarskiHornerValue
    (f : Frame Point) (x : AxisPoint f)
    (coeff : List (AxisPoint f)) : AxisPoint f :=
  axisHornerOf f (operation_graphs_total_tarski f).1
    (operation_graphs_total_tarski f).2 x coeff

theorem tarskiHornerValue_spec
    (f : Frame Point) (x : AxisPoint f)
    (coeff : List (AxisPoint f)) :
    HornerGraph f x coeff (tarskiHornerValue f x coeff) :=
  axisHornerOf_spec f (operation_graphs_total_tarski f).1
    (operation_graphs_total_tarski f).2 x coeff

theorem tarskiHornerValue_eq_iff_graph
    (f : Frame Point) (x : AxisPoint f)
    (coeff : List (AxisPoint f)) (z : AxisPoint f) :
    tarskiHornerValue f x coeff = z ↔ HornerGraph f x coeff z := by
  exact (hornerGraph_iff_axisHornerOf_eq f
    (operation_graphs_total_tarski f).1
    (operation_graphs_total_tarski f).2 x coeff z).symm

#print axioms TarskiField.axisHornerOf_spec
#print axioms TarskiField.tarskiHornerValue_spec
#print axioms TarskiField.tarskiHornerValue_eq_iff_graph

end TarskiField


/-!
## First-order polynomial sign and root formulas have unique geometric values

Fix a Tarski frame O,I,J, a finite coefficient list and a valuation rho.
For every free coefficient index c and the polynomial input x, suppose
rho(c) and rho(x) equal the actual geometric axis points sigma(c)
and sigma(x). The existing finite-expression compiler proves that
the one-sorted sign formulas have exactly the same witnesses as
the relational, point-constructed HornerGraph.

NEGATIVE. From the negative formula obtain an axis point v together
with HornerGraph f x coeff v, v different from O, and Bet v O I.
Existence and uniqueness of HornerGraph identifies v with the
constructed tarskiHornerValue. Substitution establishes precisely the
negative-ray condition for this single point. Conversely, if the
constructed point satisfies both negative-ray conditions, the proved
HornerGraph specification supplies the required witness for the
original first-order formula. Both cases include empty coefficients.

POSITIVE. From the positive formula obtain an axis point v on the
strict positive ray with a HornerGraph witness. Uniqueness again
identifies it with the constructed value. Conversely that point and
its HornerGraph certificate witness the formula. The strict positive
ray already excludes the zero point.

ZERO. The already proved compiler says the root formula holds exactly
if HornerGraph evaluates to the axis zero. By uniqueness the selected
value equals zero if and only if this graph holds.

EXISTENTIAL ZERO. The existential formula says there is an actual
axis point satisfying the relational HornerGraph at zero. Apply the
preceding equality of the relational and functional results for each
possible point, in both directions. No external scalar sort is used.

DISJOINTNESS. If the first-order positive and negative formulas held
at the same valuation, their selected Horner point would be on both
strict opposite rays. The Tarski-derived positive_not_negative lemma
excludes this configuration. Thus no new functionality hypothesis,
field law, order-completeness principle or real coordinates are
used in the sign-disjointness proof.

The method matches functional extraction from geometric construction
relations in GeoCoq Ch16 sum_f and prod_f. The finite syntax and
the sign predicates here remain solely in Tarski's point language.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Negative polynomial formula iff the unique geometric Horner value
is strictly on the negative oriented axis ray. -/
theorem polynomialNegativeFormula_value_iff_tarski
    (f : Frame Point) {n : Nat}
    (o i j x : Fin n) (coefficients : List (Fin n))
    (ρ : Fin n → Point) (σ : Fin n → AxisPoint f)
    (hO : ρ o = f.O) (hI : ρ i = f.I) (hJ : ρ j = f.J)
    (hx : ρ x = (σ x).1)
    (hcoeff : ∀ c, c ∈ coefficients → ρ c = (σ c).1) :
    (polynomialNegativeFormula o i j x coefficients).eval ρ ↔
      (tarskiHornerValue f (σ x) (coefficients.map σ)).1 ≠ f.O ∧
      Bet (tarskiHornerValue f (σ x) (coefficients.map σ)).1 f.O f.I := by
  rw [polynomialNegativeFormula_horner_iff
    f o i j x coefficients ρ σ hO hI hJ hx hcoeff]
  constructor
  · rintro ⟨v, hv, hnonzero, hneg⟩
    have hvalue :
        tarskiHornerValue f (σ x) (coefficients.map σ) = v :=
      (tarskiHornerValue_eq_iff_graph
        f (σ x) (coefficients.map σ) v).mpr hv
    simpa only [hvalue] using And.intro hnonzero hneg
  · rintro ⟨hnonzero, hneg⟩
    exact ⟨tarskiHornerValue f (σ x) (coefficients.map σ),
      tarskiHornerValue_spec f (σ x) (coefficients.map σ),
      hnonzero, hneg⟩

/-- Positive polynomial formula iff the unique geometric Horner value
belongs to the strict positive ray. -/
theorem polynomialPositiveFormula_value_iff_tarski
    (f : Frame Point) {n : Nat}
    (o i j x : Fin n) (coefficients : List (Fin n))
    (ρ : Fin n → Point) (σ : Fin n → AxisPoint f)
    (hO : ρ o = f.O) (hI : ρ i = f.I) (hJ : ρ j = f.J)
    (hx : ρ x = (σ x).1)
    (hcoeff : ∀ c, c ∈ coefficients → ρ c = (σ c).1) :
    (polynomialPositiveFormula o i j x coefficients).eval ρ ↔
      Positive f (tarskiHornerValue f (σ x) (coefficients.map σ)) := by
  rw [polynomialPositiveFormula_horner_iff
    f o i j x coefficients ρ σ hO hI hJ hx hcoeff]
  constructor
  · rintro ⟨v, hv, hpositive⟩
    have hvalue :
        tarskiHornerValue f (σ x) (coefficients.map σ) = v :=
      (tarskiHornerValue_eq_iff_graph
        f (σ x) (coefficients.map σ) v).mpr hv
    simpa only [hvalue] using hpositive
  · intro hpositive
    exact ⟨tarskiHornerValue f (σ x) (coefficients.map σ),
      tarskiHornerValue_spec f (σ x) (coefficients.map σ),
      hpositive⟩

/-- One-sorted root formula iff the selected geometric value is O. -/
theorem polynomialRootFormula_value_iff_tarski
    (f : Frame Point) {n : Nat}
    (o i j x : Fin n) (coefficients : List (Fin n))
    (ρ : Fin n → Point) (σ : Fin n → AxisPoint f)
    (hO : ρ o = f.O) (hI : ρ i = f.I) (hJ : ρ j = f.J)
    (hx : ρ x = (σ x).1)
    (hcoeff : ∀ c, c ∈ coefficients → ρ c = (σ c).1) :
    (polynomialRootFormula o i j x coefficients).eval ρ ↔
      tarskiHornerValue f (σ x) (coefficients.map σ) = axisZero f := by
  rw [polynomialRootFormula_horner_iff
    f o i j x coefficients ρ σ hO hI hJ hx hcoeff]
  exact (tarskiHornerValue_eq_iff_graph
    f (σ x) (coefficients.map σ) (axisZero f)).symm

/-- There is a first-order root iff an actual axis point has zero as
its unique geometric Horner value. -/
theorem polynomialHasRootFormula_value_iff_tarski
    (f : Frame Point) {n : Nat}
    (o i j : Fin n) (coefficients : List (Fin n))
    (ρ : Fin n → Point) (σ : Fin n → AxisPoint f)
    (hO : ρ o = f.O) (hI : ρ i = f.I) (hJ : ρ j = f.J)
    (hcoeff : ∀ c, c ∈ coefficients → ρ c = (σ c).1) :
    (polynomialHasRootFormula o i j coefficients).eval ρ ↔
      ∃ x : AxisPoint f,
        tarskiHornerValue f x (coefficients.map σ) = axisZero f := by
  rw [polynomialHasRootFormula_horner_iff
    f o i j coefficients ρ σ hO hI hJ hcoeff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (tarskiHornerValue_eq_iff_graph
      f x (coefficients.map σ) (axisZero f)).mpr hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (tarskiHornerValue_eq_iff_graph
      f x (coefficients.map σ) (axisZero f)).mp hx⟩

/-- The two opposite sign formulas cannot hold for the same finite
polynomial and geometric input; only Tarski axioms are used. -/
theorem polynomialSignFormulas_disjoint_tarski
    (f : Frame Point) {n : Nat}
    (o i j x : Fin n) (coefficients : List (Fin n))
    (ρ : Fin n → Point) (σ : Fin n → AxisPoint f)
    (hO : ρ o = f.O) (hI : ρ i = f.I) (hJ : ρ j = f.J)
    (hx : ρ x = (σ x).1)
    (hcoeff : ∀ c, c ∈ coefficients → ρ c = (σ c).1) :
    ¬ ((polynomialPositiveFormula o i j x coefficients).eval ρ ∧
       (polynomialNegativeFormula o i j x coefficients).eval ρ) := by
  rintro ⟨hp, hn⟩
  have hPositive :
      Positive f (tarskiHornerValue f (σ x) (coefficients.map σ)) :=
    (polynomialPositiveFormula_value_iff_tarski
      f o i j x coefficients ρ σ hO hI hJ hx hcoeff).mp hp
  have hNegative :
      (tarskiHornerValue f (σ x) (coefficients.map σ)).1 ≠ f.O ∧
      Bet (tarskiHornerValue f (σ x) (coefficients.map σ)).1 f.O f.I :=
    (polynomialNegativeFormula_value_iff_tarski
      f o i j x coefficients ρ σ hO hI hJ hx hcoeff).mp hn
  exact positive_not_negative f _ hPositive hNegative.2

#print axioms TarskiField.polynomialNegativeFormula_value_iff_tarski
#print axioms TarskiField.polynomialPositiveFormula_value_iff_tarski
#print axioms TarskiField.polynomialRootFormula_value_iff_tarski
#print axioms TarskiField.polynomialHasRootFormula_value_iff_tarski
#print axioms TarskiField.polynomialSignFormulas_disjoint_tarski

end TarskiField



/-!
# Finite-Horner polynomial strict-sign persistence from finite algebra

This file uses only the algebra and order axioms of an *arbitrary* ordered
field, including non-Archimedean fields. It does not use real numbers,
topology, the analytic intermediate value theorem, Dedekind completeness,
or any new Tarski-plane axiom.

This proof is an independently compilable *downstream template*, to be
applied to the scalar-axis carrier only once its field and order laws
have been proved from Tarski's primitive Bet and Cong geometry.

For finite coefficient lists, recursively define:
  H(x,[]) = 0;
  H(x,a::rest) = a + x * H(x,rest).

For B >= 0 define the two finite coefficient-list bounds:
  V(B,[]) = 0;
  V(B,a::rest) = |a| + B*V(B,rest);
  D(B,[]) = 0;
  D(B,a::rest) = V(B,rest) + B*D(B,rest).

Complete proofs by structural induction establish:
  |x| <= B -> |H(x,c)| <= V(B,c),
  |x|,|y| <= B -> |H(x,c)-H(y,c)| <= |x-y| * D(B,c).

For the second induction, expand the ring identity
  H(x,a::r)-H(y,a::r)
    = (x-y)*H(x,r)+y*(H(x,r)-H(y,r)),
bound each summand, and combine.

Given H(b,c) != 0, set B=|b| + 1 and K=D(B,c)+1 > 0;
then delta=min(1,|H(b,c)|/K)>0. If |x-b|<delta, then
  |x| <= B,
  |H(x,c)-H(b,c)| <= |x-b| D(B,c)
                    < delta*K <= |H(b,c)|,
so the strict sign at b persists at x.

The construction gives a finite, explicit algebraic modulus
of sign persistence without importing continuity.
-/

namespace TarskiField

section FiniteHornerAlgebraicSigns

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

def finiteHornerValue (x : F) : List F → F
  | [] => 0
  | a :: rest => a + x * finiteHornerValue x rest

/-- Exact finite Horner difference quotient from the independently checked
A13 calculation. This factorization needs no division, works for x=y,
and includes empty or trailing-zero coefficient lists. -/
def finiteHornerDifferenceQuotient (x y : F) : List F → F
  | [] => 0
  | _ :: rest =>
      finiteHornerValue x rest +
        y * finiteHornerDifferenceQuotient x y rest

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem finiteHorner_sub_eq_mul_quotient_tarski
    (x y : F) (coeff : List F) :
    finiteHornerValue x coeff - finiteHornerValue y coeff =
      (x - y) * finiteHornerDifferenceQuotient x y coeff := by
  induction coeff with
  | nil =>
      simp [finiteHornerValue, finiteHornerDifferenceQuotient]
  | cons a rest ih =>
      change
        (a + x * finiteHornerValue x rest) -
          (a + y * finiteHornerValue y rest) =
        (x - y) *
          (finiteHornerValue x rest +
            y * finiteHornerDifferenceQuotient x y rest)
      calc
        _ = (x - y) * finiteHornerValue x rest +
              y * (finiteHornerValue x rest -
                finiteHornerValue y rest) := by ring
        _ = (x - y) *
              (finiteHornerValue x rest +
                y * finiteHornerDifferenceQuotient x y rest) := by
            rw [ih]
            ring

#print axioms TarskiField.finiteHorner_sub_eq_mul_quotient_tarski


def finiteHornerBound (B : F) : List F → F
  | [] => 0
  | a :: rest => |a| + B * finiteHornerBound B rest

def finiteHornerLipschitzBound (B : F) : List F → F
  | [] => 0
  | _ :: rest =>
      finiteHornerBound B rest + B * finiteHornerLipschitzBound B rest

theorem finiteHornerBound_nonneg (B : F) (hB : 0 ≤ B)
    (coeff : List F) : 0 ≤ finiteHornerBound B coeff := by
  induction coeff with
  | nil => simp [finiteHornerBound]
  | cons a rest ih =>
      change 0 ≤ |a| + B * finiteHornerBound B rest
      exact add_nonneg (abs_nonneg _) (mul_nonneg hB ih)

theorem finiteHornerLipschitzBound_nonneg (B : F) (hB : 0 ≤ B)
    (coeff : List F) : 0 ≤ finiteHornerLipschitzBound B coeff := by
  induction coeff with
  | nil => simp [finiteHornerLipschitzBound]
  | cons a rest ih =>
      change 0 ≤
        finiteHornerBound B rest + B * finiteHornerLipschitzBound B rest
      exact add_nonneg (finiteHornerBound_nonneg B hB rest)
        (mul_nonneg hB ih)

theorem finiteHorner_abs_le (B : F) (hB : 0 ≤ B)
    (x : F) (hx : |x| ≤ B) (coeff : List F) :
    |finiteHornerValue x coeff| ≤ finiteHornerBound B coeff := by
  induction coeff with
  | nil => simp [finiteHornerValue, finiteHornerBound]
  | cons a rest ih =>
      change |a + x * finiteHornerValue x rest| ≤
        |a| + B * finiteHornerBound B rest
      calc
        _ ≤ |a| + |x * finiteHornerValue x rest| := abs_add_le _ _
        _ = |a| + |x| * |finiteHornerValue x rest| := by rw [abs_mul]
        _ ≤ |a| + B * |finiteHornerValue x rest| :=
          add_le_add_right
            (mul_le_mul_of_nonneg_right hx (abs_nonneg _)) _
        _ ≤ |a| + B * finiteHornerBound B rest :=
          add_le_add_right (mul_le_mul_of_nonneg_left ih hB) _

theorem finiteHorner_difference_le (B : F) (hB : 0 ≤ B)
    (x y : F) (hx : |x| ≤ B) (hy : |y| ≤ B)
    (coeff : List F) :
    |finiteHornerValue x coeff - finiteHornerValue y coeff| ≤
      |x-y| * finiteHornerLipschitzBound B coeff := by
  induction coeff with
  | nil => simp [finiteHornerValue, finiteHornerLipschitzBound]
  | cons a rest ih =>
      have hid :
          finiteHornerValue x (a :: rest) -
              finiteHornerValue y (a :: rest) =
            (x-y)*finiteHornerValue x rest +
            y*(finiteHornerValue x rest - finiteHornerValue y rest) := by
        simp only [finiteHornerValue]
        ring
      rw [hid]
      change |(x-y)*finiteHornerValue x rest +
          y*(finiteHornerValue x rest - finiteHornerValue y rest)| ≤
        |x-y| * (finiteHornerBound B rest +
          B*finiteHornerLipschitzBound B rest)
      calc
        _ ≤ |(x-y)*finiteHornerValue x rest| +
            |y*(finiteHornerValue x rest -
                 finiteHornerValue y rest)| :=
          abs_add_le _ _
        _ = |x-y| * |finiteHornerValue x rest| +
            |y| * |finiteHornerValue x rest -
                    finiteHornerValue y rest| := by
          rw [abs_mul, abs_mul]
        _ ≤ |x-y| * finiteHornerBound B rest +
             B*(|x-y| * finiteHornerLipschitzBound B rest) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (finiteHorner_abs_le B hB x hx rest) (abs_nonneg _)
          · calc
              _ ≤ B * |finiteHornerValue x rest -
                       finiteHornerValue y rest| :=
                mul_le_mul_of_nonneg_right hy (abs_nonneg _)
              _ ≤ B * (|x-y| * finiteHornerLipschitzBound B rest) :=
                mul_le_mul_of_nonneg_left ih hB
        _ = |x-y| * (finiteHornerBound B rest +
            B*finiteHornerLipschitzBound B rest) := by ring

theorem finiteHorner_local_difference_small
    (coeff : List F) (b : F)
    (hb : finiteHornerValue b coeff ≠ 0) :
    ∃ δ : F, 0 < δ ∧ ∀ x : F, |x-b| < δ →
      |finiteHornerValue x coeff - finiteHornerValue b coeff| <
        |finiteHornerValue b coeff| := by
  let B : F := |b| + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let K : F := finiteHornerLipschitzBound B coeff + 1
  have hK : 0 < K := by
    have hBound := finiteHornerLipschitzBound_nonneg B hB coeff
    dsimp [K]
    linarith
  have hKne : K ≠ 0 := ne_of_gt hK
  let δ : F := min 1 (|finiteHornerValue b coeff| / K)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (div_pos (abs_pos.mpr hb) hK)
  refine ⟨δ, hδ, ?_⟩
  intro x hxδ
  have hx1 : |x-b| < 1 := lt_of_lt_of_le hxδ (min_le_left 1 _)
  have hxB : |x| ≤ B := by
    have hxid : x = (x-b) + b := by ring
    calc
      |x| = |(x-b)+b| := congrArg abs hxid
      _ ≤ |x-b| + |b| := abs_add_le _ _
      _ ≤ B := by dsimp [B]; linarith
  have hbB : |b| ≤ B := by dsimp [B]; linarith
  have hKbound : finiteHornerLipschitzBound B coeff ≤ K := by
    dsimp [K]
    linarith
  calc
    _ ≤ |x-b| * finiteHornerLipschitzBound B coeff :=
      finiteHorner_difference_le B hB x b hxB hbB coeff
    _ ≤ |x-b| * K :=
      mul_le_mul_of_nonneg_left hKbound (abs_nonneg _)
    _ < δ*K := mul_lt_mul_of_pos_right hxδ hK
    _ ≤ (|finiteHornerValue b coeff|/K)*K :=
      mul_le_mul_of_nonneg_right (min_le_right 1 _) (le_of_lt hK)
    _ = |finiteHornerValue b coeff| := by
      field_simp [hKne]

theorem finiteHorner_positive_local (coeff : List F) (b : F)
    (hb : 0 < finiteHornerValue b coeff) :
    ∃ δ : F, 0 < δ ∧ ∀ x : F, |x-b| < δ →
      0 < finiteHornerValue x coeff := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    finiteHorner_local_difference_small coeff b (ne_of_gt hb)
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hs := hsmall x hx
  rw [abs_of_pos hb] at hs
  have hbelow :
      -|finiteHornerValue x coeff - finiteHornerValue b coeff| ≤
      finiteHornerValue x coeff - finiteHornerValue b coeff :=
    neg_abs_le _
  linarith

theorem finiteHorner_negative_local (coeff : List F) (b : F)
    (hb : finiteHornerValue b coeff < 0) :
    ∃ δ : F, 0 < δ ∧ ∀ x : F, |x-b| < δ →
      finiteHornerValue x coeff < 0 := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    finiteHorner_local_difference_small coeff b (ne_of_lt hb)
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hs := hsmall x hx
  rw [abs_of_neg hb] at hs
  have habove :
      finiteHornerValue x coeff - finiteHornerValue b coeff ≤
      |finiteHornerValue x coeff - finiteHornerValue b coeff| :=
    le_abs_self _
  linarith

#print axioms TarskiField.finiteHorner_difference_le
#print axioms TarskiField.finiteHorner_positive_local
#print axioms TarskiField.finiteHorner_negative_local

end FiniteHornerAlgebraicSigns
end TarskiField




/-!
## A13 to finite-Horner root: discharge local sign hypotheses completely

The preceding finite-Horner derivation was proved in any ordered field:
for every finite coefficient list c and every scalar t with H(t,c) != 0,
an explicit positive δ (constructed by finitely many ordered-field
operations) makes the sign of H(x,c) constant whenever |x-t|<δ.
In particular the positive and negative locality functions are
unconditional *theorems of finite ordered-field algebra*.

Now fix L<R and the actual polynomial initial negative prefix
C = {x | L<=x<=R, and every t in [L,x] has H(t,c)<0}.
Assume the following exact conclusion of the intended first-order A13
cut: a selected *internal axis scalar* b lies in [L,R], bounds C,
and is not larger than any other upper bound of C.
The A13 axiom itself is not strengthened or replaced here:
the missing geometric task is to transport its primitive-betweenness
least-upper-bound result into this ordered-field statement.

Complete proof that b is a zero:

First, from H(L,c)<0, use the finite-Horner negative sign lemma at L.
Choose a positive δ on which H remains negative. Put
ε=min(δ,R-L)>0 and x0=L+ε/2. Then L<x0<R, and every t in [L,x0]
satisfies |t-L|<δ and H(t,c)<0. Thus x0 belongs to C and b>=x0>L.

If H(b,c)>0, positive locality gives δ>0 and choose
y=b-min(δ,b-L)/2. Then L<y<b and H(y,c)>0. Every x in C must lie
below y: otherwise y is a point in [L,x] with a positive polynomial
value, contradicting the prefix condition that all such values are
negative. Hence y is an upper bound of C, contradicting that b is
its least upper bound because y<b.

If H(b,c)<0, then b<R since H(R,c)>0. Use negative locality at b
and choose z=b+min(δ,R-b)/2. Every t in [b,z] has H(t,c)<0.
For t in [L,b), t cannot be an upper bound of C (otherwise the
minimality of b forces b<=t). Therefore some x in C satisfies x>t;
the defining prefix property of x gives H(t,c)<0. The two cases
t<b and b<=t<=z exhaust t in [L,z], so z belongs to C.
But z>b, contradicting that b bounds C.

By linear-order trichotomy, neither positive nor negative value at b
is possible. Therefore H(b,c)=0. All endpoint cases are included:
b=L is ruled out by x0, and b=R is ruled out by H(R,c)>0.

This theorem invokes the already verified complete cut-boundary proof
in the same Tarski source, with the formerly explicit local sign
premises now discharged by *separately verified finite-Horner lemmas*.
It does not claim that the pending ordered-field laws on AxisPoint f
or the directed-betweenness correspondence are already established.
References for the geometric continuity semantics:
GeoCoq.Axioms.continuity_axioms and GeoCoq.Meta_theory.Continuity.first_order.
-/

namespace TarskiField

section FiniteHornerA13Bridge

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Finite-algebraic sign persistence plus the A13-cut least-upper-bound
conclusion force the exact finite-Horner polynomial value to be zero. -/
theorem finiteHorner_zero_at_A13_ordered_cut
    (coeff : List F) (L R b : F)
    (hLR : L < R)
    (hLeft : finiteHornerValue L coeff < 0)
    (hRight : 0 < finiteHornerValue R coeff)
    (hSegment : L ≤ b ∧ b ≤ R)
    (hBound : ∀ x : F,
      OrderedNegativePrefix (fun t => finiteHornerValue t coeff) L R x →
      x ≤ b)
    (hLeast : ∀ y : F,
      (∀ x : F,
        OrderedNegativePrefix (fun t => finiteHornerValue t coeff) L R x →
        x ≤ y) → b ≤ y) :
    finiteHornerValue b coeff = 0 := by
  exact ordered_negative_prefix_cut_zero_of_local_sign
    (fun t : F => finiteHornerValue t coeff) L R b
    hLR hLeft hRight hSegment hBound hLeast
    (fun t ht => finiteHorner_positive_local coeff t ht)
    (fun t ht => finiteHorner_negative_local coeff t ht)

/-- A13's ordered-cut existence claim therefore entails a zero in the
closed interval, with no additional analytic-continuity assumption. -/
theorem finiteHorner_root_exists_of_A13_ordered_cut
    (coeff : List F) (L R : F)
    (hLR : L < R)
    (hLeft : finiteHornerValue L coeff < 0)
    (hRight : 0 < finiteHornerValue R coeff)
    (hCut : ∃ b : F,
      (L ≤ b ∧ b ≤ R) ∧
      (∀ x : F,
        OrderedNegativePrefix (fun t => finiteHornerValue t coeff) L R x →
        x ≤ b) ∧
      (∀ y : F,
        (∀ x : F,
          OrderedNegativePrefix (fun t => finiteHornerValue t coeff) L R x →
          x ≤ y) → b ≤ y)) :
    ∃ x : F, L ≤ x ∧ x ≤ R ∧ finiteHornerValue x coeff = 0 := by
  obtain ⟨b, hSegment, hBound, hLeast⟩ := hCut
  exact ⟨b, hSegment.1, hSegment.2,
    finiteHorner_zero_at_A13_ordered_cut
      coeff L R b hLR hLeft hRight hSegment hBound hLeast⟩

#print axioms TarskiField.finiteHorner_zero_at_A13_ordered_cut
#print axioms TarskiField.finiteHorner_root_exists_of_A13_ordered_cut

end FiniteHornerA13Bridge

end TarskiField


/-!
## A13 finite-polynomial IVT implies nonnegative square roots

The original Tarski continuity scheme is not invoked as a second-order
statement about all continuous functions. The theorem below receives the
*exact target* still to be derived from its first-order polynomial cut:
every finite Horner expression with a strict negative value at L and
strict positive value at R has a point between L and R where the value
is zero.

Once the ordered-field laws on the actual Tarski axis are established,
the earlier explicit finite-Horner sign persistence plus the proved A13
cut boundary will supply this finite-polynomial-IVT property.

Complete finite-algebra proof of square-root existence:
- Fix a>0 and take the three-element coefficient list [-a,0,1].
- By the definition of finite Horner evaluation, this list represents
  the polynomial q(x)=-a+x*x; no formal derivative or analytic limit.
- At L=0, q(0)=-a<0.
- At R=a+1, R>0 and q(R)=a*a+a+1>0. Here a*a>=0 from
  the ordered-field square-nonnegativity theorem, while a>0 and 1>0.
- The finite polynomial sign-change property supplies x with
  0<=x<=a+1 and q(x)=0. Ring arithmetic rearranges q(x)=0 into
  x*x=a. Thus x is an internal nonnegative square root.
- For a=0, x=0 is a root by ring identities. The two cases a>0
  and a=0 exhaust a>=0 by linear-order trichotomy.

This is a downstream algebraic conditional theorem, *not* a new axiom
on Tarski Point and not a completed derivation of the IVT property.
The witness will be mapped back to MulGraph using uniqueness of the
previously geometrically constructed multiplication, never by
postulating the field laws on the point sort.
-/

namespace TarskiField

section FiniteHornerQuadraticRoot

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The precise finite-polynomial intermediate-value target of A13,
stated as a predicate on an arbitrary interpreted ordered field. -/
def FiniteHornerIVT : Prop :=
  ∀ (coeff : List F) (L R : F),
    L < R →
    finiteHornerValue L coeff < 0 →
    0 < finiteHornerValue R coeff →
    ∃ x : F, L ≤ x ∧ x ≤ R ∧ finiteHornerValue x coeff = 0

/-- A strict positive scalar has a nonnegative square root, assuming
only finite-polynomial sign-change for the explicitly constructed
quadratic list [-a,0,1]. -/
theorem positive_sqrt_of_finiteHornerIVT
    (hIVT : FiniteHornerIVT (F := F))
    (a : F) (ha : 0 < a) :
    ∃ x : F, 0 ≤ x ∧ x * x = a := by
  let c : List F := [-a, 0, 1]
  have hLR : (0 : F) < a + 1 := by linarith
  have hLeft : finiteHornerValue (0 : F) c < 0 := by
    simp only [c, finiteHornerValue]
    simpa using (neg_lt_zero.mpr ha)
  have hRight : 0 < finiteHornerValue (a + 1) c := by
    have hSquare : 0 ≤ a * a := mul_self_nonneg a
    simp only [c, finiteHornerValue]
    nlinarith
  obtain ⟨x, hx0, _, hx⟩ :=
    hIVT c 0 (a + 1) hLR hLeft hRight
  refine ⟨x, hx0, ?_⟩
  simp only [c, finiteHornerValue] at hx
  nlinarith

/-- Nonnegative square roots are obtained by splitting the zero
and strict-positive cases, with no extra completeness assumption. -/
theorem nonnegative_sqrt_of_finiteHornerIVT
    (hIVT : FiniteHornerIVT (F := F))
    (a : F) (ha : 0 ≤ a) :
    ∃ x : F, 0 ≤ x ∧ x * x = a := by
  rcases eq_or_lt_of_le ha with hzero | hpositive
  · subst a
    exact ⟨0, le_refl 0, by ring⟩
  · exact positive_sqrt_of_finiteHornerIVT hIVT a hpositive

#print axioms TarskiField.positive_sqrt_of_finiteHornerIVT
#print axioms TarskiField.nonnegative_sqrt_of_finiteHornerIVT

end FiniteHornerQuadraticRoot

end TarskiField




/-!
## Algebraic A13-to-square-root assembly, with an exact geometric interface

Define the outstanding A13-ordered-cut property as follows: for each
finite Horner list c and oriented interval L<R with negative value at L
and positive value at R, the internal ordered axis contains a point b
in the interval that is the least upper bound of the *definable*
initial negative prefix. This is a property to prove from first-order
Tarski A13 and the geometric order/Bet correspondence, not an
extra assumption on Plane.

Complete proof of the assembly:
1. Fix an arbitrary finite polynomial and a strict sign-change
   interval. Use the claimed ordered A13 cut property to obtain b
   and unpack its interval, upper-bound, and minimality conjuncts.
2. The already verified finiteHorner_root_exists_of_A13_ordered_cut
   proves H(b,c)=0. Its proof, previously checked by Lean, derives
   *all* sign-persistence claims from finite algebra, and handles
   positive, zero and negative boundary values exhaustively.
3. Since c,L,R were arbitrary, this construction establishes
   FiniteHornerIVT, a universal property over finite coefficient lists.
4. Fix a>=0. If a=0, the chosen root is x=0. If a>0, evaluate
   [-a,0,1] at L=0 and R=a+1. The first value is -a<0; the
   second is a²+a+1>0. Step 3 gives an x in [0,a+1] with x²=a.
   All the square-root branches have already been explicitly proved
   by the preceding verified quadratic-root lemmas.

The only remaining premise is precisely the first-order A13 to
*ordered* cut correspondence; there is no analytic continuity
hypothesis, Archimedean principle or imported real coordinate model.
-/

namespace TarskiField

section FiniteHornerA13SquareRootAssembly

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Precise remaining geometric-order interface: A13 supplies a least
upper bound for each finite-Horner definable negative-prefix cut. -/
def FiniteHornerA13OrderedCuts : Prop :=
  ∀ (coeff : List F) (L R : F),
    L < R →
    finiteHornerValue L coeff < 0 →
    0 < finiteHornerValue R coeff →
    ∃ b : F,
      (L ≤ b ∧ b ≤ R) ∧
      (∀ x : F,
        OrderedNegativePrefix (fun t => finiteHornerValue t coeff) L R x →
        x ≤ b) ∧
      (∀ y : F,
        (∀ x : F,
          OrderedNegativePrefix (fun t => finiteHornerValue t coeff) L R x →
          x ≤ y) → b ≤ y)

/-- Exact finite polynomial intermediate-value property follows from the
definable A13 least-upper-bound interface and proved Horner inequalities. -/
theorem finiteHornerIVT_of_A13_ordered_cuts
    (hA13 : FiniteHornerA13OrderedCuts (F := F)) :
    FiniteHornerIVT (F := F) := by
  intro coeff L R hLR hLeft hRight
  exact finiteHorner_root_exists_of_A13_ordered_cut
    coeff L R hLR hLeft hRight
    (hA13 coeff L R hLR hLeft hRight)

/-- The finite definable-cut version of A13 implies nonnegative
square-root existence in the internally interpreted ordered field. -/
theorem nonnegative_sqrt_of_A13_ordered_cuts
    (hA13 : FiniteHornerA13OrderedCuts (F := F))
    (a : F) (ha : 0 ≤ a) :
    ∃ x : F, 0 ≤ x ∧ x*x = a := by
  exact nonnegative_sqrt_of_finiteHornerIVT
    (finiteHornerIVT_of_A13_ordered_cuts hA13) a ha

#print axioms TarskiField.finiteHornerIVT_of_A13_ordered_cuts
#print axioms TarskiField.nonnegative_sqrt_of_A13_ordered_cuts

end FiniteHornerA13SquareRootAssembly

end TarskiField


/-!
## Semantic normalization of the first-order A13 negative polynomial prefix

The complete natural-language proof precedes this theorem in
proofs/Tarski_Polynomial_Prefix_Semantics.md.

For an actual axis point X, the one-sorted finite Tarski formula for
the initial negative polynomial prefix is equivalent to:

  Bet L X R,
  and for every ACTUAL axis point t with Bet L t X,
  the uniquely constructed geometric Horner value H(t) is nonzero
  and lies on the negative ray Bet(H(t),O,I).

The forward direction extracts the universally quantified point T
and applies the already verified negative-sign-to-Horner theorem.
The reverse direction must first establish that an arbitrary plane
point T between L and X is on the axis OI. The verified neutral-Tarski
segment-closure theorem supplies that exact subtype witness.

The formula uses TWO nested quantifiers. Its shifted coefficient
indices are c.succ.succ, and the two-level environments below ensure
that each such variable still denotes the original coefficient.
This is a finite binder/substitution proof, not the introduction
of an external polynomial evaluation or a new field.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- The exact finite first-order lower cut and the geometric
negative-Horner initial prefix agree on every axis point. -/
theorem polynomialLowerCutFormula_geometricValue_iff_tarski
    (f : Frame Point) {n : Nat}
    (o i j l r : Fin n) (coefficients : List (Fin n))
    (ρ : Fin n → Point) (σ : Fin n → AxisPoint f)
    (hO : ρ o = f.O) (hI : ρ i = f.I) (hJ : ρ j = f.J)
    (hl : ρ l = (σ l).1) (hr : ρ r = (σ r).1)
    (hcoeff : ∀ c, c ∈ coefficients → ρ c = (σ c).1)
    (X : AxisPoint f) :
    (polynomialLowerCutFormula o i j l r coefficients).eval
      (Fin.cons X.1 ρ) ↔
    Bet (σ l).1 X.1 (σ r).1 ∧
      ∀ t : AxisPoint f,
        Bet (σ l).1 t.1 X.1 →
        (tarskiHornerValue f t (coefficients.map σ)).1 ≠ f.O ∧
          Bet (tarskiHornerValue f t (coefficients.map σ)).1 f.O f.I := by
  have hShift (t : AxisPoint f) :
      (polynomialNegativeFormula
        o.succ.succ i.succ.succ j.succ.succ 0
        ((coefficients.map Fin.succ).map Fin.succ)).eval
          (Fin.cons t.1 (Fin.cons X.1 ρ)) ↔
      (tarskiHornerValue f t (coefficients.map σ)).1 ≠ f.O ∧
        Bet (tarskiHornerValue f t (coefficients.map σ)).1 f.O f.I := by
    let σ2 : Fin (n + 2) → AxisPoint f :=
      Fin.cons t (Fin.cons X σ)
    let ρ2 : Fin (n + 2) → Point :=
      Fin.cons t.1 (Fin.cons X.1 ρ)
    have hcoeff2 :
        ∀ c, c ∈ ((coefficients.map Fin.succ).map Fin.succ) →
          ρ2 c = (σ2 c).1 := by
      intro c hc
      rcases List.mem_map.mp hc with ⟨d, hd, rfl⟩
      rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
      simpa only [ρ2, σ2, Fin.cons_succ] using hcoeff e he
    have hCoeffMap :
        ((coefficients.map Fin.succ).map Fin.succ).map σ2 =
          coefficients.map σ := by
      simp [σ2, List.map_map, Function.comp_def]
    have hFormula :=
      polynomialNegativeFormula_value_iff_tarski
        f o.succ.succ i.succ.succ j.succ.succ 0
        ((coefficients.map Fin.succ).map Fin.succ)
        ρ2 σ2
        (by simpa [ρ2] using hO) (by simpa [ρ2] using hI)
        (by simpa [ρ2] using hJ) (by rfl) hcoeff2
    simpa only [ρ2, σ2, Fin.cons_zero, hCoeffMap] using hFormula
  rw [polynomialLowerCutFormula_prefix_eval]
  constructor
  · rintro ⟨_, hBetween, hPrefix⟩
    refine ⟨by simpa [hl, hr] using hBetween, ?_⟩
    intro t ht
    apply (hShift t).mp
    apply hPrefix t.1
    simpa [hl] using ht
  · rintro ⟨hBetween, hNegative⟩
    refine ⟨by simpa [hO, hI] using X.2, ?_, ?_⟩
    · simpa [hl, hr] using hBetween
    · intro T hBet
      have hLaxis : Col f.O f.I (ρ l) := by
        simpa [hl] using (σ l).2
      have hTaxis : Col f.O f.I T :=
        col_segment_closed_tarski f.O_ne_I hLaxis X.2 hBet
      let t : AxisPoint f := ⟨T, hTaxis⟩
      have htBet : Bet (σ l).1 t.1 X.1 := by
        simpa [t, hl] using hBet
      have hNeg := hNegative t htBet
      exact (hShift t).mpr (by simpa [t] using hNeg)

#print axioms TarskiField.polynomialLowerCutFormula_geometricValue_iff_tarski

end TarskiField




/-!
# Integrated final-goal closure and ordered-axis law derivation

## Logical status and complete proof of the final target equivalence

The complete 17-conjunct final proposition RealClosedAxisGoal contains
nine outstanding statements: the commutativity and associativity laws
for the two geometric operations, the left distributive law, the
positive closure of addition and multiplication, the geometric
square-root property and the odd-degree polynomial root property.
The remaining eight conjuncts (operation existence, right zero,
additive inverse, multiplicative unit and inverse, trichotomy and
properness of positive rays) are previously proved unconditionally
from the Tarski Plane axioms in this same consolidated source.

The forward implication of the equivalence takes the nine indicated
conjuncts from RealClosedAxisGoal. Conversely, choose the already
constructed addition and multiplication totality proofs, use the
proved right-zero and additive-inverse theorems, choose the proved
multiplicative-unit and inverse theorems from mulKernel_tarski,
and use the proved positive-trichotomy and properness lemmas.
Together with the nine stated goals, these are exactly the
17 conjuncts in the original definition; no side condition has
been forgotten, and no new geometric axiom is installed.

## Ordered axis: completed consequences of the outstanding algebraic laws

Strict comparison x<y is by definition a positive geometric
displacement d satisfying AddGraph f x d y.

TOTALITY. Fix x,y and choose d uniquely by the Tarski-constructed
geometric displacement. The proven positiveTrichotomy_tarski applied
to d has three exhaustive branches. If d=0, uniqueness of the
AddGraph result with the already proved right-zero identity gives
x=y. If d is positive, it directly witnesses x<y. Otherwise there
exists a positive e with d+e=0. Choose w with y+e=w by geometric
totality. Apply the *stated* associativity law to x+d=y,
y+e=w, d+e=0, x+0=x, obtaining w=x. Thus e witnesses y<x.
These are all cases, and associativity is used only in the third.

TRANSITIVITY. If x<y by positive displacement a and y<z by positive
displacement b, construct c=a+b and w=x+c by geometric totality.
Associativity applied to x+a=y, y+b=z, a+b=c, x+c=w shows z=w.
The *stated* positive-additive-closure goal makes c positive, so x<z.

ASYMMETRY. If x<y and y<x, take positive a,b with x+a=y,y+b=x.
Construct c=a+b and w=x+c. Associativity yields w=x.
The already verified geometric fixed-point theorem
addGraph_fixed_point_iff_zero_tarski forces c=0, while the
*stated* positive-additive-closure goal makes c positive, and
positive excludes zero. Contradiction.

NON-STRICT ORDER. AxisLe is equality or AxisLt. Reflexivity follows
by equality. Antisymmetry follows from asymmetry in the case when
both comparisons are strict; equality cases are immediate.
Transitivity follows from strict transitivity, with equality cases
handled by substitution. The strict order is therefore a total
linear order as soon as associativity and positive-additive-closure
are established synthetically. The correspondence with primitive
Tarski Bet remains an independent geometric obligation.

The following Lean declarations formalize each implication while
retaining the exact missing geometric hypotheses. Their proofs
do NOT count as a proof of associativity or positive closure.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- The final real-closed-axis goal is exactly the remaining nine
geometrically defined propositions; all other clauses are already
proved from Plane without a field-axiom postulate. -/
theorem realClosedAxisGoal_iff_nine_remaining_tarski
    (f : Frame Point) :
    RealClosedAxisGoal f ↔
      AddCommLaw f ∧ AddAssocLaw f ∧
      MulCommLaw f ∧ MulAssocLaw f ∧
      LeftDistributiveLaw f ∧
      PositiveAddClosed f ∧ PositiveMulClosed f ∧
      PositiveSquareRootProperty f ∧ OddPolynomialRootProperty f := by
  constructor
  · intro h
    rcases h with
      ⟨_, _, hAC, hAA, _, _, hMC, hMA, _, _, hD,
       hPA, hPM, _, _, hSQ, hOdd⟩
    exact ⟨hAC, hAA, hMC, hMA, hD, hPA, hPM, hSQ, hOdd⟩
  · rintro ⟨hAC, hAA, hMC, hMA, hD, hPA, hPM, hSQ, hOdd⟩
    obtain ⟨hAddTotal, hMulTotal⟩ := operation_graphs_total_tarski f
    obtain ⟨_, _, hMulOne, hMulInverse⟩ := mulKernel_tarski f
    exact ⟨hAddTotal, hMulTotal,
      hAC, hAA, addRightZeroLaw_tarski f, addInverseLaw_tarski f,
      hMC, hMA, hMulOne, hMulInverse, hD, hPA, hPM,
      positiveTrichotomy_tarski f, positiveProper_tarski f, hSQ, hOdd⟩

/-- Trichotomy of the point-based strict order needs only synthetic
associativity, because positivity trichotomy and additive displacement
existence are already proved from Tarski geometry. -/
theorem axisLt_trichotomy_of_addAssoc_tarski
    (f : Frame Point) (hAssoc : AddAssocLaw f)
    (x y : AxisPoint f) :
    x = y ∨ AxisLt f x y ∨ AxisLt f y x := by
  let d := axisDisplacementOf f x y
  have hxd : AddGraph f x d y := axisDisplacementOf_spec f x y
  rcases positiveTrichotomy_tarski f d with hdZero | hdPos | hNeg
  · have hxyz : y = x := by
      rw [hdZero] at hxd
      exact (operation_graphs_functional_tarski f).1
        x (axisZero f) y x hxd (add_zero_right_tarski f x)
    exact Or.inl hxyz.symm
  · exact Or.inr (Or.inl ⟨d, hxd, hdPos⟩)
  · obtain ⟨e, hePos, hde⟩ := hNeg
    obtain ⟨w, hyew, _⟩ :=
      (operation_graphs_total_tarski f).1 y e
    have hywx : w = x :=
      hAssoc x d e y (axisZero f) w x
        hxd hyew hde (add_zero_right_tarski f x)
    rw [hywx] at hyew
    exact Or.inr (Or.inr ⟨e, hyew, hePos⟩)

/-- Two ordered positive geometric translations compose into another
positive translation using exactly associativity and positive closure. -/
theorem axisLt_trans_of_addAssoc_posClosed_tarski
    (f : Frame Point)
    (hAssoc : AddAssocLaw f)
    (hPositiveAdd : PositiveAddClosed f)
    {x y z : AxisPoint f}
    (hxy : AxisLt f x y) (hyz : AxisLt f y z) :
    AxisLt f x z := by
  obtain ⟨a, hxa, hpa⟩ := hxy
  obtain ⟨b, hyb, hpb⟩ := hyz
  obtain ⟨c, hab, _⟩ := (operation_graphs_total_tarski f).1 a b
  obtain ⟨w, hxw, _⟩ := (operation_graphs_total_tarski f).1 x c
  have hzw : z = w :=
    hAssoc x a b y c z w hxa hyb hab hxw
  rw [← hzw] at hxw
  exact ⟨c, hxw, hPositiveAdd a b c hpa hpb hab⟩

/-- Strict order is asymmetric: a positive geometric translation and
a positive translation back would force a positive displacement zero. -/
theorem axisLt_asymm_of_addAssoc_posClosed_tarski
    (f : Frame Point)
    (hAssoc : AddAssocLaw f)
    (hPositiveAdd : PositiveAddClosed f)
    {x y : AxisPoint f}
    (hxy : AxisLt f x y) (hyx : AxisLt f y x) : False := by
  obtain ⟨a, hxa, hpa⟩ := hxy
  obtain ⟨b, hyb, hpb⟩ := hyx
  obtain ⟨c, hab, _⟩ := (operation_graphs_total_tarski f).1 a b
  obtain ⟨w, hxw, _⟩ := (operation_graphs_total_tarski f).1 x c
  have hwx : x = w :=
    hAssoc x a b y c x w hxa hyb hab hxw
  rw [← hwx] at hxw
  have hcZero : c = axisZero f :=
    (addGraph_fixed_point_iff_zero_tarski f x c).mp hxw
  have hcPos : Positive f c := hPositiveAdd a b c hpa hpb hab
  exact hcPos.2.1 (congrArg Subtype.val hcZero)

/-- Antisymmetry of the derived non-strict relation, with no
independent order axioms on AxisPoint. -/
theorem axisLe_antisymm_of_addAssoc_posClosed_tarski
    (f : Frame Point)
    (hAssoc : AddAssocLaw f)
    (hPositiveAdd : PositiveAddClosed f)
    {x y : AxisPoint f}
    (hxy : AxisLe f x y) (hyx : AxisLe f y x) : x = y := by
  rcases hxy with hEq | hLt
  · exact hEq
  rcases hyx with hEq | hLt2
  · exact hEq.symm
  exact False.elim
    (axisLt_asymm_of_addAssoc_posClosed_tarski
      f hAssoc hPositiveAdd hLt hLt2)

/-- Transitivity of the non-strict relation follows from geometric
strict transitivity and two equality branches. -/
theorem axisLe_trans_of_addAssoc_posClosed_tarski
    (f : Frame Point)
    (hAssoc : AddAssocLaw f)
    (hPositiveAdd : PositiveAddClosed f)
    {x y z : AxisPoint f}
    (hxy : AxisLe f x y) (hyz : AxisLe f y z) : AxisLe f x z := by
  rcases hxy with hEq | hLt
  · subst y
    exact hyz
  rcases hyz with hEq | hLt2
  · subst z
    exact Or.inr hLt
  · exact Or.inr
      (axisLt_trans_of_addAssoc_posClosed_tarski
        f hAssoc hPositiveAdd hLt hLt2)

#print axioms TarskiField.realClosedAxisGoal_iff_nine_remaining_tarski
#print axioms TarskiField.axisLt_trichotomy_of_addAssoc_tarski
#print axioms TarskiField.axisLt_trans_of_addAssoc_posClosed_tarski
#print axioms TarskiField.axisLt_asymm_of_addAssoc_posClosed_tarski
#print axioms TarskiField.axisLe_antisymm_of_addAssoc_posClosed_tarski
#print axioms TarskiField.axisLe_trans_of_addAssoc_posClosed_tarski

end TarskiField


/-!
## Coefficient-sum growth bound for odd-degree leading-term domination

The final odd-degree-root proof needs a positive internal scalar T at
which the leading monomial dominates all lower-degree terms. This
section derives the exact finite-Horner estimate required for that
argument, without assuming an Archimedean field.

Let S(c) be the finite sum of the absolute values of the entries of a
coefficient list c. For every B>=1 and every NONEMPTY list c of
length n, the two inequalities to be proved are

 V(B,c) <= S(c)*B^(n-1)
 and for every y with |y|<=B,
 |H(y,c)| <= S(c)*B^(n-1).

These involve only the finite Horner recurrences, not limits.

Complete induction on the list:

For c=[], the theorem has a contradiction hypothesis c≠[]; hence
there is no such case to prove.

For c=[a], the value bound is |a| and the sum is |a|. Since n=1,
the exponent is zero and B^0=1, giving equality.

For c=a::b::tail, put r=b::tail. The induction hypothesis gives
V(B,r) <= S(r)*B^(length(tail)), since r has length length(tail)+1.
Because B>=1>=0, multiply both sides by B:
B*V(B,r) <= B*S(r)*B^length(tail)
           = S(r)*B^(length(tail)+1).
Also B^(length(tail)+1)>=1. Multiplying that inequality by |a|>=0
gives |a| <= |a| * B^(length(tail)+1).
Adding the last two inequalities yields
|a| + B*V(B,r) <= (|a| + S(r))*B^(length(tail)+1).
The left side is exactly V(B,a::r); the right side is
S(a::r)*B^(length(a::r)-1). Thus the induction is complete.

The second claim follows by applying the already Lean-proved
|H(y,c)|<=V(B,c), then the freshly established bound for V.
No omitted base or degeneracy cases remain.

Application to odd-degree roots: if p(X)=a_n X^n+q(X) with n>=1,
the lower coefficient list q is nonempty; for T>=1,
|q(±T)| <= S(q)*T^(n-1). Choose T>S(q)/|a_n| and T>1.
Then |a_n| * T^n>S(q)*T^(n-1)>=|q(±T)|. Because n is odd,
the leading terms at -T and T have opposite signs; the strict
bound transfers those signs to p(-T) and p(T). This establishes
opposite signs without any Archimedean axiom. The final use of the
finite-Horner IVT is a separate formalization obligation.

GeoCoq Ch14 order supplies the ordered-field comparison framework;
the present proof uses only its finite algebraic consequences after
the field has been constructed from point geometry.
-/

namespace TarskiField

section FiniteHornerLeadingTermBounds

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Finite sum of absolute coefficient magnitudes. -/
def finiteHornerCoeffAbsSum : List F → F
  | [] => 0
  | a :: rest => |a| + finiteHornerCoeffAbsSum rest

theorem finiteHornerCoeffAbsSum_nonneg (coeff : List F) :
    0 ≤ finiteHornerCoeffAbsSum coeff := by
  induction coeff with
  | nil => simp [finiteHornerCoeffAbsSum]
  | cons a rest ih =>
      change 0 ≤ |a| + finiteHornerCoeffAbsSum rest
      exact add_nonneg (abs_nonneg a) ih

/-- The bound is of degree exactly one less than the length of the
nonempty coefficient list. The empty-list case is excluded, and the
singleton and longer-list cases are proved separately. -/
theorem finiteHornerBound_le_coeffSum_mul_pow
    (B : F) (hB : 1 ≤ B) (coeff : List F) :
    coeff ≠ [] →
    finiteHornerBound B coeff ≤
      finiteHornerCoeffAbsSum coeff * B ^ (coeff.length - 1) := by
  induction coeff with
  | nil =>
      intro hne
      exact False.elim (hne rfl)
  | cons a rest ih =>
      intro _
      cases rest with
      | nil =>
          simp [finiteHornerBound, finiteHornerCoeffAbsSum]
      | cons b tail =>
          have hTail :
              finiteHornerBound B (b :: tail) ≤
                finiteHornerCoeffAbsSum (b :: tail) * B ^ tail.length := by
            simpa [List.length_cons] using (ih (by simp))
          have hB0 : (0 : F) ≤ B :=
            le_trans (zero_le_one) hB
          have hMul :
              B * finiteHornerBound B (b :: tail) ≤
                B * (finiteHornerCoeffAbsSum (b :: tail) * B ^ tail.length) :=
            mul_le_mul_of_nonneg_left hTail hB0
          have hPow : (1 : F) ≤ B ^ (tail.length + 1) :=
            one_le_pow₀ hB
          have hFirst : |a| ≤ |a| * B ^ (tail.length + 1) := by
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hPow (abs_nonneg a))
          have hStep :
              |a| + B * finiteHornerBound B (b :: tail) ≤
                (|a| + finiteHornerCoeffAbsSum (b :: tail)) *
                  B ^ (tail.length + 1) := by
            calc
              _ ≤ |a| +
                    B * (finiteHornerCoeffAbsSum (b :: tail) *
                         B ^ tail.length) :=
                  add_le_add_right hMul _
              _ = |a| + finiteHornerCoeffAbsSum (b :: tail) *
                    B ^ (tail.length + 1) := by
                  rw [pow_succ]
                  ring
              _ ≤ |a| * B ^ (tail.length + 1) +
                    finiteHornerCoeffAbsSum (b :: tail) *
                    B ^ (tail.length + 1) :=
                  add_le_add_left hFirst _
              _ = (|a| + finiteHornerCoeffAbsSum (b :: tail)) *
                    B ^ (tail.length + 1) := by ring
          simpa [finiteHornerBound, finiteHornerCoeffAbsSum,
            List.length_cons] using hStep

/-- Explicit non-Archimedean-safe bound for the actual finite Horner
value at every argument with magnitude at most B. -/
theorem finiteHorner_abs_le_coeffSum_mul_pow
    (B : F) (hB : 1 ≤ B)
    (coeff : List F) (hne : coeff ≠ [])
    (y : F) (hy : |y| ≤ B) :
    |finiteHornerValue y coeff| ≤
      finiteHornerCoeffAbsSum coeff * B ^ (coeff.length - 1) := by
  have hB0 : (0 : F) ≤ B := le_trans (zero_le_one) hB
  exact le_trans (finiteHorner_abs_le B hB0 y hy coeff)
    (finiteHornerBound_le_coeffSum_mul_pow B hB coeff hne)

#print axioms TarskiField.finiteHornerBound_le_coeffSum_mul_pow
#print axioms TarskiField.finiteHorner_abs_le_coeffSum_mul_pow

end FiniteHornerLeadingTermBounds

end TarskiField


/-!
## Finite-list identities needed for the odd-degree coefficient case split

For an arbitrary finite coefficient list r and last coefficient a,
the recursive Horner definition yields
H(x,r++[a]) = H(x,r) + a*x^length(r).

Proof. If r=[], the left side is H(x,[a])=a+0=a and
the right side is 0+a*x^0=a. If r=b::t, use the induction
hypothesis for t. Expanding the Horner recursion and using
the distributive law gives
b+x*(H(x,t)+a*x^length(t))
 = b+x*H(x,t)+a*x^(length(t)+1),
which is exactly the desired identity for b::t.

For coefficient-wise negation, H(x,(-r))=-H(x,r).
The empty case is 0=-0. For r=b::t, the induction
hypothesis gives H(x,-t)=-H(x,t), and then
-b+x*(-H(x,t))=-(b+x*H(x,t)) by distributivity.
These are finite structural inductions over all possible lists.
-/

namespace TarskiField

section FiniteHornerOddListIdentities

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem finiteHorner_append_last
    (x : F) (coeff : List F) (a : F) :
    finiteHornerValue x (coeff ++ [a]) =
      finiteHornerValue x coeff + a * x ^ coeff.length := by
  induction coeff with
  | nil =>
      simp [finiteHornerValue]
  | cons b rest ih =>
      change b + x * finiteHornerValue x (rest ++ [a]) =
        b + x * finiteHornerValue x rest +
          a * x ^ (rest.length + 1)
      rw [ih, pow_succ]
      ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem finiteHorner_neg_coeffs
    (x : F) (coeff : List F) :
    finiteHornerValue x (coeff.map (fun c => -c)) =
      -(finiteHornerValue x coeff) := by
  induction coeff with
  | nil =>
      simp [finiteHornerValue]
  | cons a rest ih =>
      change -a + x * finiteHornerValue x
        (rest.map (fun c => -c)) =
          -(a + x * finiteHornerValue x rest)
      rw [ih]
      ring

#print axioms TarskiField.finiteHorner_append_last
#print axioms TarskiField.finiteHorner_neg_coeffs

end FiniteHornerOddListIdentities

end TarskiField


/-!
## Construct opposite signs and the root of every finite odd-degree Horner list

The detailed, omission-free proof precedes this formalization in
proofs/FiniteHorner_OddDegree_CompleteProof.md on the parent branch.

Let coeff be the finite lower-coefficient list and let a be its
nonzero final coefficient. The target list is coeff ++ [a], with
coeff.length=2*k+1. Its degree is therefore odd. Define the
finite coefficient magnitude S and choose the internal witness
T=2+S/|a|. This is positive and >1, and the scalar inequality
S<T*|a| is obtained from a != 0 by finite ordered-field arithmetic.

The previously proved finite-Horner magnitude estimate gives
|H(±T,coeff)| ≤ S*T^(length(coeff)-1)
               < |a| * T^length(coeff).
The second inequality follows by multiplying S<T*|a|
by the strictly positive T^(length(coeff)-1).
The last-coefficient identity rewrites the full value as the
lower value plus a*(±T)^length(coeff). Odd parity makes
(-T)^length(coeff)=-T^length(coeff).

If a>0, the two estimates give H(-T,coeff++[a])<0
and H(T,coeff++[a])>0. If a<0, both signs reverse.
In the latter case negate each list coefficient. The already
proved list induction gives H(x,-coeff)=-H(x,coeff), so the
negated polynomial has the required negative-left/positive-right
signs. Apply the finite-polynomial IVT, and negate its zero
equation to obtain a zero of the original list.
These two cases exhaust a≠0; no Archimedean bound is used.
-/

namespace TarskiField

section FiniteHornerOddDegreeRoots

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Finite odd-degree Horner polynomial with nonzero leading coefficient
has a root from finite polynomial IVT, independent of Archimedeanness. -/
theorem finiteHorner_odd_root_of_IVT_append
    (hIVT : FiniteHornerIVT (F := F))
    (coeff : List F) (a : F) (k : Nat)
    (hlen : coeff.length = 2*k+1) (ha : a ≠ 0) :
    ∃ x : F, finiteHornerValue x (coeff ++ [a]) = 0 := by
  let S : F := finiteHornerCoeffAbsSum coeff
  have hS : 0 ≤ S :=
    finiteHornerCoeffAbsSum_nonneg coeff
  have hAbsA : 0 < |a| := abs_pos.mpr ha
  have hAbsANE : |a| ≠ 0 := ne_of_gt hAbsA
  let T : F := 2 + S / |a|
  have hRatio : 0 ≤ S / |a| :=
    div_nonneg hS (le_of_lt hAbsA)
  have hTpos : 0 < T := by
    dsimp [T]
    linarith
  have hTone : 1 ≤ T := by
    dsimp [T]
    linarith
  have hTidentity : |a| * T = 2 * |a| + S := by
    dsimp [T]
    field_simp [hAbsANE]
  have hLeading : S < |a| * T := by
    calc
      S < 2 * |a| + S := by linarith [hAbsA]
      _ = |a| * T := hTidentity.symm
  have hNonempty : coeff ≠ [] := by
    intro h
    simp [h] at hlen
  have hPowPos : 0 < T^(coeff.length-1) := pow_pos hTpos _
  have hExp : (coeff.length-1)+1 = coeff.length := by omega
  have hPowSucc : T^(coeff.length-1)*T = T^coeff.length := by
    rw [← pow_succ, hExp]
  have hDom :
      S*T^(coeff.length-1) < |a| * T^coeff.length := by
    calc
      S*T^(coeff.length-1) <
          (|a| * T)*T^(coeff.length-1) :=
        mul_lt_mul_of_pos_right hLeading hPowPos
      _ = |a| * T^coeff.length := by rw [← hPowSucc]; ring
  have hAtPos : |finiteHornerValue T coeff| <
      |a| * T^coeff.length := by
    have hAbsT : |T| ≤ T := by rw [abs_of_nonneg (le_of_lt hTpos)]
    exact lt_of_le_of_lt
      (finiteHorner_abs_le_coeffSum_mul_pow
        T hTone coeff hNonempty T hAbsT) hDom
  have hAtNeg : |finiteHornerValue (-T) coeff| <
      |a| * T^coeff.length := by
    have hAbsT : |(-T)| ≤ T := by
      rw [abs_neg, abs_of_nonneg (le_of_lt hTpos)]
    exact lt_of_le_of_lt
      (finiteHorner_abs_le_coeffSum_mul_pow
        T hTone coeff hNonempty (-T) hAbsT) hDom
  have hOddPower : (-T)^coeff.length = -(T^coeff.length) := by
    rw [hlen, pow_succ, pow_succ]
    have heven : (-T)^(2*k) = T^(2*k) := by
      calc
        (-T)^(2*k) = ((-T)^2)^k := by rw [pow_mul]
        _ = (T^2)^k := by congr 1; ring
        _ = T^(2*k) := by rw [pow_mul]
    rw [heven]
    ring
  have hInterval : -T < T := by linarith
  rcases lt_trichotomy a 0 with haNeg | haZero | haPos
  · have hAbsNeg : |a| = -a := abs_of_neg haNeg
    have hLeftOrig : 0 < finiteHornerValue (-T) (coeff ++ [a]) := by
      rw [finiteHorner_append_last, hOddPower]
      have hLow : -|finiteHornerValue (-T) coeff| ≤
          finiteHornerValue (-T) coeff :=
        neg_abs_le _
      rw [hAbsNeg] at hAtNeg
      nlinarith
    have hRightOrig : finiteHornerValue T (coeff ++ [a]) < 0 := by
      rw [finiteHorner_append_last]
      have hUp : finiteHornerValue T coeff ≤
          |finiteHornerValue T coeff| := le_abs_self _
      rw [hAbsNeg] at hAtPos
      nlinarith
    let coeffNeg : List F := (coeff ++ [a]).map (fun z => -z)
    have hLeft : finiteHornerValue (-T) coeffNeg < 0 := by
      dsimp [coeffNeg]
      rw [finiteHorner_neg_coeffs]
      exact neg_lt_zero.mpr hLeftOrig
    have hRight : 0 < finiteHornerValue T coeffNeg := by
      dsimp [coeffNeg]
      rw [finiteHorner_neg_coeffs]
      exact neg_pos.mpr hRightOrig
    obtain ⟨x, _, _, hx⟩ :=
      hIVT coeffNeg (-T) T hInterval hLeft hRight
    refine ⟨x, ?_⟩
    have hRoot : -(finiteHornerValue x (coeff ++ [a])) = 0 := by
      simpa only [coeffNeg, finiteHorner_neg_coeffs] using hx
    exact neg_eq_zero.mp hRoot
  · exact False.elim (ha haZero)
  · have hAbsPos : |a| = a := abs_of_pos haPos
    have hLeft : finiteHornerValue (-T) (coeff ++ [a]) < 0 := by
      rw [finiteHorner_append_last, hOddPower]
      have hUp : finiteHornerValue (-T) coeff ≤
          |finiteHornerValue (-T) coeff| := le_abs_self _
      rw [hAbsPos] at hAtNeg
      nlinarith
    have hRight : 0 < finiteHornerValue T (coeff ++ [a]) := by
      rw [finiteHorner_append_last]
      have hLow : -|finiteHornerValue T coeff| ≤
          finiteHornerValue T coeff := neg_abs_le _
      rw [hAbsPos] at hAtPos
      nlinarith
    obtain ⟨x, _, _, hx⟩ :=
      hIVT (coeff ++ [a]) (-T) T hInterval hLeft hRight
    exact ⟨x, hx⟩

#print axioms TarskiField.finiteHorner_odd_root_of_IVT_append

end FiniteHornerOddDegreeRoots

end TarskiField


/-!
## Remove the explicit append decomposition from the odd-degree theorem

Complete list proof: every nonempty list has a unique *last* element.
For [a], choose stem [] and last a. For b::tail with nonempty tail,
inductively write tail=stem++[a], then the whole list equals
(b::stem)++[a]. These are all cases of nonempty finite lists.

For a list c of length 2k+2, nonemptiness follows immediately since
2k+2>0. Choose its stem and last coefficient a as above. Then
stem.length+1=2k+2, and elementary arithmetic implies
stem.length=2k+1. The condition c.getLast? != some 0 and the
decomposition imply a!=0, because c.getLast?=some a.

The previously proved strict endpoint-sign and IVT theorem applies
to stem, a and k and produces a root of stem++[a]. This
list equals the original c, so that point is a root of c.
No unmentioned case remains; in particular the constant/empty
polynomial is excluded by the odd-degree length and leading
coefficient hypotheses rather than by an assumed analytic theorem.
-/

namespace TarskiField

section FiniteOddDegreeComplete

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Every nonempty list is a stem followed by one last element.
The proof is structural induction, including singleton and longer lists. -/
theorem finiteList_append_last_of_nonempty
    {α : Type*} (coeff : List α) (hne : coeff ≠ []) :
    ∃ (stem : List α) (last : α), coeff = stem ++ [last] := by
  induction coeff with
  | nil =>
      exact False.elim (hne rfl)
  | cons a rest ih =>
      cases rest with
      | nil =>
          exact ⟨[], a, rfl⟩
      | cons b tail =>
          obtain ⟨stem, last, hrest⟩ :=
            ih (by simp)
          refine ⟨a :: stem, last, ?_⟩
          simp [hrest]

/-- Every finite Horner list of odd degree and nonzero leading
coefficient has an internal scalar zero, assuming finite-Horner IVT. -/
theorem finiteHorner_odd_degree_root_of_IVT
    (hIVT : FiniteHornerIVT (F := F))
    (coeff : List F) (k : Nat)
    (hlen : coeff.length = 2*k+2)
    (hlast : coeff.getLast? ≠ some (0 : F)) :
    ∃ x : F, finiteHornerValue x coeff = 0 := by
  have hnonempty : coeff ≠ [] := by
    intro h
    simp [h] at hlen
  obtain ⟨stem, a, hdecomp⟩ :=
    finiteList_append_last_of_nonempty coeff hnonempty
  have hLast : coeff.getLast? = some a := by
    rw [hdecomp]
    simp
  have ha : a ≠ 0 := by
    intro h
    apply hlast
    rw [hLast, h]
  have hlenPre : stem.length = 2*k+1 := by
    have hLength : stem.length+1 = 2*k+2 := by
      simpa [hdecomp] using hlen
    omega
  obtain ⟨x, hx⟩ :=
    finiteHorner_odd_root_of_IVT_append
      hIVT stem a k hlenPre ha
  exact ⟨x, by simpa [hdecomp] using hx⟩

#print axioms TarskiField.finiteList_append_last_of_nonempty
#print axioms TarskiField.finiteHorner_odd_degree_root_of_IVT

end FiniteOddDegreeComplete

end TarskiField


/-!
## The zero-sum symmetry and geometric sign involution

**Complete synthetic proof.** The zero-output addition theorem identifies
`AddGraph f a b O` exactly with the Tarski midpoint statement
`Bet a O b ∧ Cong O a O b`. Reversing the endpoints of a midpoint
preserves both betweenness and segment congruence, so the zero-output graph
is symmetric even before general addition commutativity has been proved.

Every pair of axis points has a unique *geometric displacement* for the
`AddGraph` relation, by the independent synthetic parallel-projection
construction. Thus a zero-output sum `a+b=O` is precisely the assertion
that `b` is the chosen displacement from `a` to `O`, named
`axisNegOf f a`. Symmetry proves the *left* inverse
`AddGraph f (axisNegOf f a) a O`; the right inverse was constructed
earlier. No associative or commutative field law appears.

By definition, `AxisNegative f a` means that some positive axis point
`b` has `AddGraph f a b O`. The uniqueness just proved forces
`b=axisNegOf f a`; conversely the chosen opposite is always a
zero-sum witness. Hence the geometric opposite is positive exactly when
`a` is negative. Applying the already proved involution
`axisNegOf f (axisNegOf f a)=a` gives the reverse sign statement.
Finally the old `axisNegative_iff_opposite_ray_tarski` identifies the
same sign with the betweenness configuration `Bet a O I`.
All three possibilities (origin, positive, negative) are now compatible
with the canonical midpoint reflection. The proofs use only `Plane`
and the earlier verified synthetic constructions.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Zero-output geometric addition is symmetric, without a global
commutativity or associativity assumption. -/
theorem addGraph_zero_swap_tarski
    (f : Frame Point) (a b : AxisPoint f) :
    AddGraph f a b (axisZero f) ↔
      AddGraph f b a (axisZero f) := by
  constructor
  · intro hab
    exact (addGraph_zero_iff_midpoint_tarski f b a).2
      (mul_midpoint_reverse
        ((addGraph_zero_iff_midpoint_tarski f a b).1 hab))
  · intro hba
    exact (addGraph_zero_iff_midpoint_tarski f a b).2
      (mul_midpoint_reverse
        ((addGraph_zero_iff_midpoint_tarski f b a).1 hba))

/-- The unique geometrically constructed opposite is exactly
the second argument of every zero-output sum. -/
theorem addGraph_zero_iff_axisNegOf_tarski
    (f : Frame Point) (a b : AxisPoint f) :
    AddGraph f a b (axisZero f) ↔ b = axisNegOf f a := by
  constructor
  · intro hab
    exact (axisDisplacementOf_eq_of_graph
      f a (axisZero f) b hab).symm
  · intro hb
    rw [hb]
    exact axisNegOf_spec_tarski f a

/-- The already constructed right inverse is also a left inverse,
proved by the midpoint symmetry of the original geometric relation. -/
theorem axisNegOf_left_inverse_tarski
    (f : Frame Point) (a : AxisPoint f) :
    AddGraph f (axisNegOf f a) a (axisZero f) :=
  (addGraph_zero_swap_tarski f a (axisNegOf f a)).1
    (axisNegOf_spec_tarski f a)

/-- The geometric opposite of O is O. -/
theorem axisNegOf_zero_tarski (f : Frame Point) :
    axisNegOf f (axisZero f) = axisZero f := by
  simpa only [axisNegOf] using
    (axisDisplacementOf_self_tarski f (axisZero f))

/-- Geometric reflection is zero only at the origin. -/
theorem axisNegOf_eq_zero_iff_tarski
    (f : Frame Point) (a : AxisPoint f) :
    axisNegOf f a = axisZero f ↔ a = axisZero f := by
  constructor
  · intro ha
    have h := congrArg (axisNegOf f) ha
    simpa only [axisNegOf_involutive_tarski,
      axisNegOf_zero_tarski] using h
  · intro ha
    rw [ha]
    exact axisNegOf_zero_tarski f

/-- An axis point is negative iff its canonical opposite is positive. -/
theorem axisNegOf_positive_iff_axisNegative_tarski
    (f : Frame Point) (a : AxisPoint f) :
    Positive f (axisNegOf f a) ↔ AxisNegative f a := by
  constructor
  · intro hpositive
    exact ⟨axisNegOf f a, hpositive, axisNegOf_spec_tarski f a⟩
  · rintro ⟨b, hbpositive, hab⟩
    have hb : axisNegOf f a = b :=
      axisDisplacementOf_eq_of_graph f a (axisZero f) b hab
    simpa only [hb] using hbpositive

/-- Reflection swaps positive and negative signs in the reverse direction. -/
theorem axisNegOf_axisNegative_iff_positive_tarski
    (f : Frame Point) (a : AxisPoint f) :
    AxisNegative f (axisNegOf f a) ↔ Positive f a := by
  simpa only [axisNegOf_involutive_tarski] using
    (axisNegOf_positive_iff_axisNegative_tarski
      f (axisNegOf f a)).symm

/-- The geometric image is positive exactly when the original point lies
on the opposite open ray, expressed in the primitive Tarski betweenness. -/
theorem axisNegOf_positive_iff_opposite_ray_tarski
    (f : Frame Point) (a : AxisPoint f) :
    Positive f (axisNegOf f a) ↔
      a.1 ≠ f.O ∧ Bet a.1 f.O f.I :=
  (axisNegOf_positive_iff_axisNegative_tarski f a).trans
    (axisNegative_iff_opposite_ray_tarski f a)

/-- The signed cases of an axis point agree with its constructed
midpoint reflection, without any ordered-field structure. -/
theorem axisNegOf_sign_cases_tarski
    (f : Frame Point) (a : AxisPoint f) :
    a = axisZero f ∨
      (Positive f a ∧ AxisNegative f (axisNegOf f a)) ∨
      (AxisNegative f a ∧ Positive f (axisNegOf f a)) := by
  rcases axisSignTrichotomy_tarski f a with hzero | hpositive | hnegative
  · exact Or.inl hzero
  · exact Or.inr (Or.inl
      ⟨hpositive,
        (axisNegOf_axisNegative_iff_positive_tarski f a).2 hpositive⟩)
  · exact Or.inr (Or.inr
      ⟨hnegative,
        (axisNegOf_positive_iff_axisNegative_tarski f a).2 hnegative⟩)

#print axioms TarskiField.addGraph_zero_swap_tarski
#print axioms TarskiField.addGraph_zero_iff_axisNegOf_tarski
#print axioms TarskiField.axisNegOf_left_inverse_tarski
#print axioms TarskiField.axisNegOf_zero_tarski
#print axioms TarskiField.axisNegOf_eq_zero_iff_tarski
#print axioms TarskiField.axisNegOf_positive_iff_axisNegative_tarski
#print axioms TarskiField.axisNegOf_axisNegative_iff_positive_tarski
#print axioms TarskiField.axisNegOf_positive_iff_opposite_ray_tarski
#print axioms TarskiField.axisNegOf_sign_cases_tarski

end TarskiField


/-! SOURCE: workstreams/GeoCoqSumFunctionality.lean

## Tarski-only proof: functionality of the full GeoCoq sum diagram

Fix a noncollinear frame O,I,J and nonzero axis inputs x,y. Suppose the
five-projector GeoCoq sum diagram gives output z, with auxiliaries A,C.

(1) The first weak projector from x along IJ into A on OJ is strict.
If x=A, the two distinct axes OI and OJ intersect at x; the previously
proved axis-intersection theorem forces x=O, contrary to the premise.
Consequently IJ is parallel to xA and, by the Tarski line-uniqueness
theorem, A is uniquely determined by x. The same argument prevents A=O.

(2) C cannot equal A. If it did, C would belong to OJ. The third
projector from y in the OJ direction is either y=C, making y a point on OJ,
or is a parallel line yC through the common point C of OJ and yC. In the
latter case the two lines coincide, again putting y on OJ. As y is also
on OI, either alternative forces y=O, a contradiction. Thus the second
projector OI parallel to AC is strict.

(3) A is outside OI: it is on OJ and is not O. Hence the lines OI and AC
are disjoint by the existing Tarski-Playfair strict-parallel lemma. In
particular C is outside OI. Since y,z lie on OI, neither y=C nor C=z
is possible. The third and final weak projectors are therefore strict.

(4) Given two diagrams for identical x,y, the first auxiliary points
are equal by the already proved first projection uniqueness. Their second
auxiliaries agree by the already proved middle projection uniqueness,
because both must lie on the same OI-parallel and both are reached from y
in an OJ-parallel direction. Finally, the two output points z,w on OI
have parallel C-to-output lines in direction JI, with C off OI.
Tarski-Playfair uniqueness of oblique projection implies z=w.

For arbitrary x,y, the x=O and y=O cases follow from the separately
proved GeoCoq zero-output uniqueness lemmas. These cases exhaust all
possibilities, establishing functionality without assuming AddCommLaw,
AddAssocLaw, an external ordered field, Pappus, or A13.

Dependency: Tarski Bet/Cong, derived Playfair, line intersection uniqueness,
existing three projection uniqueness lemmas, and the already checked
zero-input GeoCoq sum proofs. No extra geometric assumption is introduced.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]

/-- Every weak projection in a GeoCoq sum with both inputs nonzero is in
fact a strict synthetic parallel projection. In particular, the middle
auxiliary point is outside the scalar axis. -/
theorem geoCoqSum_nonzero_strict_projections_tarski
    (f : Frame Point) (x y z : AxisPoint f)
    (hx : x.1 ≠ f.O) (hy : y.1 ≠ f.O)
    (hSum : GeoCoqSum f x y z) :
    ∃ A C : Point,
      Col f.O f.J A ∧
      Parallel f.I f.J x.1 A ∧
      Parallel f.O f.I A C ∧
      Parallel f.O f.J y.1 C ∧
      (¬ Col f.O f.I C) ∧
      Parallel f.J f.I C z.1 := by
  obtain ⟨A, C, hFirst, hAxis, hSecond, hThird, hLast⟩ := hSum
  have hxA : x.1 ≠ A := by
    intro h
    have hXOJ : Col f.O f.J x.1 := by
      rw [h]
      exact hAxis
    exact hx (frame_axes_intersection_only_origin_tarski f x.1 x.2 hXOJ)
  have hFirstPar : Parallel f.I f.J x.1 A := by
    rcases hFirst with hPar | hEq
    · exact hPar
    · exact False.elim (hxA hEq)
  have hAneO : A ≠ f.O :=
    geoCoq_firstPj_not_origin f x A hx hFirst
  have hAoffOI : ¬ Col f.O f.I A := by
    intro hAOI
    exact hAneO
      (frame_axes_intersection_only_origin_tarski f A hAOI hAxis)
  have hCneA : C ≠ A := by
    intro hCA
    have hCOJ : Col f.O f.J C := by
      rw [hCA]
      exact hAxis
    rcases hThird with hPar | hEq
    · have hSame : ∀ S, Col f.O f.J S ↔ Col y.1 C S :=
        parallel_same_of_intersection hPar hCOJ (col_right y.1 C)
      have hYOJ : Col f.O f.J y.1 :=
        (hSame y.1).mpr (col_left y.1 C)
      exact hy
        (frame_axes_intersection_only_origin_tarski f y.1 y.2 hYOJ)
    · have hYOJ : Col f.O f.J y.1 := by
        rw [hEq]
        exact hCOJ
      exact hy
        (frame_axes_intersection_only_origin_tarski f y.1 y.2 hYOJ)
  have hSecondPar : Parallel f.O f.I A C := by
    rcases hSecond with hPar | hEq
    · exact hPar
    · exact False.elim (hCneA hEq.symm)
  have hCoffOI : ¬ Col f.O f.I C := by
    have hDisjoint : ∀ S,
        ¬ (Col f.O f.I S ∧ Col A C S) :=
      playfair_strict_of_off_reference_tarski
        hSecondPar hAoffOI (col_left A C)
    intro hCOI
    exact hDisjoint C ⟨hCOI, col_right A C⟩
  have hyC : y.1 ≠ C := by
    intro h
    apply hCoffOI
    rw [← h]
    exact y.2
  have hThirdPar : Parallel f.O f.J y.1 C := by
    rcases hThird with hPar | hEq
    · exact hPar
    · exact False.elim (hyC hEq)
  have hCz : C ≠ z.1 := by
    intro h
    apply hCoffOI
    rw [h]
    exact z.2
  have hLastPar : Parallel f.J f.I C z.1 := by
    rcases hLast with hPar | hEq
    · exact hPar
    · exact False.elim (hCz hEq)
  exact ⟨A, C, hAxis, hFirstPar, hSecondPar,
    hThirdPar, hCoffOI, hLastPar⟩

/-- Functionality of the GeoCoq four-projection sum in the genuinely
nonzero case, with all weak-projector degeneracies eliminated. -/
theorem geoCoqSum_nonzero_functional_tarski
    (f : Frame Point) (x y z w : AxisPoint f)
    (hx : x.1 ≠ f.O) (hy : y.1 ≠ f.O)
    (hz : GeoCoqSum f x y z) (hw : GeoCoqSum f x y w) :
    z = w := by
  obtain ⟨A, C, hAaxis, hFirstA, hSecondA,
      hThirdA, hCoff, hFinalA⟩ :=
    geoCoqSum_nonzero_strict_projections_tarski f x y z hx hy hz
  obtain ⟨B, D, hBaxis, hFirstB, hSecondB,
      hThirdB, _, hFinalB⟩ :=
    geoCoqSum_nonzero_strict_projections_tarski f x y w hx hy hw
  have hAB : A = B :=
    geoCoqSum_first_projection_unique_tarski
      f x hx A B hAaxis hBaxis hFirstA hFirstB
  subst B
  have hAneO : A ≠ f.O :=
    geoCoq_firstPj_not_origin f x A hx (Or.inl hFirstA)
  have hAoff : ¬ Col f.O f.I A := by
    intro hAOI
    exact hAneO
      (frame_axes_intersection_only_origin_tarski f A hAOI hAaxis)
  have hCD : C = D :=
    geoCoqSum_middle_projections_unique_tarski
      f A y hAoff C D hSecondA hSecondB hThirdA hThirdB
  subst D
  have hLineExt : ∀ A B C D : Point,
      A ≠ B → C ≠ D → Col A B C → Col A B D →
      ∀ S, Col A B S ↔ Col C D S := by
    intro A B C D hAB hCD hC hD
    exact col_line_extensionality_tarski hAB hCD hC hD
  have hZW : z.1 = w.1 :=
    directional_projection_unique_of_playfair
      tarski_playfair hLineExt f.O f.I f.J f.I C z.1 w.1
      f.O_ne_I hCoff z.2 w.2 hFinalA hFinalB
  exact Subtype.ext hZW

/-- The original GeoCoq weak four-projector definition is a functional
relation for every pair of axis inputs. This is independent of any
unproved additive field law. -/
theorem geoCoqSum_functional_tarski (f : Frame Point) :
    ∀ x y z w : AxisPoint f,
      GeoCoqSum f x y z → GeoCoqSum f x y w → z = w := by
  intro x y z w hz hw
  by_cases hx0 : x = axisZero f
  · subst x
    exact (geoCoqSum_left_zero_unique_tarski f y z hz).trans
      (geoCoqSum_left_zero_unique_tarski f y w hw).symm
  by_cases hy0 : y = axisZero f
  · subst y
    exact (geoCoqSum_right_zero_unique_tarski f x z hz).trans
      (geoCoqSum_right_zero_unique_tarski f x w hw).symm
  have hx : x.1 ≠ f.O := by
    intro h
    exact hx0 (Subtype.ext h)
  have hy : y.1 ≠ f.O := by
    intro h
    exact hy0 (Subtype.ext h)
  exact geoCoqSum_nonzero_functional_tarski f x y z w hx hy hz hw

end TarskiField

#print axioms TarskiField.geoCoqSum_nonzero_strict_projections_tarski
#print axioms TarskiField.geoCoqSum_nonzero_functional_tarski
#print axioms TarskiField.geoCoqSum_functional_tarski



/-!
## Constructive geometric totality of GeoCoq addition

For x,y different from O, the existing Tarski proof constructs the unique
first IJ-direction projection A onto OJ. By the previously verified
parallelogram midpoint construction, it then constructs C such that AC is
parallel to OI and yC is parallel to OJ. Since A belongs to OJ and A != O,
A cannot belong to OI. The strict parallelism OI || AC consequently
forces C to lie outside OI.

The final GeoCoq projector from C to the scalar axis has direction JI.
It exists because JI is not parallel to OI (the two lines intersect at I
and are distinct by frame noncollinearity). The synthetic
weak_directional_projection_exists theorem constructs the intersection Z
of OI with the line through C in direction JI, with auxiliary point W.
As C lies off OI, C != Z. The line-extensionality theorem then replaces
the line CW by CZ, upgrading the weak projection to strict JI || CZ.
The witnesses A,C,Z satisfy all five projections of GeoCoqSum.

For the left- or right-zero inputs the verified explicit zero diagrams
supply witnesses directly. Functionality, proved independently above,
then upgrades total existence to unique existence for every axis pair.

This is a full synthetic construction. No AddGraph-GeoCoqSum bridge,
Pappus, algebraic field law, A13, or external coordinates are used.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]

/-- For two nonzero inputs every stage of the GeoCoq sum construction
exists, including the final transverse projection back onto OI. -/
theorem geoCoqSum_nonzero_exists_tarski
    (f : Frame Point) (x y : AxisPoint f)
    (hx : x.1 ≠ f.O) (hy : y.1 ≠ f.O) :
    ∃ z : AxisPoint f, GeoCoqSum f x y z := by
  obtain ⟨A, hFirst, hAxis⟩ :=
    geoCoqSum_first_projection_strong_tarski f x hx
  have hAneO : A ≠ f.O :=
    geoCoq_firstPj_not_origin f x A hx (Or.inl hFirst)
  obtain ⟨C, hHorizontal, hVertical⟩ :=
    geoCoqSum_middle_projections_exists_tarski
      f A hAxis hAneO y hy
  have hAoffOI : ¬ Col f.O f.I A := by
    intro hAOI
    exact hAneO
      (frame_axes_intersection_only_origin_tarski f A hAOI hAxis)
  have hCoffOI : ¬ Col f.O f.I C := by
    have hDisjoint : ∀ S,
        ¬ (Col f.O f.I S ∧ Col A C S) :=
      playfair_strict_of_off_reference_tarski
        hHorizontal hAoffOI (col_left A C)
    intro hCOI
    exact hDisjoint C ⟨hCOI, col_right A C⟩
  have hThrough : ∀ A B P : Point, A ≠ B →
      ∃ W : Point, Parallel A B P W := by
    intro A B P hAB
    exact parallel_through_any_point_tarski hAB
  have hTrans : ∀ {A B C D E F : Point},
      Parallel A B C D → Parallel C D E F → Parallel A B E F := by
    intro A B C D E F h1 h2
    exact parallel_trans_of_playfair tarski_playfair h1 h2
  have hTransverse : ¬ Parallel f.J f.I f.O f.I := by
    simpa [axisOne] using
      (frame_JX_not_parallel_OI f (axisOne f))
  obtain ⟨Z, hZaxis, W, hCW, hCZcol⟩ :=
    weak_directional_projection_exists hThrough hTrans
      f.O f.I f.J f.I C
      f.O_ne_I f.I_ne_J.symm hTransverse
  have hCZ : C ≠ Z := by
    intro h
    apply hCoffOI
    rw [h]
    exact hZaxis
  have hLine : ∀ S, Col C W S ↔ Col C Z S :=
    col_line_extensionality_tarski hCW.2.1 hCZ
      (col_left C W) hCZcol
  have hLast : Parallel f.J f.I C Z :=
    parallel_retarget_right_of_line_eq hCW hCZ hLine
  exact ⟨⟨Z, hZaxis⟩, A, C, Or.inl hFirst, hAxis,
    Or.inl hHorizontal, Or.inl hVertical, Or.inl hLast⟩

/-- Total, single-valued GeoCoq addition on the original Tarski axis. -/
theorem geoCoqSum_existsUnique_tarski (f : Frame Point) :
    ∀ x y : AxisPoint f,
      ∃! z : AxisPoint f, GeoCoqSum f x y z := by
  intro x y
  have hExists : ∃ z : AxisPoint f, GeoCoqSum f x y z := by
    by_cases hx0 : x = axisZero f
    · subst x
      exact ⟨y, geoCoqSum_left_zero_tarski f y⟩
    by_cases hy0 : y = axisZero f
    · subst y
      exact ⟨x, geoCoqSum_right_zero_tarski f x⟩
    have hx : x.1 ≠ f.O := by
      intro h
      exact hx0 (Subtype.ext h)
    have hy : y.1 ≠ f.O := by
      intro h
      exact hy0 (Subtype.ext h)
    exact geoCoqSum_nonzero_exists_tarski f x y hx hy
  obtain ⟨z, hz⟩ := hExists
  refine ⟨z, hz, ?_⟩
  intro w hw
  exact geoCoqSum_functional_tarski f x y w z hw hz

end TarskiField

#print axioms TarskiField.geoCoqSum_nonzero_exists_tarski
#print axioms TarskiField.geoCoqSum_existsUnique_tarski



/-!
## Reducing the full addition-graph identification to one directional lemma

Both Tarski AddGraph and GeoCoqSum are now proved total and functional on
all axis points. Their zero-input equivalences are also proved. Thus one
nonzero-input inclusion in either direction determines the entire relation.

Forward geometric route: given F asserting AddGraph(x,y,z) implies
GeoCoqSum(x,y,z) for x,y != O, the reverse follows by constructing w with
AddGraph(x,y,w), applying F, then invoking uniqueness of GeoCoqSum outputs.
Reverse geometric route: given R asserting GeoCoqSum(x,y,z) implies
AddGraph(x,y,z) for x,y != O, construct w with GeoCoqSum(x,y,w) and invoke
uniqueness of AddGraph outputs. In either route, the two zero branches are
discharged by existing concrete Tarski equivalences.

These two theorems are conditional *reductions*, not completed geometric
inclusions. Their hypotheses are explicit named local arguments. No
additional axiom or field law is introduced.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]

/-- One nonzero AddGraph-to-GeoCoqSum implication suffices for the entire
identification of the two total, single-valued Tarski relations. -/
theorem addGraph_iff_geoCoqSum_of_nonzero_forward_tarski
    (f : Frame Point)
    (hForward : ∀ x y z : AxisPoint f,
      x ≠ axisZero f → y ≠ axisZero f →
      AddGraph f x y z → GeoCoqSum f x y z)
    (x y z : AxisPoint f) :
    AddGraph f x y z ↔ GeoCoqSum f x y z := by
  by_cases hx : x = axisZero f
  · subst x
    exact addGraph_left_zero_iff_geoCoqSum_tarski f y z
  by_cases hy : y = axisZero f
  · subst y
    exact addGraph_right_zero_iff_geoCoqSum_tarski f x z
  constructor
  · exact hForward x y z hx hy
  · intro hGeo
    obtain ⟨w, hw, _⟩ := (operation_graphs_total_tarski f).1 x y
    have hwGeo : GeoCoqSum f x y w :=
      hForward x y w hx hy hw
    have hZW : z = w :=
      geoCoqSum_functional_tarski f x y z w hGeo hwGeo
    rw [hZW]
    exact hw

/-- Conversely, one nonzero GeoCoqSum-to-AddGraph implication also
suffices, because AddGraph was already proved a total functional graph. -/
theorem addGraph_iff_geoCoqSum_of_nonzero_reverse_tarski
    (f : Frame Point)
    (hReverse : ∀ x y z : AxisPoint f,
      x ≠ axisZero f → y ≠ axisZero f →
      GeoCoqSum f x y z → AddGraph f x y z)
    (x y z : AxisPoint f) :
    AddGraph f x y z ↔ GeoCoqSum f x y z := by
  by_cases hx : x = axisZero f
  · subst x
    exact addGraph_left_zero_iff_geoCoqSum_tarski f y z
  by_cases hy : y = axisZero f
  · subst y
    exact addGraph_right_zero_iff_geoCoqSum_tarski f x z
  constructor
  · intro hAdd
    obtain ⟨w, hwGeo, _⟩ := geoCoqSum_existsUnique_tarski f x y
    have hwAdd : AddGraph f x y w :=
      hReverse x y w hx hy hwGeo
    have hZW : z = w :=
      (operation_graphs_functional_tarski f).1 x y z w hAdd hwAdd
    rw [hZW]
    exact hwGeo
  · exact hReverse x y z hx hy

end TarskiField

#print axioms TarskiField.addGraph_iff_geoCoqSum_of_nonzero_forward_tarski
#print axioms TarskiField.addGraph_iff_geoCoqSum_of_nonzero_reverse_tarski


/-!
## GeoCoq's strict nonzero grid and the unique remaining synthetic bridge

Complete natural-language proof of strict-grid normal form:
The reverse implication is immediate: the five conjuncts of the strict
grid are witnesses for the four weak GeoCoq projectors and the OJ-axis
constraint. For the forward implication, fix a weak GeoCoq diagram with
x,y both nonzero. The proven strict projection theorem eliminates x=A,
A=C, y=C, and C=z using the two-axis uniqueness and disjointness of
parallel lines. The resulting A,C supply every strict conjunct,
including C outside OI.

Complete conditional proof of the last-parallel bridge:
Assume the single geometric grid-composition implication hFinal.
Take nonzero x,y and a strict AddGraph(x,y,z) with auxiliary point T.
Its three parallel conditions are fed unchanged to hFinal. Construct A
by the proven IJ projection of x to OJ. As x!=O, this is strict, and
the proof of first-projection nonzero gives A!=O. Construct C via the
proved midpoint-diagonal parallelogram: OI||AC, OJ||yC.
Apply hFinal to T,A,C, obtaining JI||Cz. Thus A,C witness
GeoCoqSum(x,y,z). By the previously proved global reduction,
this one forward inclusion implies the full equivalence, including
zero inputs, and proves its converse by uniqueness.

The hypothesis hFinal is *not* assumed as a field axiom. It is the
exact open incidence configuration to be derived from Tarski Bet/Cong,
equivalently the parallelogram-grid composition behind GeoCoq
Ch14_sum's sum_plg and plg_pseudo_trans. No claim of AddCommLaw is made.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]

/-- Exact strong-projection normal form of the GeoCoq sum diagram when
both scalar inputs are nonzero. This is a theorem of Tarski geometry,
not an added hypothesis. -/
theorem geoCoqSum_nonzero_iff_strictGrid_tarski
    (f : Frame Point) (x y z : AxisPoint f)
    (hx : x.1 ≠ f.O) (hy : y.1 ≠ f.O) :
    GeoCoqSum f x y z ↔
      ∃ A C : Point,
        Col f.O f.J A ∧
        Parallel f.I f.J x.1 A ∧
        Parallel f.O f.I A C ∧
        Parallel f.O f.J y.1 C ∧
        (¬ Col f.O f.I C) ∧
        Parallel f.J f.I C z.1 := by
  constructor
  · intro h
    exact geoCoqSum_nonzero_strict_projections_tarski f x y z hx hy h
  · rintro ⟨A, C, hAxis, hFirst, hSecond, hThird, _, hLast⟩
    exact ⟨A, C, Or.inl hFirst, hAxis,
      Or.inl hSecond, Or.inl hThird, Or.inl hLast⟩

/-- The entire AddGraph ↔ GeoCoqSum identification is reduced to one
precise final parallelism in two overlapping affine projector grids.
All other projections are already constructible from Tarski Bet/Cong.

The parameter hFinal is the outstanding *theorem target*, not a new
geometry axiom. If this incidence lemma is proved, the conclusion
needs no extra field or order hypotheses. -/
theorem addGraph_iff_geoCoqSum_of_final_parallel_tarski
    (f : Frame Point)
    (hFinal : ∀ (x y z : AxisPoint f) (T A C : Point),
      x.1 ≠ f.O → y.1 ≠ f.O →
      Parallel f.O f.J x.1 T →
      Parallel f.O f.I f.J T →
      Parallel f.J y.1 T z.1 →
      Col f.O f.J A →
      Parallel f.I f.J x.1 A →
      Parallel f.O f.I A C →
      Parallel f.O f.J y.1 C →
      Parallel f.J f.I C z.1)
    (x y z : AxisPoint f) :
    AddGraph f x y z ↔ GeoCoqSum f x y z := by
  have hForward : ∀ a b c : AxisPoint f,
      a ≠ axisZero f → b ≠ axisZero f →
      AddGraph f a b c → GeoCoqSum f a b c := by
    intro a b c ha0 hb0 hAdd
    have ha : a.1 ≠ f.O := by
      intro h
      exact ha0 (Subtype.ext h)
    have hb : b.1 ≠ f.O := by
      intro h
      exact hb0 (Subtype.ext h)
    rcases hAdd with ⟨h0, _⟩ | ⟨_, T, hVert, hHorz, hDiag⟩
    · exact False.elim (ha h0)
    obtain ⟨A, hFirst, hAxis⟩ :=
      geoCoqSum_first_projection_strong_tarski f a ha
    have hAne : A ≠ f.O :=
      geoCoq_firstPj_not_origin f a A ha (Or.inl hFirst)
    obtain ⟨C, hSecond, hThird⟩ :=
      geoCoqSum_middle_projections_exists_tarski
        f A hAxis hAne b hb
    have hLast : Parallel f.J f.I C c.1 :=
      hFinal a b c T A C ha hb hVert hHorz hDiag
        hAxis hFirst hSecond hThird
    exact ⟨A, C, Or.inl hFirst, hAxis,
      Or.inl hSecond, Or.inl hThird, Or.inl hLast⟩
  exact addGraph_iff_geoCoqSum_of_nonzero_forward_tarski
    f hForward x y z

end TarskiField

#print axioms TarskiField.geoCoqSum_nonzero_iff_strictGrid_tarski
#print axioms TarskiField.addGraph_iff_geoCoqSum_of_final_parallel_tarski


/-!
## General first-order A13 upper-bound cuts live on the original axis

The previous branch gpt-order-core-no-fixed-point proved this as a local
Tarski-only logical consequence, but its declaration was not carried into
the unified file. We restore the exact general theorem, not merely the
polynomial-specialized result already present.

Complete proof: the existing upperBounds_cut_A13_internal_scalar theorem
constructs the unique least upper-bound point B for any finite first-order
Formula 'lower', on condition that the interval's axis is closed.
The closure condition is already an unconditional Tarski Bet/Cong
consequence axisSegmentClosed_tarski. Substitute that theorem directly;
the resulting witness is a point of the original AxisPoint f by
segment closure, and uniqueness follows from the original A13
unique-bound result. No order field, arbitrary-subset completeness, or
independently assumed axis-closure condition is used.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]

/-- Tarski A13 gives a definable least upper bound on the *existing*
axis for every finite first-order formula satisfying the endpoint cut
hypotheses. This discharges the earlier line-closure interface. -/
theorem upperBounds_cut_A13_internal_scalar_tarski
    [ContinuousPlane Point]
    (f : Frame Point) {n : Nat}
    (l : Fin n) (lower : Formula (n + 1))
    (params : Fin n → Point) (R : Point)
    (hLaxis : Col f.O f.I (params l))
    (hRaxis : Col f.O f.I R)
    (hL : lower.eval (Fin.cons (params l) params))
    (hR : (upperBoundsFormula l lower).eval (Fin.cons R params)) :
    ∃! b : AxisPoint f,
      Plane.Bet (params l) b.1 R ∧
      (upperBoundsFormula l lower).eval (Fin.cons b.1 params) ∧
      ∀ Y : Point,
        (upperBoundsFormula l lower).eval (Fin.cons Y params) →
        Plane.Bet (params l) b.1 Y := by
  exact upperBounds_cut_A13_internal_scalar f l lower params R
    hLaxis hRaxis (axisSegmentClosed_tarski f) hL hR

end TarskiField

#print axioms TarskiField.upperBounds_cut_A13_internal_scalar_tarski


/-!
## GeoCoq plg_uniqueness: strict non-flat fourth-vertex case

Complete Tarski proof: Fix U,V,W with U,V,W noncollinear and two
quadrilaterals U,V,W,Z and U,V,W,Z'. Both have UV parallel to WZ (resp.
WZ') and VW parallel to ZU (resp. Z'U). For each, the previously
proved strictly nonflat parallelogram-diagonal lemma yields a midpoint
of UW that is simultaneously a midpoint of VZ, respectively VZ'.
Since the midpoint of a fixed segment UW is unique by Tarski
congruence and between-identity, both centers coincide. Reflection of
V about that fixed center is unique by the segment-construction axiom,
so Z and Z' coincide. The noncollinearity hypothesis excludes the
flat quadrilateral case; no extra algebraic assumption is used.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]

/-- Exact strict-parallelogram fourth vertex uniqueness required in the
nonflat branch of GeoCoq Annexes.quadrilaterals_inter_dec.plg_uniqueness. -/
theorem strict_parallelogram_fourth_vertex_unique_tarski
    {U V W Z Z' : Point}
    (htri : ¬ Col U V W)
    (hUV : Parallel U V W Z)
    (hVW : Parallel V W Z U)
    (hUV' : Parallel U V W Z')
    (hVW' : Parallel V W Z' U) :
    Z = Z' := by
  have hFirst : ∃ M : Point,
      MulMidpoint M U W ∧ MulMidpoint M V Z :=
    parallelogram_diagonal_midpoint_exists_tarski htri hUV hVW
  have hSecond : ∃ N : Point,
      MulMidpoint N U W ∧ MulMidpoint N V Z' :=
    parallelogram_diagonal_midpoint_exists_tarski htri hUV' hVW'
  exact diagonal_midpoints_fourth_vertex_unique_tarski hFirst hSecond

end TarskiField

#print axioms TarskiField.strict_parallelogram_fourth_vertex_unique_tarski


/-!
## GeoCoq flat parallelograms: constructive common midpoint and uniqueness

Natural-language proof: proofs/GeoCoq_flat_parallelogram_midpoint_complete.md
This is the exact five-conjunct GeoCoq Parallelogram_flat on Tarski points.

If A=C, nondegeneracy gives B!=D; Col(B,D,A) and AB == AD
force A to be the midpoint of BD, while A is trivially a midpoint of AA.

If A!=C, construct midpoint M of AC and reflect B across M to B'.
Reflection sends collinear A,B,C to C,B',A; B' lies on AC.
Congruence preservation gives AB == CB' and CB == AB'.
Combined with AB == CD and AD == CB, this yields
AB' == AD and CB' == CD. Two-station congruence propagation
at collinear B' forces B'B' == B'D and hence B'=D.
Therefore M also bisects BD.

Two common midpoints of AC coincide, so reflection uniqueness
determines the fourth vertex. The strict/flat union is functional,
since mixed cases violate Col(A,B,C) versus its negation.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- The exact five conjuncts of GeoCoq Parallelogram_flat. -/
def GeoCoqFlatParallelogram (A B C D : Point) : Prop :=
  Col A B C ∧ Col A B D ∧
    Cong A B C D ∧ Cong A D C B ∧
    (A ≠ C ∨ B ≠ D)

/-- A GeoCoq flat parallelogram has a common midpoint of its diagonals
in the original Tarski plane, including the degenerate A=C case. -/
theorem geoCoqFlatParallelogram_midpoint_tarski
    {A B C D : Point}
    (h : GeoCoqFlatParallelogram A B C D) :
    ∃ M : Point, MulMidpoint M A C ∧ MulMidpoint M B D := by
  rcases h with ⟨hColABC, hColABD, hABCD, hADCB, hNontrivial⟩
  by_cases hAC : A = C
  · subst C
    have hBD : B ≠ D := by
      rcases hNontrivial with hAneA | hBneD
      · exact False.elim (hAneA rfl)
      · exact hBneD
    have hColBDA : Col B D A := col_rotate hColABD
    have hMidBD : MulMidpoint A B D := by
      rcases col_equidistant_midpoint_or_eq_tarski hColBDA hABCD with heq | hmid
      · exact False.elim (hBD heq)
      · exact hmid
    exact ⟨A, ⟨bet_end A A, congr_refl A A⟩, hMidBD⟩
  · obtain ⟨M, hMAC⟩ := midpoint_existence_tarski A C
    obtain ⟨B', hMBB', _⟩ := mul_reflection_exists_unique M B
    have hMCA : MulMidpoint M C A := mul_midpoint_reverse hMAC
    have hMB'B : MulMidpoint M B' B := mul_midpoint_reverse hMBB'
    have hColCB'A : Col C B' A :=
      mul_reflection_preserves_col hMAC hMBB' hMCA hColABC
    have hColACB' : Col A C B' :=
      col_rotate (col_rotate hColCB'A)
    have hAB_CB' : Cong A B C B' :=
      mul_reflection_preserves_cong hMCA hMB'B
    have hCB_AB' : Cong C B A B' :=
      mul_reflection_preserves_cong hMAC hMB'B
    have hCB'_CD : Cong C B' C D :=
      cong_trans (cong_symm hAB_CB') hABCD
    have hAB'_AD : Cong A B' A D :=
      cong_trans (cong_symm hCB_AB') (cong_symm hADCB)
    have hAtB' : Cong B' B' B' D :=
      col_equidistant_of_two_stations hAC hColACB'
        hAB'_AD hCB'_CD
    have hB'D : B' = D :=
      cong_identity B' D B' (cong_symm hAtB')
    have hMBD : MulMidpoint M B D := by
      simpa only [← hB'D] using hMBB'
    exact ⟨M, hMAC, hMBD⟩

/-- Flat fourth-vertex uniqueness. -/
theorem geoCoqFlatParallelogram_fourth_vertex_unique_tarski
    {A B C D D' : Point}
    (hD : GeoCoqFlatParallelogram A B C D)
    (hD' : GeoCoqFlatParallelogram A B C D') :
    D = D' :=
  diagonal_midpoints_fourth_vertex_unique_tarski
    (geoCoqFlatParallelogram_midpoint_tarski hD)
    (geoCoqFlatParallelogram_midpoint_tarski hD')

/-- Synthetic union of strict opposite-parallel and flat quadrilaterals. -/
def TarskiParallelQuadrilateral (A B C D : Point) : Prop :=
  (¬ Col A B C ∧ Parallel A B C D ∧ Parallel B C D A) ∨
    GeoCoqFlatParallelogram A B C D

/-- The fourth vertex is unique in either strict or flat cases,
and mixed cases contradict collinearity. -/
theorem tarskiParallelQuadrilateral_fourth_vertex_unique_tarski
    {A B C D D' : Point}
    (hD : TarskiParallelQuadrilateral A B C D)
    (hD' : TarskiParallelQuadrilateral A B C D') :
    D = D' := by
  rcases hD with hStrict | hFlat
  · rcases hD' with hStrict' | hFlat'
    · exact strict_parallelogram_fourth_vertex_unique_tarski
        hStrict.1 hStrict.2.1 hStrict.2.2
        hStrict'.2.1 hStrict'.2.2
    · exact False.elim (hStrict.1 hFlat'.1)
  · rcases hD' with hStrict' | hFlat'
    · exact False.elim (hStrict'.1 hFlat.1)
    · exact geoCoqFlatParallelogram_fourth_vertex_unique_tarski
        hFlat hFlat'

end TarskiField

#print axioms TarskiField.geoCoqFlatParallelogram_midpoint_tarski
#print axioms TarskiField.geoCoqFlatParallelogram_fourth_vertex_unique_tarski
#print axioms TarskiField.tarskiParallelQuadrilateral_fourth_vertex_unique_tarski

/-!
## GeoCoq directed-segment bridge: exact adjacent-bet step

The natural proof in
proofs/Tarski_RealClosedAxis_NaturalProof_SINGLE_20261123.md, §3.3.1,
uses the GeoCoq construction of a directed vector from a strict or flat
parallelogram.  The local Tarski representations below introduce no
primitive operation or new axiom.  The same-direction relation is
defined by the original geometric disjunction, and the adjacent
betweenness result is proved from its witness.

The stronger statement
  TarskiSameDir A B B C -> Bet A B C
avoids a later case split between two directions of an Out ray.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- An equal directed displacement: a synthetic parallelogram or two
    zero segments.  The parallelogram component is the already derived
    Tarski strict/flat union. -/
def TarskiEqV (A B C D : Point) : Prop :=
  TarskiParallelQuadrilateral A B D C ∨
    (A = B ∧ C = D)

/-- The same ray direction, with the zero-vector branch explicit.
    This matches the branching structure of GeoCoq's Same_dir. -/
def TarskiSameDir (A B C D : Point) : Prop :=
  (A = B ∧ C = D) ∨
    ∃ D' : Point, Out C D D' ∧ TarskiEqV A B C D'

/-- Adjacent equal vectors share a midpoint; the strict
    parallelogram case is impossible when its second and fourth
    vertices coincide. -/
theorem tarskiEqV_adjacent_midpoint_tarski
    {A B D : Point} (h : TarskiEqV A B B D) :
    MulMidpoint B A D := by
  rcases h with hQuad | hNull
  · rcases hQuad with hStrict | hFlat
    · have hLine : ∀ X : Point, Col B D X ↔ Col B A X :=
        parallel_same_of_intersection hStrict.2.2
          (col_left B D) (col_left B A)
      have hColBAD : Col B A D := (hLine D).mp (col_right B D)
      exact False.elim (hStrict.1 (col_swap hColBAD))
    · obtain ⟨M, hMidAD, hMidBB⟩ :=
        geoCoqFlatParallelogram_midpoint_tarski hFlat
      have hBM : B = M := between_identity B M hMidBB.1
      subst M
      exact hMidAD
  · rcases hNull with ⟨hAB, hBD⟩
    subst A
    subst D
    exact ⟨bet_end B B, congr_refl B B⟩

/-- Formalized GeoCoq eqv_mid + Out argument:
    forward-adjacent segments in the same direction are ordered
    by Tarski's primitive betweenness. -/
theorem tarskiSameDir_adjacent_bet_tarski
    {A B C : Point} (h : TarskiSameDir A B B C) :
    Bet A B C := by
  rcases h with ⟨hAB, hBC⟩ | ⟨D', hOut, hEqV⟩
  · subst A
    subst C
    exact bet_end B B
  · have hMid : MulMidpoint B A D' :=
      tarskiEqV_adjacent_midpoint_tarski hEqV
    rcases hOut with ⟨_, hDB, hCase⟩
    rcases hCase with hBCD | hBDC
    · exact bet_inner_trans hMid.1 hBCD
    · have hADC : Bet A D' C :=
        bet_outer_trans hMid.1 hBDC hDB.symm
      exact bet_extend hMid.1 hADC

end TarskiField

#print axioms TarskiField.tarskiEqV_adjacent_midpoint_tarski
#print axioms TarskiField.tarskiSameDir_adjacent_bet_tarski

/-!
## GeoCoq directed-segment degeneracy and opposite-direction exclusion

These are the remaining elementary zero/opposite branches from the
natural-language proof §3.3.1.  They use only the existing definitions
of TarskiEqV, TarskiSameDir, Col, MulMidpoint and the Tarski lemmas
already proved in this file.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- A directed displacement equal to a zero segment must itself be
    zero.  This is GeoCoq's null_vector branch in the Lean
    strict/flat-parallelogram representation. -/
theorem tarskiEqV_zero_left_tarski
    {A C D : Point} (h : TarskiEqV A A C D) : C = D := by
  rcases h with hQuad | hNull
  · rcases hQuad with hStrict | hFlat
    · have hcol : Col A A D := Or.inl (bet_start A D)
      exact False.elim (hStrict.1 hcol)
    · have hDC : D = C :=
        cong_identity D C A (cong_symm hFlat.2.2.1)
      exact hDC.symm
  · exact hNull.2

/-- Same_dir cannot have exactly one zero directed segment:
    the representative point would violate the nonzero Out condition. -/
theorem tarskiSameDir_null_tarski
    {A C D : Point} (h : TarskiSameDir A A C D) :
    C = D := by
  rcases h with hNull | ⟨D', hOut, hEqV⟩
  · exact hNull.2
  · have hCD' : C = D' := tarskiEqV_zero_left_tarski hEqV
    exact False.elim (hOut.2.1 hCD'.symm)

/-- GeoCoq same_dir_id: an oriented segment cannot have the same
    direction as its reversal unless its endpoints coincide. -/
theorem tarskiSameDir_id_tarski
    {A B : Point} (h : TarskiSameDir A B B A) :
    A = B := by
  rcases h with hNull | ⟨D', hOut, hEqV⟩
  · exact hNull.1
  · have hMid : MulMidpoint B A D' :=
      tarskiEqV_adjacent_midpoint_tarski hEqV
    rcases hOut with ⟨_, hDB, hCase⟩
    rcases hCase with hBAD | hBDA
    · exact bet_swap_endpoint_eq hMid.1 hBAD
    · have hBD : B = D' :=
        bet_swap_endpoint_eq hBDA (bet_symm hMid.1)
      exact False.elim (hDB hBD.symm)

end TarskiField

#print axioms TarskiField.tarskiEqV_zero_left_tarski
#print axioms TarskiField.tarskiSameDir_null_tarski
#print axioms TarskiField.tarskiSameDir_id_tarski
/-!
## Directed segments: unconditional midpoint bridge and the exact axis-order interface

Natural-language master §3.3: EqV(A,B,C,D) is first reduced to a
common midpoint for AD and BC, using the existing strict and flat
parallelogram theorems.  SameDir on the distinguished axis then
produces a *positive axis point* and the precise midpoint witness
for the reverse direction of the additive characterization K.

The final order step is deliberately conditional on K's reverse
direction.  This is a theorem parameter, not a new Plane field or
a claim that the outstanding addition bridge is already proved.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Every equal directed displacement has the corresponding diagonal
midpoints.  Both strict and flat quadrilaterals, as well as the
two-zero-segment case, are included without any extra field axiom. -/
theorem tarskiEqV_common_midpoint_tarski
    {A B C D : Point} (h : TarskiEqV A B C D) :
    ∃ M : Point, MulMidpoint M A D ∧ MulMidpoint M B C := by
  rcases h with hQuad | ⟨hAB, hCD⟩
  · rcases hQuad with hStrict | hFlat
    · exact parallelogram_diagonal_midpoint_exists_tarski
        hStrict.1 hStrict.2.1 hStrict.2.2
    · exact geoCoqFlatParallelogram_midpoint_tarski hFlat
  · subst B
    subst D
    obtain ⟨M, hMid⟩ := midpoint_existence_tarski A C
    exact ⟨M, hMid, hMid⟩

/-- A same-direction axis segment provides a positive axis displacement
and the exact common midpoint demanded by the reverse addition bridge K.
This theorem is unconditional; it does not use AddGraph. -/
theorem tarskiSameDir_axis_positive_common_midpoint_tarski
    (f : Frame Point) {a b : AxisPoint f}
    (h : TarskiSameDir a.1 b.1 f.O f.I) :
    ∃ d : AxisPoint f, Positive f d ∧
      ∃ M : Point,
        MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1 := by
  rcases h with ⟨_, hOI⟩ | ⟨D, hOut, hEqV⟩
  · exact False.elim (f.O_ne_I hOI)
  · let d : AxisPoint f := ⟨D, out_implies_col hOut⟩
    obtain ⟨M, hAD, hBO⟩ :=
      tarskiEqV_common_midpoint_tarski hEqV
    exact ⟨d, hOut, M, mul_midpoint_reverse hBO, hAD⟩

/-- Exact dependency of the SameDir -> AxisLt direction:
only the reverse common-midpoint/addition characterization K remains.
No reverse implication is claimed without its geometric proof. -/
theorem axisLt_of_tarskiSameDir_of_midpoint_bridge_tarski
    (f : Frame Point)
    (hKrev : ∀ a d b : AxisPoint f,
      (∃ M : Point,
        MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1) →
      AddGraph f a d b)
    {a b : AxisPoint f}
    (h : TarskiSameDir a.1 b.1 f.O f.I) :
    AxisLt f a b := by
  obtain ⟨d, hd, M, hOB, hAD⟩ :=
    tarskiSameDir_axis_positive_common_midpoint_tarski f h
  exact ⟨d, hKrev a d b ⟨M, hOB, hAD⟩, hd⟩

end TarskiField

#print axioms TarskiField.tarskiEqV_common_midpoint_tarski
#print axioms TarskiField.tarskiSameDir_axis_positive_common_midpoint_tarski
#print axioms TarskiField.axisLt_of_tarskiSameDir_of_midpoint_bridge_tarski
/-!
## Positive-axis midpoint quadrilaterals are flat directed vectors

This closes the forward axis-order direction at the level of geometry:
once a positive displacement has the common-midpoint witness Q,
its corresponding flat parallelogram and hence SameDir are proved
without GeoCoq's general parallelogram equivalence theorem.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- General midpoint-to-EqV converse, including non-flat quadrilaterals,
flat quadrilaterals, and the two-zero-segment case.  It is derived
solely from Tarski midpoint reflection and the proved diagonal
parallelism theorem, without any group or field laws. -/
theorem tarskiEqV_of_common_midpoint_tarski
    {A B C D : Point}
    (hQ : ∃ M : Point,
      MulMidpoint M A D ∧ MulMidpoint M B C) :
    TarskiEqV A B C D := by
  obtain ⟨M, hAD, hBC⟩ := hQ
  by_cases hAB : A = B
  · subst B
    obtain ⟨X, _, huniq⟩ := mul_reflection_exists_unique M A
    have hDX : D = X := huniq D hAD
    have hCX : C = X := huniq C hBC
    exact Or.inr ⟨rfl, hCX.trans hDX.symm⟩
  · by_cases hABD : Col A B D
    · have hColM : Col A B M :=
        col_segment_closed_tarski
          hAB (col_left A B) hABD hAD.1
      have hColC : Col A B C := by
        by_cases hBM : B = M
        · have hCong : Cong B B B C := by
            simpa only [← hBM] using hBC.2
          have hBCeq : B = C :=
            cong_identity B C B (cong_symm hCong)
          simpa only [← hBCeq] using (col_right A B)
        · have hline : ∀ X : Point,
              Col A B X ↔ Col B M X :=
            col_line_extensionality_tarski
              hAB hBM (col_right A B) hColM
          exact (hline C).mpr (Or.inl hBC.1)
      have hABDC : Cong A B D C :=
        mul_reflection_preserves_cong
          (mul_midpoint_reverse hAD) (mul_midpoint_reverse hBC)
      have hACDB : Cong A C D B :=
        mul_reflection_preserves_cong
          (mul_midpoint_reverse hAD) hBC
      have hNontrivial : A ≠ D ∨ B ≠ C := by
        by_cases haD : A = D
        · right
          intro hbC
          have haM : A = M :=
            between_identity A M (by
              simpa only [← haD] using hAD.1)
          have hbM : B = M :=
            between_identity B M (by
              simpa only [← hbC] using hBC.1)
          exact hAB (haM.trans hbM.symm)
        · exact Or.inl haD
      exact Or.inl (Or.inr
        ⟨hABD, hColC, hABDC, hACDB, hNontrivial⟩)
    · have hNotColABC : ¬ Col A B C := by
        intro hABC
        have hColM : Col A B M :=
          col_segment_closed_tarski
            hAB (col_right A B) hABC hBC.1
        by_cases hAM : A = M
        · have hCong : Cong A A A D := by
            simpa only [← hAM] using hAD.2
          have hAD_eq : A = D :=
            cong_identity A D A (cong_symm hCong)
          exact hABD (by simpa only [← hAD_eq] using (col_left A B))
        · have hline : ∀ X : Point,
              Col A B X ↔ Col A M X :=
            col_line_extensionality_tarski
              hAB hAM (col_left A B) hColM
          exact hABD ((hline D).mpr (Or.inl hAD.1))
      obtain ⟨hPar1, hPar2⟩ :=
        midpoint_diagonals_parallelogram_tarski
          hNotColABC hBC hAD
      exact Or.inl (Or.inl ⟨hABD, hPar1, hPar2⟩)

/-- Complete exact equivalence of GeoCoq directed-segment equality and
the common-midpoint (diagonal) relation, without a nonzero restriction. -/
theorem tarskiEqV_iff_common_midpoint_tarski
    {A B C D : Point} :
    TarskiEqV A B C D ↔
      ∃ M : Point, MulMidpoint M A D ∧ MulMidpoint M B C :=
  ⟨tarskiEqV_common_midpoint_tarski,
    tarskiEqV_of_common_midpoint_tarski⟩

/-- Complete transport of any directed segment AB to start at C.
Take the midpoint of BC and reflect A across it; the unique
reflective image is the endpoint D.  No parallelogram composition is
used, and the construction covers zero directed segments. -/
theorem tarskiEqV_transport_exists_unique_tarski
    (A B C : Point) :
    ∃! D : Point, TarskiEqV A B C D := by
  obtain ⟨M, hBC⟩ := midpoint_existence_tarski B C
  obtain ⟨D, hAD, huniq⟩ := mul_reflection_exists_unique M A
  refine ⟨D, tarskiEqV_of_common_midpoint_tarski
    ⟨M, hAD, hBC⟩, ?_⟩
  intro D' hEqV
  obtain ⟨N, hAD', hBC'⟩ :=
    tarskiEqV_common_midpoint_tarski hEqV
  have hMN : M = N :=
    mul_midpoint_center_unique_tarski hBC hBC'
  have hAD'M : MulMidpoint M A D' := by
    simpa only [hMN] using hAD'
  exact huniq D' hAD'M

/-- GeoCoq eqv_sym, now simply reversal of the two midpoint diagonals. -/
theorem tarskiEqV_sym_tarski
    {A B C D : Point} (h : TarskiEqV A B C D) :
    TarskiEqV C D A B := by
  obtain ⟨M, hAD, hBC⟩ :=
    tarskiEqV_common_midpoint_tarski h
  exact tarskiEqV_of_common_midpoint_tarski
    ⟨M, mul_midpoint_reverse hBC, mul_midpoint_reverse hAD⟩

/-- GeoCoq eqv_comm: reverse both vectors, without any new axiom. -/
theorem tarskiEqV_comm_tarski
    {A B C D : Point} (h : TarskiEqV A B C D) :
    TarskiEqV B A D C := by
  obtain ⟨M, hAD, hBC⟩ :=
    tarskiEqV_common_midpoint_tarski h
  exact tarskiEqV_of_common_midpoint_tarski ⟨M, hBC, hAD⟩

/-- GeoCoq eqv_refl, including the A=B case. -/
theorem tarskiEqV_refl_tarski (A B : Point) :
    TarskiEqV A B A B := by
  obtain ⟨M, hAB⟩ := midpoint_existence_tarski A B
  exact tarskiEqV_of_common_midpoint_tarski
    ⟨M, hAB, mul_midpoint_reverse hAB⟩

#print axioms TarskiField.tarskiEqV_transport_exists_unique_tarski
#print axioms TarskiField.tarskiEqV_sym_tarski
#print axioms TarskiField.tarskiEqV_comm_tarski
#print axioms TarskiField.tarskiEqV_refl_tarski

/-- The axis-specific SameDir bridge is now a direct specialization
of the unconditional general midpoint/EqV equivalence; positivity
is needed only to supply the ray, not for the EqV construction. -/
theorem tarskiEqV_of_positive_axis_common_midpoint_tarski
    (f : Frame Point) (a b d : AxisPoint f)
    (_hd : Positive f d)
    (hQ : ∃ M : Point,
       MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1) :
    TarskiEqV a.1 b.1 f.O d.1 := by
  obtain ⟨M, hOB, hAD⟩ := hQ
  exact tarskiEqV_of_common_midpoint_tarski
    ⟨M, hAD, mul_midpoint_reverse hOB⟩

#print axioms TarskiField.tarskiEqV_of_common_midpoint_tarski
#print axioms TarskiField.tarskiEqV_iff_common_midpoint_tarski

/-- One direction of the ordered-axis bridge, conditional only on the
forward AddGraph -> Q characterization K. -/
theorem tarskiSameDir_of_axisLt_of_midpoint_bridge_tarski
    (f : Frame Point)
    (hKforward : ∀ a d b : AxisPoint f,
      AddGraph f a d b →
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    {a b : AxisPoint f} (h : AxisLt f a b) :
    TarskiSameDir a.1 b.1 f.O f.I := by
  obtain ⟨d, hAdd, hd⟩ := h
  have hEqV : TarskiEqV a.1 b.1 f.O d.1 :=
    tarskiEqV_of_positive_axis_common_midpoint_tarski
      f a b d hd (hKforward a d b hAdd)
  exact Or.inr ⟨d.1, hd, hEqV⟩

/-- Exact order/SameDir equivalence using only the two directions of K.
No field law or ordered-field instance appears as a hypothesis. -/
theorem axisLt_iff_tarskiSameDir_of_midpoint_characterization_tarski
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (a b : AxisPoint f) :
    AxisLt f a b ↔ TarskiSameDir a.1 b.1 f.O f.I := by
  constructor
  · exact tarskiSameDir_of_axisLt_of_midpoint_bridge_tarski
      f (fun a d b h => (hK a d b).mp h)
  · exact axisLt_of_tarskiSameDir_of_midpoint_bridge_tarski
      f (fun a d b h => (hK a d b).mpr h)

end TarskiField

#print axioms TarskiField.tarskiEqV_of_positive_axis_common_midpoint_tarski
#print axioms TarskiField.tarskiSameDir_of_axisLt_of_midpoint_bridge_tarski
#print axioms TarskiField.axisLt_iff_tarskiSameDir_of_midpoint_characterization_tarski
/-!
## Bet -> direction: direct reflection proof without vector construction

The natural-language master §3.3.1 now gives the explicit B-centered
reflection witness for GeoCoq bet_same_dir2.  Both related implications
below are unconditional geometry theorems.  In particular no additive
midpoint characterization K or ordered-field law is used.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- GeoCoq bet_same_dir1, obtained with the flat reflexive directed
segment and the Bet-defined ray. -/
theorem tarskiSameDir_of_bet_same_origin_tarski
    {A B C : Point}
    (hAB : A ≠ B) (_hBC : B ≠ C) (hABC : Bet A B C) :
    TarskiSameDir A B A C := by
  have hAC : A ≠ C := by
    intro h
    have hABA : Bet A B A := by simpa only [← h] using hABC
    exact hAB (between_identity A B hABA)
  have hOut : Out A C B :=
    ⟨hAC.symm, hAB.symm, Or.inr hABC⟩
  have hEqV : TarskiEqV A B A B :=
    tarskiEqV_refl_tarski A B
  exact Or.inr ⟨B, hOut, hEqV⟩

/-- GeoCoq bet_same_dir2 by reflection of A in B: the reflected
point D is on the same ray from B as C by Tarski's betweenness
comparability, and (A,B,D,B) is a flat parallelogram. -/
theorem tarskiSameDir_of_bet_same_start_tarski
    {A B C : Point}
    (hAB : A ≠ B) (hBC : B ≠ C) (hABC : Bet A B C) :
    TarskiSameDir A B B C := by
  obtain ⟨D, hMid, _⟩ := mul_reflection_exists_unique B A
  have hBD : B ≠ D := by
    intro h
    have hCong : Cong B A B B := by
      simpa only [← h] using hMid.2
    have hBA : B = A := cong_identity B A B hCong
    exact hAB hBA.symm
  have hOut : Out B C D :=
    ⟨hBC.symm, hBD.symm,
      ray_bet_comparable_after_station hAB hABC hMid.1⟩
  have hAD : A ≠ D := by
    intro h
    have hABA : Bet A B A := by simpa only [← h] using hMid.1
    exact hAB (between_identity A B hABA)
  have hCong : Cong A B D B := cong_reverse_both hMid.2
  have hEqV : TarskiEqV A B B D := by
    exact Or.inl (Or.inr
      ⟨Or.inl hMid.1, col_right A B,
        hCong, hCong, Or.inl hAD⟩)
  exact Or.inr ⟨D, hOut, hEqV⟩

end TarskiField

#print axioms TarskiField.tarskiSameDir_of_bet_same_origin_tarski
#print axioms TarskiField.tarskiSameDir_of_bet_same_start_tarski
/-!
## Complete AxisDirectedBetOrder from addition K, commutativity and associativity

For an oriented interval a<c, reflection in the common midpoint of the
addition quadrilateral gives b<=c by primitive Bet alone.  Central
reflection at O reverses the derived strict order by the additive
group laws: this transports the same argument to a<=b.  Consequently
the general GeoCoq Same_dir symmetry/transitivity theorems are no
longer dependencies of the A13 order bridge.

The three proof parameters hK, hComm, hAssoc are precisely previously
identified geometrical proof obligations, not extra Plane axioms.
-/
namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- The upper comparison of a primitive betweenness interval is
proved by reflecting its intermediate point in the sum quadrilateral.
This half of AxisDirectedBetOrder needs only the two directions of K:
no SameDir symmetry, transitivity, or additive law is required. -/
theorem axisLe_right_of_axisLt_bet_midpoint_tarski
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    {a b c : AxisPoint f}
    (hAC : AxisLt f a c)
    (hBet : Bet a.1 b.1 c.1) :
    AxisLe f b c := by
  obtain ⟨d, hAddAC, hdPos⟩ := hAC
  obtain ⟨M, hOC, hAD⟩ := (hK a d c).mp hAddAC
  obtain ⟨E, hMBE, _⟩ := mul_reflection_exists_unique M b.1
  have hDEO : Bet d.1 E f.O :=
    mul_reflection_preserves_bet
      hAD hMBE (mul_midpoint_reverse hOC) hBet
  have hOED : Bet f.O E d.1 := bet_symm hDEO
  have hEaxis : Col f.O f.I E :=
    col_segment_closed_tarski
      f.O_ne_I (col_left f.O f.I) d.2 hOED
  let e : AxisPoint f := ⟨E, hEaxis⟩
  by_cases hEO : E = f.O
  · have hMbO : MulMidpoint M b.1 f.O := by
      simpa only [hEO] using hMBE
    have hBC : b.1 = c.1 :=
      mul_reflection_involution hMbO hOC
    exact Or.inl (Subtype.ext hBC)
  · have hOut : Out f.O d.1 E :=
      ⟨hdPos.2.1, hEO, Or.inr hOED⟩
    have hePos : Positive f e :=
      out_trans_tarski hdPos hOut
    have hAddBC : AddGraph f b e c :=
      (hK b e c).mpr ⟨M, hOC, hMBE⟩
    exact Or.inr ⟨e, hAddBC, hePos⟩

/-- The canonical midpoint-reflection opposite reverses the geometric
strict order as soon as the two pending additive group laws are proved.
The SAME positive displacement witnesses both inequalities. -/
theorem axisNegOf_order_reverse_of_addCommAssoc_tarski
    (f : Frame Point)
    (hComm : AddCommLaw f) (hAssoc : AddAssocLaw f)
    {a c : AxisPoint f}
    (hAC : AxisLt f a c) :
    AxisLt f (axisNegOf f c) (axisNegOf f a) := by
  obtain ⟨d, hAddAC, hdPos⟩ := hAC
  obtain ⟨t, hNcD, _⟩ :=
    (operation_graphs_total_tarski f).1 (axisNegOf f c) d
  obtain ⟨u, hTa, _⟩ :=
    (operation_graphs_total_tarski f).1 t a
  have hDaC : AddGraph f d a c :=
    hComm a d c hAddAC
  have hNcC : AddGraph f (axisNegOf f c) c (axisZero f) :=
    axisNegOf_left_inverse_tarski f c
  have huZero : u = axisZero f :=
    hAssoc (axisNegOf f c) d a t c u (axisZero f)
      hNcD hTa hDaC hNcC
  have hTaZero : AddGraph f t a (axisZero f) := by
    simpa only [huZero] using hTa
  have hAtZero : AddGraph f a t (axisZero f) :=
    (addGraph_zero_swap_tarski f t a).mp hTaZero
  have htNegA : t = axisNegOf f a :=
    (addGraph_zero_iff_axisNegOf_tarski f a t).mp hAtZero
  refine ⟨d, ?_, hdPos⟩
  change AddGraph f (axisNegOf f c) d (axisNegOf f a)
  simpa only [htNegA] using hNcD

/-- Full directed betweenness/order interface by upper-half reflection,
then order reversal through the origin.  Only K, AddComm, AddAssoc and
already proved Tarski reflection facts are needed; both general
SameDir symmetry and transitivity have been eliminated. -/
theorem axisDirectedBetOrder_of_midpoint_addLaws_tarski
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hComm : AddCommLaw f)
    (hAssoc : AddAssocLaw f) :
    AxisDirectedBetOrder f := by
  intro a b c hAC hBet
  have hRight : AxisLe f b c :=
    axisLe_right_of_axisLt_bet_midpoint_tarski f hK hAC hBet
  have hNegAC : AxisLt f (axisNegOf f c) (axisNegOf f a) :=
    axisNegOf_order_reverse_of_addCommAssoc_tarski
      f hComm hAssoc hAC
  have hRefBet :
      Bet (axisNegOf f a).1
          (axisNegOf f b).1
          (axisNegOf f c).1 :=
    mul_reflection_preserves_bet
      (axisNegOf_midpoint_tarski f a)
      (axisNegOf_midpoint_tarski f b)
      (axisNegOf_midpoint_tarski f c) hBet
  have hNegRight : AxisLe f (axisNegOf f b) (axisNegOf f a) :=
    axisLe_right_of_axisLt_bet_midpoint_tarski
      f hK hNegAC (bet_symm hRefBet)
  have hLeft : AxisLe f a b := by
    rcases hNegRight with hEq | hLt
    · have hBA : b = a := by
        have hh := congrArg (axisNegOf f) hEq
        simpa only [axisNegOf_involutive_tarski] using hh
      exact Or.inl hBA.symm
    · have hLt' :
          AxisLt f
            (axisNegOf f (axisNegOf f a))
            (axisNegOf f (axisNegOf f b)) :=
        axisNegOf_order_reverse_of_addCommAssoc_tarski
          f hComm hAssoc hLt
      have hAB : AxisLt f a b := by
        simpa only [axisNegOf_involutive_tarski] using hLt'
      exact Or.inr hAB
  exact ⟨hLeft, hRight⟩

end TarskiField

#print axioms TarskiField.axisLe_right_of_axisLt_bet_midpoint_tarski
#print axioms TarskiField.axisNegOf_order_reverse_of_addCommAssoc_tarski
#print axioms TarskiField.axisDirectedBetOrder_of_midpoint_addLaws_tarski
/-!
## Positive closure of addition: midpoint-and-ray proof

The canonical natural proof §3.2 reduces positive addition to only
the *forward* geometric K midpoint bridge.  Once that bridge is proved
in Lean, no independent port of GeoCoq l14_36_a/b or plg_bet1 is needed.

All midpoint, ray and Bet results used below are already unconditional
theorems of Plane.  The hKforward parameter exposes the sole unproved
dependency and does not add a field or a Tarski geometry axiom.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

theorem positiveAddClosed_of_midpoint_forward_tarski
    (f : Frame Point)
    (hKforward : ∀ a b c : AxisPoint f,
      AddGraph f a b c →
        ∃ M : Point,
          MulMidpoint M f.O c.1 ∧ MulMidpoint M a.1 b.1) :
    PositiveAddClosed f := by
  intro a b c ha hb hAdd
  obtain ⟨M, hOC, hAB⟩ := hKforward a b c hAdd
  have habRay : Out f.O a.1 b.1 :=
    out_trans_tarski (out_swap_tarski ha) hb
  have hOM : Out f.O f.I M := by
    rcases habRay.2.2 with hOAB | hOBA
    · have hOAM : Bet f.O a.1 M :=
        bet_inner_trans hOAB hAB.1
      have hMne : M ≠ f.O := by
        intro hMeq
        have hOA : f.O = a.1 :=
          between_identity f.O a.1 (by simpa [hMeq] using hOAM)
        exact ha.2.1 hOA.symm
      have hOaM : Out f.O a.1 M :=
        ⟨ha.2.1, hMne, Or.inl hOAM⟩
      exact out_trans_tarski ha hOaM
    · have hOBM : Bet f.O b.1 M :=
        bet_inner_trans hOBA (bet_symm hAB.1)
      have hMne : M ≠ f.O := by
        intro hMeq
        have hOB : f.O = b.1 :=
          between_identity f.O b.1 (by simpa [hMeq] using hOBM)
        exact hb.2.1 hOB.symm
      have hObM : Out f.O b.1 M :=
        ⟨hb.2.1, hMne, Or.inl hOBM⟩
      exact out_trans_tarski hb hObM
  have hcNe : c.1 ≠ f.O := by
    intro hc
    have hOMeq : f.O = M :=
      between_identity f.O M (by simpa [hc] using hOC.1)
    exact hOM.2.1 hOMeq.symm
  exact out_trans_tarski hOM
    ⟨hOM.2.1, hcNe, Or.inl hOC.1⟩

end TarskiField

#print axioms TarskiField.positiveAddClosed_of_midpoint_forward_tarski
/-!
## Semantic elimination for same-origin directed rays

The exact GeoCoq Same_dir relation on two segments with the same
starting point reduces to Out, except for the joint zero-vector case.
Uniqueness of vector transport is already derived from the complete
EqV/common-midpoint equivalence.  No general Same_dir symmetry or
transitivity, and no addition law, is used here.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Equal directed vectors have the same (unoriented) segment length:
both segments are reflected images of each other about their common
midpoint, with endpoints reversed in the second segment. -/
theorem tarskiEqV_cong_tarski
    {A B C D : Point} (h : TarskiEqV A B C D) :
    Cong A B C D := by
  obtain ⟨M, hAD, hBC⟩ :=
    tarskiEqV_common_midpoint_tarski h
  exact cong_reverse_right
    (cong_symm (mul_reflection_preserves_cong hAD hBC))

/-- Exact zero-aware reduction of SameDir when its two directed
segments have the same origin. -/
theorem tarskiSameDir_same_origin_iff_tarski
    (A B D : Point) :
    TarskiSameDir A B A D ↔
      ((A = B ∧ A = D) ∨ Out A B D) := by
  constructor
  · intro h
    rcases h with hZero | ⟨D', hOut, hEqV⟩
    · exact Or.inl hZero
    · obtain ⟨E, _, hUnique⟩ :=
        tarskiEqV_transport_exists_unique_tarski A B A
      have hBE : B = E :=
        hUnique B (tarskiEqV_refl_tarski A B)
      have hDE : D' = E := hUnique D' hEqV
      have hDB : D' = B := hDE.trans hBE.symm
      exact Or.inr
        (out_swap_tarski (by simpa only [hDB] using hOut))
  · intro h
    rcases h with hZero | hRay
    · exact Or.inl hZero
    · exact Or.inr
        ⟨B, out_swap_tarski hRay, tarskiEqV_refl_tarski A B⟩

end TarskiField

#print axioms TarskiField.tarskiEqV_cong_tarski
#print axioms TarskiField.tarskiSameDir_same_origin_iff_tarski
/-!
## Directed difference is an axis point before the additive K bridge

The natural master §3.3 proves that EqV preserves a containing
nondegenerate line, by reflection of three collinear points.
The unique transported vector from scalar a to scalar b, placed
at the origin O, is therefore again on the original OI axis.

These theorems need only the already verified Bet/Cong midpoint
and collinearity results, not AddGraph, geometric associativity,
an ordered field, or continuity.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- If a directed vector AB is transported to CD, and A,B,C are
collinear, then D is on that same line.  All A=B and B=C degeneracies
are discharged before applying the nondegenerate line theorem. -/
theorem tarskiEqV_collinear_closure_tarski
    {A B C D : Point}
    (h : TarskiEqV A B C D)
    (hABC : Col A B C) :
    Col A B D := by
  obtain ⟨M, hAD, hBC⟩ :=
    tarskiEqV_common_midpoint_tarski h
  by_cases hAB : A = B
  · subst B
    have hCD : C = D := tarskiEqV_zero_left_tarski h
    rw [← hCD]
    exact hABC
  · by_cases hBCeq : B = C
    · have hBM : B = M :=
        between_identity B M
          (by simpa only [← hBCeq] using hBC.1)
      have hABD : Bet A B D := by
        simpa only [← hBM] using hAD.1
      exact Or.inl hABD
    · have hDCB : Col D C B :=
        mul_reflection_preserves_col
          hAD hBC (mul_midpoint_reverse hBC) hABC
      have hCBD : Col C B D := col_rotate hDCB
      have hline : ∀ X : Point,
          Col A B X ↔ Col C B X :=
        col_line_extensionality_tarski
          hAB (Ne.symm hBCeq) hABC (col_right A B)
      exact (hline D).mpr hCBD

/-- Every axis segment a -> b has a unique transported directed
difference O -> d which lies on that same axis.  In particular this
construction does not rely on the still-open addition midpoint
equivalence K. -/
theorem tarskiEqV_axis_transport_exists_unique_tarski
    (f : Frame Point) (a b : AxisPoint f) :
    ∃! d : AxisPoint f, TarskiEqV a.1 b.1 f.O d.1 := by
  obtain ⟨D, hEqV, hUnique⟩ :=
    tarskiEqV_transport_exists_unique_tarski a.1 b.1 f.O
  have hAxis : Col f.O f.I D := by
    by_cases hab : a.1 = b.1
    · have hZero : TarskiEqV a.1 a.1 f.O D := by
        simpa only [← hab] using hEqV
      have hOD : f.O = D := tarskiEqV_zero_left_tarski hZero
      simpa only [← hOD] using (col_left f.O f.I)
    · have hline : ∀ X : Point,
          Col f.O f.I X ↔ Col a.1 b.1 X :=
        col_line_extensionality_tarski
          f.O_ne_I hab a.2 b.2
      have hABO : Col a.1 b.1 f.O :=
        (hline f.O).mp (col_left f.O f.I)
      have hABD : Col a.1 b.1 D :=
        tarskiEqV_collinear_closure_tarski hEqV hABO
      exact (hline D).mpr hABD
  refine ⟨⟨D, hAxis⟩, hEqV, ?_⟩
  intro d hd
  apply Subtype.ext
  exact hUnique d.1 hd

end TarskiField

#print axioms TarskiField.tarskiEqV_collinear_closure_tarski
#print axioms TarskiField.tarskiEqV_axis_transport_exists_unique_tarski
/-!
## The reverse Bet/order implication without vector direction lemmas

After deriving the upper and lower bounds by midpoint and origin
reflection, collinearity itself has precisely three primitive-Bet
branches.  The other two force equality through antisymmetry of the
internally defined scalar order and hence contradict the two strict
bounds.  This gives the exact equivalence needed for A13's cut formula
without any external ordered-field structure or GeoCoq Same_dir laws.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

theorem axisBet_iff_directedBounds_of_addLaws_tarski
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hComm : AddCommLaw f)
    (hAssoc : AddAssocLaw f)
    {a b c : AxisPoint f}
    (hAC : AxisLt f a c) :
    Bet a.1 b.1 c.1 ↔ AxisLe f a b ∧ AxisLe f b c := by
  have hOrder : AxisDirectedBetOrder f :=
    axisDirectedBetOrder_of_midpoint_addLaws_tarski
      f hK hComm hAssoc
  have hPos : PositiveAddClosed f :=
    positiveAddClosed_of_midpoint_forward_tarski
      f (fun x y z hAdd => (hK x y z).mp hAdd)
  constructor
  · exact hOrder a b c hAC
  · rintro ⟨hLeAB, hLeBC⟩
    rcases hLeAB with habEq | habLt
    · subst b
      exact bet_start a.1 c.1
    rcases hLeBC with hbcEq | hbcLt
    · subst c
      exact bet_end a.1 b.1
    have habv : a.1 ≠ b.1 :=
      fun hv => (axisLt_ne_tarski f habLt) (Subtype.ext hv)
    have hline : ∀ X : Point,
        Col f.O f.I X ↔ Col a.1 b.1 X :=
      col_line_extensionality_tarski
        f.O_ne_I habv a.2 b.2
    have hABCCol : Col a.1 b.1 c.1 :=
      (hline c.1).mp c.2
    rcases hABCCol with hABC | hBCA | hCAB
    · exact hABC
    · have hACB : Bet a.1 c.1 b.1 := bet_symm hBCA
      have hCB : AxisLe f c b :=
        (hOrder a c b habLt hACB).2
      have hBCeq : b = c :=
        axisLe_antisymm_of_addAssoc_posClosed_tarski
          f hAssoc hPos (Or.inr hbcLt) hCB
      exact False.elim ((axisLt_ne_tarski f hbcLt) hBCeq)
    · have hBAC : Bet b.1 a.1 c.1 := bet_symm hCAB
      have hBA : AxisLe f b a :=
        (hOrder b a c hbcLt hBAC).1
      have hABeq : a = b :=
        axisLe_antisymm_of_addAssoc_posClosed_tarski
          f hAssoc hPos (Or.inr habLt) hBA
      exact False.elim ((axisLt_ne_tarski f habLt) hABeq)

end TarskiField

#print axioms TarskiField.axisBet_iff_directedBounds_of_addLaws_tarski
/-!
## Canonical field structure on the original Tarski scalar axis

Natural proof §3.3.2 (ten minimal field axioms).  All operations in
the constructed instance are precisely the previously chosen unique
outputs of AddGraph and MulGraph.  Zero, one and the additive opposite
are original geometric points and central midpoint reflection.

The inverse function selects the unique multiplicative-inverse graph
witness for nonzero inputs and maps zero to zero.  The only outstanding
hypotheses needed to build a Field are the actual geometric add
associativity, mul commutativity/associativity, and left distributivity.
No external coordinate field is used.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Multiplicative inverse chosen from the already verified geometric
MulInverseLaw; zero has the customary definitional inverse zero. -/
noncomputable def axisInvOf_tarski
    (f : Frame Point) (x : AxisPoint f) : AxisPoint f := by
  classical
  exact if hx : x = axisZero f then axisZero f
    else Classical.choose ((mulKernel_tarski f).2.2.2 x hx)

/-- Every nonzero axis point multiplies its chosen geometric inverse
to the original frame unit I. -/
theorem axisInvOf_mul_spec_tarski
    (f : Frame Point) (x : AxisPoint f)
    (hx : x ≠ axisZero f) :
    MulGraph f x (axisInvOf_tarski f x) (axisOne f) := by
  simpa only [axisInvOf_tarski, dite_eq_right hx] using
    (Classical.choose_spec ((mulKernel_tarski f).2.2.2 x hx))

theorem axisInvOf_zero_tarski
    (f : Frame Point) :
    axisInvOf_tarski f (axisZero f) = axisZero f := by
  simp [axisInvOf_tarski]

/-- A Field structure on the *same axis points*, built by exactly ten
minimal algebraic laws.  Its Add and Mul operations are the original
Tarski graph operations; the four indicated relational laws remain
explicit inputs until their geometric Lean proofs are finished. -/
@[instance_reducible] noncomputable def axisFieldOfGeometricLaws_tarski
    (f : Frame Point)
    (hAddAssoc : AddAssocLaw f)
    (hMulComm : MulCommLaw f)
    (hMulAssoc : MulAssocLaw f)
    (hDistrib : LeftDistributiveLaw f) :
    Field (AxisPoint f) := by
  let hAdd : AddTotal f := (operation_graphs_total_tarski f).1
  let hMul : MulTotal f := (operation_graphs_total_tarski f).2
  letI : Add (AxisPoint f) := ⟨axisAddOf f hAdd⟩
  letI : Mul (AxisPoint f) := ⟨axisMulOf f hMul⟩
  letI : Neg (AxisPoint f) := ⟨axisNegOf f⟩
  letI : Inv (AxisPoint f) := ⟨axisInvOf_tarski f⟩
  letI : Zero (AxisPoint f) := ⟨axisZero f⟩
  letI : One (AxisPoint f) := ⟨axisOne f⟩
  apply Field.ofMinimalAxioms (AxisPoint f)
  · intro x y z
    change axisAddOf f hAdd (axisAddOf f hAdd x y) z =
      axisAddOf f hAdd x (axisAddOf f hAdd y z)
    exact axisAddOf_assoc_of_law f hAdd hAddAssoc x y z
  · intro x
    change axisAddOf f hAdd (axisZero f) x = x
    exact axisAddOf_zero_left f hAdd x
  · intro x
    change axisAddOf f hAdd (axisNegOf f x) x = axisZero f
    exact (addGraph_iff_axisAddOf_eq
      f hAdd (axisNegOf f x) x (axisZero f)).mp
        (axisNegOf_left_inverse_tarski f x)
  · intro x y z
    change axisMulOf f hMul (axisMulOf f hMul x y) z =
      axisMulOf f hMul x (axisMulOf f hMul y z)
    exact axisMulOf_assoc_of_law f hMul hMulAssoc x y z
  · intro x y
    change axisMulOf f hMul x y = axisMulOf f hMul y x
    exact axisMulOf_comm_of_law f hMul hMulComm x y
  · intro x
    change axisMulOf f hMul (axisOne f) x = x
    exact axisMulOf_one_left_of_law
      f hMul (mulKernel_tarski f).2.2.1 x
  · intro x hx
    change axisMulOf f hMul x (axisInvOf_tarski f x) = axisOne f
    exact (mulGraph_iff_axisMulOf_eq
      f hMul x (axisInvOf_tarski f x) (axisOne f)).mp
        (axisInvOf_mul_spec_tarski f x hx)
  · change axisInvOf_tarski f (axisZero f) = axisZero f
    exact axisInvOf_zero_tarski f
  · intro x y z
    change axisMulOf f hMul x (axisAddOf f hAdd y z) =
      axisAddOf f hAdd
        (axisMulOf f hMul x y) (axisMulOf f hMul x z)
    exact axisMulOf_left_distrib_of_law
      f hAdd hMul hDistrib x y z
  · exact ⟨axisZero f, axisOne f, axisZero_ne_axisOne f⟩

end TarskiField

#print axioms TarskiField.axisInvOf_mul_spec_tarski
#print axioms TarskiField.axisFieldOfGeometricLaws_tarski
/-!
## Lean LinearOrder on the geometrically interpreted axis

Natural master §3.3.3: the relation AxisLt itself, not a coordinate
comparison, is made into a strict total order.  The Tarski proof of
irreflexivity is unconditional; trichotomy requires only AddAssoc,
while transitivity additionally uses PositiveAddClosed, itself
derived from the forward midpoint bridge K.

This constructor uses neither the generic ordered-field laws nor
the multiplication graph or continuity.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- The existing geometric strict comparison yields a genuine
Lean LinearOrder on the same AxisPoint carrier as soon as K and
associativity are proved geometrically.  The order relation is
definitionally the original AxisLt, rather than imported ℝ order. -/
@[instance_reducible] noncomputable def axisLinearOrderOfMidpointAddAssoc_tarski
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hAssoc : AddAssocLaw f) :
    LinearOrder (AxisPoint f) := by
  have hPositiveAdd : PositiveAddClosed f :=
    positiveAddClosed_of_midpoint_forward_tarski
      f (fun a d b h => (hK a d b).mp h)
  letI : IsStrictTotalOrder (AxisPoint f) (AxisLt f) := {
    irrefl := fun x => axisLt_irrefl_tarski f x
    trans := fun a b c hab hbc =>
      axisLt_trans_of_addAssoc_posClosed_tarski
        f hAssoc hPositiveAdd hab hbc
    trichotomous := by
      intro a b hab hba
      rcases axisLt_trichotomy_of_addAssoc_tarski f hAssoc a b with
        heq | hlt | hgt
      · exact heq
      · exact False.elim (hab hlt)
      · exact False.elim (hba hgt)
  }
  letI : DecidableRel (AxisLt f) := Classical.decRel _
  exact linearOrderOfSTO (AxisLt f)

end TarskiField

#print axioms TarskiField.axisLinearOrderOfMidpointAddAssoc_tarski
/-!
## The ordered-ring interface on the very same Tarski axis

Natural master §3.3.4 derives the additive strict monotonicity
from a positive geometric displacement and AddAssoc, then derives
closure of multiplication on strictly positive axis points from
the exact PositiveMulClosed relational goal.  The field and order
structures below are the previously constructed geometric ones.

Nothing is assumed about external numeric coordinates or about a
preexisting ordered-field instance on AxisPoint.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Construct ordered-ring compatibility, conditional on exactly the
still outstanding geometric K and field/positive-multiplication
theorems.  This creates no new axioms or unrelated scalar structure. -/
theorem axisStrictOrderedRingOfGeometricLaws_tarski
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hAddAssoc : AddAssocLaw f)
    (hMulComm : MulCommLaw f)
    (hMulAssoc : MulAssocLaw f)
    (hDistrib : LeftDistributiveLaw f)
    (hPosMul : PositiveMulClosed f) :
    letI : Field (AxisPoint f) :=
      axisFieldOfGeometricLaws_tarski
        f hAddAssoc hMulComm hMulAssoc hDistrib
    letI : LinearOrder (AxisPoint f) :=
      axisLinearOrderOfMidpointAddAssoc_tarski f hK hAddAssoc
    IsStrictOrderedRing (AxisPoint f) := by
  letI : Field (AxisPoint f) :=
    axisFieldOfGeometricLaws_tarski
      f hAddAssoc hMulComm hMulAssoc hDistrib
  letI : LinearOrder (AxisPoint f) :=
    axisLinearOrderOfMidpointAddAssoc_tarski f hK hAddAssoc
  let hAdd : AddTotal f := (operation_graphs_total_tarski f).1
  let hMul : MulTotal f := (operation_graphs_total_tarski f).2
  have hAddStrict : ∀ t x y : AxisPoint f,
      x < y → t + x < t + y := by
    intro t x y hxy
    change AxisLt f x y at hxy
    obtain ⟨d, hSub, hdPos⟩ := hxy
    change AddGraph f x d y at hSub
    have hXdY : x + d = y :=
      (addGraph_iff_axisAddOf_eq f hAdd x d y).mp hSub
    change AxisLt f (t + x) (t + y)
    refine ⟨d, ?_, hdPos⟩
    change AddGraph f (t + x) d (t + y)
    apply (addGraph_iff_axisAddOf_eq
      f hAdd (t + x) d (t + y)).mpr
    calc
      (t + x) + d = t + (x + d) := add_assoc t x d
      _ = t + y := congrArg (fun z => t + z) hXdY
  letI : IsOrderedCancelAddMonoid (AxisPoint f) :=
    IsOrderedCancelAddMonoid.of_add_lt_add_left hAddStrict
  letI : ZeroLEOneClass (AxisPoint f) := ⟨by
    change AxisLe f (axisZero f) (axisOne f)
    exact Or.inr
      ((axisLt_zero_iff_positive_tarski f (axisOne f)).mpr
        (axisOne_positive f))⟩
  apply IsStrictOrderedRing.of_mul_pos
  intro x y hx hy
  have hxPos : Positive f x := by
    change AxisLt f (axisZero f) x at hx
    exact (axisLt_zero_iff_positive_tarski f x).mp hx
  have hyPos : Positive f y := by
    change AxisLt f (axisZero f) y at hy
    exact (axisLt_zero_iff_positive_tarski f y).mp hy
  have hProd : MulGraph f x y (x * y) := by
    change MulGraph f x y (axisMulOf f hMul x y)
    exact axisMulOf_spec f hMul x y
  have hProdPos : Positive f (x * y) :=
    hPosMul x y (x * y) hxPos hyPos hProd
  change AxisLt f (axisZero f) (x * y)
  exact (axisLt_zero_iff_positive_tarski f (x * y)).mpr hProdPos

end TarskiField

#print axioms TarskiField.axisStrictOrderedRingOfGeometricLaws_tarski
/-!
## Exact finite Horner bridge on the original Tarski scalar carrier

The natural master §3.3.5 proves by induction that the uniquely
defined HornerGraph result coincides with ordinary finiteHornerValue
once the geometric Field structure has been constructed.  This
identity keeps all future A13 sign arguments on the very same axis;
it imports neither real numbers nor an external coordinate model.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

theorem tarskiHornerValue_eq_finiteHornerValue_of_geomField_tarski
    (f : Frame Point)
    (hAddAssoc : AddAssocLaw f)
    (hMulComm : MulCommLaw f)
    (hMulAssoc : MulAssocLaw f)
    (hDistrib : LeftDistributiveLaw f)
    (x : AxisPoint f) (coeff : List (AxisPoint f)) :
    letI : Field (AxisPoint f) :=
      axisFieldOfGeometricLaws_tarski
        f hAddAssoc hMulComm hMulAssoc hDistrib
    tarskiHornerValue f x coeff = finiteHornerValue x coeff := by
  letI : Field (AxisPoint f) :=
    axisFieldOfGeometricLaws_tarski
      f hAddAssoc hMulComm hMulAssoc hDistrib
  let hAdd : AddTotal f := (operation_graphs_total_tarski f).1
  let hMul : MulTotal f := (operation_graphs_total_tarski f).2
  induction coeff with
  | nil =>
    have hZero : tarskiHornerValue f x [] = axisZero f :=
      tarskiHornerValue_spec f x []
    exact hZero
  | cons a rest ih =>
    have hGraph :
        HornerGraph f x (a :: rest)
          (tarskiHornerValue f x (a :: rest)) :=
      tarskiHornerValue_spec f x (a :: rest)
    change ∃ t u : AxisPoint f,
        HornerGraph f x rest t ∧
        MulGraph f x t u ∧
        AddGraph f a u (tarskiHornerValue f x (a :: rest))
      at hGraph
    obtain ⟨t, u, hRest, hMulGraph, hAddGraph⟩ := hGraph
    have htEq : t = tarskiHornerValue f x rest :=
      ((tarskiHornerValue_eq_iff_graph f x rest t).mpr hRest).symm
    have huEq : u = x * t :=
      ((mulGraph_iff_axisMulOf_eq f hMul x t u).mp hMulGraph).symm
    have hzEq :
        tarskiHornerValue f x (a :: rest) = a + u :=
      ((addGraph_iff_axisAddOf_eq
        f hAdd a u (tarskiHornerValue f x (a :: rest))).mp
        hAddGraph).symm
    calc
      tarskiHornerValue f x (a :: rest) = a + u := hzEq
      _ = a + x * t := by rw [huEq]
      _ = a + x * tarskiHornerValue f x rest := by rw [htEq]
      _ = a + x * finiteHornerValue x rest := by rw [ih]
      _ = finiteHornerValue x (a :: rest) := rfl

end TarskiField

#print axioms TarskiField.tarskiHornerValue_eq_finiteHornerValue_of_geomField_tarski
/-!
## Both geometric real-closedness clauses from first-order A13 cuts

The canonical natural-language proof §3.3.6 identifies the only
remaining continuity interface: the finite definable negative-prefix
cuts for Horner polynomials, transferred to the scalar's intrinsic
geometric order.  The verified finite-Horner IVT, square-root, and
odd-degree-root theorems then close the exact two geometric goals.

The cut condition hA13 is a *parameter*, not a new Plane axiom.
Its unconditional proof from ContinuousPlane and the ordered-Bet
formula bridge remains a separate geometric task.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- The exact two remaining root goals are consequences of the single
definable-cut A13 bridge, evaluated in the geometrically constructed
Field, LinearOrder and IsStrictOrderedRing on AxisPoint. -/
theorem tarskiRootProperties_of_A13_ordered_cuts_tarski
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hAddAssoc : AddAssocLaw f)
    (hMulComm : MulCommLaw f)
    (hMulAssoc : MulAssocLaw f)
    (hDistrib : LeftDistributiveLaw f)
    (hPosMul : PositiveMulClosed f)
    (hA13 :
      letI : Field (AxisPoint f) :=
        axisFieldOfGeometricLaws_tarski
          f hAddAssoc hMulComm hMulAssoc hDistrib
      letI : LinearOrder (AxisPoint f) :=
        axisLinearOrderOfMidpointAddAssoc_tarski f hK hAddAssoc
      letI : IsStrictOrderedRing (AxisPoint f) :=
        axisStrictOrderedRingOfGeometricLaws_tarski
          f hK hAddAssoc hMulComm hMulAssoc hDistrib hPosMul
      FiniteHornerA13OrderedCuts (F := AxisPoint f)) :
    PositiveSquareRootProperty f ∧ OddPolynomialRootProperty f := by
  letI : Field (AxisPoint f) :=
    axisFieldOfGeometricLaws_tarski
      f hAddAssoc hMulComm hMulAssoc hDistrib
  letI : LinearOrder (AxisPoint f) :=
    axisLinearOrderOfMidpointAddAssoc_tarski f hK hAddAssoc
  letI : IsStrictOrderedRing (AxisPoint f) :=
    axisStrictOrderedRingOfGeometricLaws_tarski
      f hK hAddAssoc hMulComm hMulAssoc hDistrib hPosMul
  let hMul : MulTotal f := (operation_graphs_total_tarski f).2
  have hIVT : FiniteHornerIVT (F := AxisPoint f) :=
    finiteHornerIVT_of_A13_ordered_cuts hA13
  constructor
  · intro a hPositive
    have haPos : (0 : AxisPoint f) < a := by
      change AxisLt f (axisZero f) a
      exact (axisLt_zero_iff_positive_tarski f a).mpr hPositive
    obtain ⟨x, hxNonneg, hxx⟩ :=
      positive_sqrt_of_finiteHornerIVT hIVT a haPos
    refine ⟨x, ?_, ?_⟩
    · rcases eq_or_lt_of_le hxNonneg with hZero | hPositive
      · exact Or.inl hZero.symm
      · exact Or.inr hPositive
    · exact (mulGraph_iff_axisMulOf_eq f hMul x x a).mpr hxx
  · intro coefficients hOdd
    rcases hOdd with ⟨⟨k, hlen⟩, hlast⟩
    have hlast0 : coefficients.getLast? ≠
        some (0 : AxisPoint f) := hlast
    obtain ⟨x, hx⟩ :=
      finiteHorner_odd_degree_root_of_IVT
        hIVT coefficients k hlen hlast0
    refine ⟨x, ?_⟩
    have hGeomRoot :
        tarskiHornerValue f x coefficients = axisZero f := by
      calc
        tarskiHornerValue f x coefficients =
            finiteHornerValue x coefficients :=
          tarskiHornerValue_eq_finiteHornerValue_of_geomField_tarski
            f hAddAssoc hMulComm hMulAssoc hDistrib x coefficients
        _ = (0 : AxisPoint f) := hx
        _ = axisZero f := rfl
    exact (tarskiHornerValue_eq_iff_graph
      f x coefficients (axisZero f)).mp hGeomRoot

end TarskiField

#print axioms TarskiField.tarskiRootProperties_of_A13_ordered_cuts_tarski
/-!
## Exact finite definable-prefix formula and order semantics

Natural-language master §3.3.7.  This stage does not invoke the A13
existence theorem: it identifies the already compiled Tarski
negative-prefix Formula with the ordered negative-prefix predicate
on the same geometric carrier, for every axis point and every
parameterized finite coefficient list.

The only outstanding parameters are additive midpoint K and the
two additive laws needed to orient primitive Bet on the axis.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Strict negativity in the geometric order is exactly the
Tarski opposite ray.  Neither K nor any field or order law is used. -/
theorem axisLt_to_zero_iff_negative_ray_tarski
    (f : Frame Point) (x : AxisPoint f) :
    AxisLt f x (axisZero f) ↔
      x.1 ≠ f.O ∧ Bet x.1 f.O f.I := by
  have hNegIff : AxisLt f x (axisZero f) ↔ AxisNegative f x := by
    constructor
    · rintro ⟨d, hGraph, hPos⟩
      exact ⟨d, hPos, hGraph⟩
    · rintro ⟨d, hPos, hGraph⟩
      exact ⟨d, hGraph, hPos⟩
  exact hNegIff.trans (axisNegative_iff_opposite_ray_tarski f x)

/-- For an oriented interval L<R, the finite Tarski prefix Formula
agrees *point for point* with the initial negative prefix defined
using the intrinsic order and the uniquely constructed Horner value.
The case X=L is handled by Bet identity/order antisymmetry. -/
theorem polynomialLowerCutFormula_orderedPrefix_iff_tarski
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hComm : AddCommLaw f)
    (hAssoc : AddAssocLaw f)
    {n : Nat} (o i j l r : Fin n)
    (coefficients : List (Fin n))
    (ρ : Fin n → Point) (σ : Fin n → AxisPoint f)
    (hO : ρ o = f.O) (hI : ρ i = f.I) (hJ : ρ j = f.J)
    (hl : ρ l = (σ l).1) (hr : ρ r = (σ r).1)
    (hcoeff : ∀ c, c ∈ coefficients → ρ c = (σ c).1)
    (hLR : AxisLt f (σ l) (σ r))
    (X : AxisPoint f) :
    letI : Zero (AxisPoint f) := ⟨axisZero f⟩
    letI : LinearOrder (AxisPoint f) :=
      axisLinearOrderOfMidpointAddAssoc_tarski f hK hAssoc
    (polynomialLowerCutFormula o i j l r coefficients).eval
      (Fin.cons X.1 ρ) ↔
      OrderedNegativePrefix
        (fun t : AxisPoint f =>
          tarskiHornerValue f t (coefficients.map σ))
        (σ l) (σ r) X := by
  letI : Zero (AxisPoint f) := ⟨axisZero f⟩
  letI : LinearOrder (AxisPoint f) :=
    axisLinearOrderOfMidpointAddAssoc_tarski f hK hAssoc
  have hBounds (Y : AxisPoint f) :
      Bet (σ l).1 Y.1 (σ r).1 ↔
        (σ l) ≤ Y ∧ Y ≤ (σ r) := by
    change Bet (σ l).1 Y.1 (σ r).1 ↔
      AxisLe f (σ l) Y ∧ AxisLe f Y (σ r)
    exact axisBet_iff_directedBounds_of_addLaws_tarski
      f hK hComm hAssoc hLR
  have hInside (hBetLR : Bet (σ l).1 X.1 (σ r).1)
      (t : AxisPoint f) :
      Bet (σ l).1 t.1 X.1 ↔
        (σ l) ≤ t ∧ t ≤ X := by
    have hLX : AxisLe f (σ l) X := (hBounds X).mp hBetLR |>.1
    rcases hLX with hEq | hLess
    · subst X
      constructor
      · intro hb
        have hPoints : (σ l).1 = t.1 :=
          between_identity (σ l).1 t.1 hb
        have ht : σ l = t := Subtype.ext hPoints
        subst t
        exact ⟨le_refl _, le_refl _⟩
      · rintro ⟨hLt, htL⟩
        have ht : t = σ l := le_antisymm htL hLt
        subst t
        exact bet_start (σ l).1 (σ l).1
    · have hBetween :
          Bet (σ l).1 t.1 X.1 ↔
            AxisLe f (σ l) t ∧ AxisLe f t X :=
        axisBet_iff_directedBounds_of_addLaws_tarski
          f hK hComm hAssoc hLess
      exact hBetween
  have hNeg (t : AxisPoint f) :
      ((tarskiHornerValue f t (coefficients.map σ)).1 ≠ f.O ∧
        Bet (tarskiHornerValue f t (coefficients.map σ)).1 f.O f.I) ↔
      tarskiHornerValue f t (coefficients.map σ) <
        (0 : AxisPoint f) := by
    change
      ((tarskiHornerValue f t (coefficients.map σ)).1 ≠ f.O ∧
        Bet (tarskiHornerValue f t (coefficients.map σ)).1 f.O f.I) ↔
      AxisLt f (tarskiHornerValue f t (coefficients.map σ))
        (axisZero f)
    exact (axisLt_to_zero_iff_negative_ray_tarski
      f (tarskiHornerValue f t (coefficients.map σ))).symm
  rw [polynomialLowerCutFormula_geometricValue_iff_tarski
    f o i j l r coefficients ρ σ hO hI hJ hl hr hcoeff X]
  change
    (Bet (σ l).1 X.1 (σ r).1 ∧
      ∀ t : AxisPoint f,
        Bet (σ l).1 t.1 X.1 →
          (tarskiHornerValue f t (coefficients.map σ)).1 ≠ f.O ∧
            Bet (tarskiHornerValue f t (coefficients.map σ)).1 f.O f.I) ↔
    ((σ l) ≤ X ∧ X ≤ (σ r) ∧
      ∀ t : AxisPoint f,
        (σ l) ≤ t → t ≤ X →
          tarskiHornerValue f t (coefficients.map σ) <
            (0 : AxisPoint f))
  constructor
  · rintro ⟨hBet, hAll⟩
    obtain ⟨hLeft, hRight⟩ := (hBounds X).mp hBet
    refine ⟨hLeft, hRight, ?_⟩
    intro t hLt htx
    have hBetT : Bet (σ l).1 t.1 X.1 :=
      (hInside hBet t).mpr ⟨hLt, htx⟩
    exact (hNeg t).mp (hAll t hBetT)
  · rintro ⟨hLeft, hRight, hAll⟩
    have hBet : Bet (σ l).1 X.1 (σ r).1 :=
      (hBounds X).mpr ⟨hLeft, hRight⟩
    refine ⟨hBet, ?_⟩
    intro t ht
    obtain ⟨hLt, htx⟩ := (hInside hBet t).mp ht
    exact (hNeg t).mpr (hAll t hLt htx)

end TarskiField

#print axioms TarskiField.axisLt_to_zero_iff_negative_ray_tarski
#print axioms TarskiField.polynomialLowerCutFormula_orderedPrefix_iff_tarski
/-!
## Finite-A13 geometric upper bounds are ordered upper bounds

Canonical natural-language master §3.3.7: once the initial negative
prefix contains a point strictly beyond its left endpoint (supplied
by the verified finite-Horner local negativity estimate), the
original first-order Bet upper-bound condition is exactly strong
enough to establish the least-upper-bound condition in the internally
oriented scalar order.  Importantly, the candidate upper bound Y
need not lie inside the initial polynomial interval.

This short proof is independent of the ordered-field and continuity
constructions: the Bet-to-interval equivalence is exposed as a
single argument, which later takes the already verified geometric
AxisDirectedBetOrder and its converse.
-/

namespace TarskiField

section OrderedA13UpperBoundBridge

variable {F : Type*} [LinearOrder F]

/-- Exact logical conversion from Tarski-style Bet bounds at a
fixed left station to the true ordered least upper bound.  The
nonempty *strict* initial prefix is needed to exclude b=L. -/
theorem ordered_lub_of_bet_upper_tarski
    (B : F → F → F → Prop) (P : F → Prop)
    (L R b : F)
    (hLR : L < R)
    (hBetIff : ∀ (x y : F), L < y →
      (B L x y ↔ L ≤ x ∧ x ≤ y))
    (hBetIdentity : ∀ x : F, B L x L → x = L)
    (hPleft : ∀ x : F, P x → L ≤ x)
    (hPstrict : ∃ x : F, P x ∧ L < x)
    (hSegment : B L b R)
    (hUpper : ∀ x : F, P x → B L x b)
    (hLeast : ∀ y : F,
      (∀ x : F, P x → B L x y) → B L b y) :
    (L ≤ b ∧ b ≤ R) ∧
    (∀ x : F, P x → x ≤ b) ∧
    (∀ y : F, (∀ x : F, P x → x ≤ y) → b ≤ y) := by
  have hBounds : L ≤ b ∧ b ≤ R :=
    (hBetIff b R hLR).mp hSegment
  have hLb : L < b := by
    rcases lt_or_eq_of_le hBounds.1 with h | heq
    · exact h
    · obtain ⟨x0, hxP, hxStrict⟩ := hPstrict
      have hxBet : B L x0 L := by
        simpa only [← heq] using hUpper x0 hxP
      exact False.elim
        ((ne_of_gt hxStrict) (hBetIdentity x0 hxBet))
  refine ⟨hBounds, ?_, ?_⟩
  · intro x hx
    exact ((hBetIff x b hLb).mp (hUpper x hx)).2
  · intro y hy
    obtain ⟨x0, hxP, hxStrict⟩ := hPstrict
    have hLy : L < y := lt_of_lt_of_le hxStrict (hy x0 hxP)
    have hGeometric : ∀ x : F, P x → B L x y := by
      intro x hx
      exact (hBetIff x y hLy).mpr ⟨hPleft x hx, hy x hx⟩
    exact ((hBetIff b y hLy).mp (hLeast y hGeometric)).2

end OrderedA13UpperBoundBridge

end TarskiField

#print axioms TarskiField.ordered_lub_of_bet_upper_tarski
/-!
## Any finite scalar coefficient list has an A13 point environment

Natural master §3.3.8.  The five fixed slots are O,I,J,L,R
and the remaining m slots are the m polynomial coefficients.
The auxiliary-axis point J is *not* a scalar: the actual plane-point
environment rho sends slot 2 to J, whereas the auxiliary scalar
environment sigma sends it to O.  All coefficient indices are ≥5,
so the required rho/sigma agreement holds exactly where used.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Every finite list of actual scalar-axis coefficients can be
represented by the point-environment used by Tarski's first-order
A13 formula, with the off-axis frame point kept in its own slot. -/
theorem finiteHorner_axis_parameters_tarski
    (f : Frame Point)
    (coeff : List (AxisPoint f))
    (L R : AxisPoint f) :
    ∃ (n : Nat)
      (o i j l r : Fin n)
      (indices : List (Fin n))
      (ρ : Fin n → Point)
      (σ : Fin n → AxisPoint f),
      ρ o = f.O ∧ ρ i = f.I ∧ ρ j = f.J ∧
      ρ l = (σ l).1 ∧ ρ r = (σ r).1 ∧
      σ l = L ∧ σ r = R ∧
      (∀ c, c ∈ indices → ρ c = (σ c).1) ∧
      indices.map σ = coeff := by
  let frameAxis : Fin 5 → AxisPoint f :=
    ![axisZero f, axisOne f, axisZero f, L, R]
  let framePoints : Fin 5 → Point :=
    ![f.O, f.I, f.J, L.1, R.1]
  let σ : Fin (5 + coeff.length) → AxisPoint f :=
    Fin.addCases frameAxis coeff.get
  let ρ : Fin (5 + coeff.length) → Point :=
    Fin.addCases framePoints (fun k => (coeff.get k).1)
  let o : Fin (5 + coeff.length) :=
    Fin.castAdd coeff.length (0 : Fin 5)
  let i : Fin (5 + coeff.length) :=
    Fin.castAdd coeff.length (1 : Fin 5)
  let j : Fin (5 + coeff.length) :=
    Fin.castAdd coeff.length (2 : Fin 5)
  let l : Fin (5 + coeff.length) :=
    Fin.castAdd coeff.length (3 : Fin 5)
  let r : Fin (5 + coeff.length) :=
    Fin.castAdd coeff.length (4 : Fin 5)
  let indices : List (Fin (5 + coeff.length)) :=
    (List.finRange coeff.length).map (Fin.natAdd 5)
  refine ⟨5 + coeff.length, o, i, j, l, r,
    indices, ρ, σ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ρ, framePoints, o]
  · simp [ρ, framePoints, i]
  · simp [ρ, framePoints, j]
  · simp [ρ, σ, framePoints, frameAxis, l]
  · simp [ρ, σ, framePoints, frameAxis, r]
  · simp [σ, frameAxis, l]
  · simp [σ, frameAxis, r]
  · intro c hc
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
    simp [ρ, σ]
  · simp [indices, σ, List.finRange, List.map_ofFn, Function.comp_def]

end TarskiField

#print axioms TarskiField.finiteHorner_axis_parameters_tarski
/-!
## The actual A13 point-cut is an ordered finite-Horner least upper bound

Canonical master §3.3.8, with a specified finite point environment.
This theorem *invokes ContinuousPlane through the existing
polynomial_cut_A13_internal_order_of_left_negative* and discharges
the conversion from primitive plane Bet upper bounds to the genuine
least-upper-bound property in the internally constructed ordered
field.  It uses no completeness axiom on the scalar field.

A subsequent finite-index coding lemma supplies the environments
for arbitrary coefficient lists, including the empty list.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

theorem finiteHorner_A13_ordered_cut_of_parameters_tarski
    [ContinuousPlane Point]
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hComm : AddCommLaw f)
    (hAddAssoc : AddAssocLaw f)
    (hMulComm : MulCommLaw f)
    (hMulAssoc : MulAssocLaw f)
    (hDistrib : LeftDistributiveLaw f)
    (hPosMul : PositiveMulClosed f)
    {n : Nat}
    (o i j l r : Fin n)
    (coefficients : List (Fin n))
    (ρ : Fin n → Point) (σ : Fin n → AxisPoint f)
    (hO : ρ o = f.O) (hI : ρ i = f.I) (hJ : ρ j = f.J)
    (hl : ρ l = (σ l).1) (hr : ρ r = (σ r).1)
    (hcoeff : ∀ c, c ∈ coefficients → ρ c = (σ c).1)
    (hLR : AxisLt f (σ l) (σ r))
    (hLeft :
      letI : Field (AxisPoint f) :=
        axisFieldOfGeometricLaws_tarski
          f hAddAssoc hMulComm hMulAssoc hDistrib
      letI : LinearOrder (AxisPoint f) :=
        axisLinearOrderOfMidpointAddAssoc_tarski f hK hAddAssoc
      letI : IsStrictOrderedRing (AxisPoint f) :=
        axisStrictOrderedRingOfGeometricLaws_tarski
          f hK hAddAssoc hMulComm hMulAssoc hDistrib hPosMul
      finiteHornerValue (σ l) (coefficients.map σ) <
        (0 : AxisPoint f)) :
    letI : Field (AxisPoint f) :=
      axisFieldOfGeometricLaws_tarski
        f hAddAssoc hMulComm hMulAssoc hDistrib
    letI : LinearOrder (AxisPoint f) :=
      axisLinearOrderOfMidpointAddAssoc_tarski f hK hAddAssoc
    letI : IsStrictOrderedRing (AxisPoint f) :=
      axisStrictOrderedRingOfGeometricLaws_tarski
        f hK hAddAssoc hMulComm hMulAssoc hDistrib hPosMul
    ∃ b : AxisPoint f,
      ((σ l) ≤ b ∧ b ≤ (σ r)) ∧
      (∀ x : AxisPoint f,
        OrderedNegativePrefix
          (fun t : AxisPoint f =>
            finiteHornerValue t (coefficients.map σ))
          (σ l) (σ r) x → x ≤ b) ∧
      (∀ y : AxisPoint f,
        (∀ x : AxisPoint f,
          OrderedNegativePrefix
            (fun t : AxisPoint f =>
              finiteHornerValue t (coefficients.map σ))
            (σ l) (σ r) x → x ≤ y) → b ≤ y) := by
  letI : Field (AxisPoint f) :=
    axisFieldOfGeometricLaws_tarski
      f hAddAssoc hMulComm hMulAssoc hDistrib
  letI : LinearOrder (AxisPoint f) :=
    axisLinearOrderOfMidpointAddAssoc_tarski f hK hAddAssoc
  letI : IsStrictOrderedRing (AxisPoint f) :=
    axisStrictOrderedRingOfGeometricLaws_tarski
      f hK hAddAssoc hMulComm hMulAssoc hDistrib hPosMul
  let q : AxisPoint f → AxisPoint f :=
    fun t => finiteHornerValue t (coefficients.map σ)
  let P : AxisPoint f → Prop :=
    fun x => OrderedNegativePrefix q (σ l) (σ r) x
  have hNegLeft :
      (polynomialNegativeFormula o i j l coefficients).eval ρ := by
    apply (polynomialNegativeFormula_value_iff_tarski
      f o i j l coefficients ρ σ hO hI hJ hl hcoeff).mpr
    have hValue :
        tarskiHornerValue f (σ l) (coefficients.map σ) =
          finiteHornerValue (σ l) (coefficients.map σ) :=
      tarskiHornerValue_eq_finiteHornerValue_of_geomField_tarski
        f hAddAssoc hMulComm hMulAssoc hDistrib
        (σ l) (coefficients.map σ)
    have hNegative :
        AxisLt f (tarskiHornerValue f (σ l) (coefficients.map σ))
          (axisZero f) := by
      change tarskiHornerValue f (σ l) (coefficients.map σ) <
        (0 : AxisPoint f)
      rw [hValue]
      exact hLeft
    exact (axisLt_to_zero_iff_negative_ray_tarski
      f (tarskiHornerValue f (σ l) (coefficients.map σ))).mp hNegative
  obtain ⟨b, ⟨hSegment, _, _, hUpperEval, hLeastEval⟩, _⟩ :=
    polynomial_cut_A13_internal_order_of_left_negative
      f o i j l r coefficients ρ σ
      hO hI hJ hl hr (axisSegmentClosed_tarski f)
      (axisDirectedBetOrder_of_midpoint_addLaws_tarski
        f hK hComm hAddAssoc)
      hLR hcoeff hNegLeft
  have hFn :
      (fun t : AxisPoint f =>
        tarskiHornerValue f t (coefficients.map σ)) = q := by
    funext t
    exact tarskiHornerValue_eq_finiteHornerValue_of_geomField_tarski
      f hAddAssoc hMulComm hMulAssoc hDistrib
      t (coefficients.map σ)
  have hPrefix (x : AxisPoint f) :
      (polynomialLowerCutFormula o i j l r coefficients).eval
        (Fin.cons x.1 ρ) ↔ P x := by
    have h :=
      polynomialLowerCutFormula_orderedPrefix_iff_tarski
        f hK hComm hAddAssoc o i j l r coefficients
        ρ σ hO hI hJ hl hr hcoeff hLR x
    change
      (polynomialLowerCutFormula o i j l r coefficients).eval
        (Fin.cons x.1 ρ) ↔
      OrderedNegativePrefix q (σ l) (σ r) x
    rw [← hFn]
    exact h
  have hStrict : ∃ x : AxisPoint f, P x ∧ (σ l) < x := by
    exact ordered_negative_prefix_strict_witness_of_local_sign
      q (σ l) (σ r) hLR hLeft
      (fun z hz => finiteHorner_negative_local
        (coefficients.map σ) z hz)
  have hUpperFormula : ∀ X : Point,
      (polynomialLowerCutFormula o i j l r coefficients).eval
        (Fin.cons X ρ) → Bet (ρ l) X b.1 :=
    (upperBoundsFormula_eval l
      (polynomialLowerCutFormula o i j l r coefficients)
      ρ b.1).mp hUpperEval
  have hUpper : ∀ x : AxisPoint f, P x →
      Bet (σ l).1 x.1 b.1 := by
    intro x hx
    have hfx :
        (polynomialLowerCutFormula o i j l r coefficients).eval
          (Fin.cons x.1 ρ) := (hPrefix x).mpr hx
    simpa only [hl] using hUpperFormula x.1 hfx
  have hLeast : ∀ y : AxisPoint f,
      (∀ x : AxisPoint f, P x →
        Bet (σ l).1 x.1 y.1) →
      Bet (σ l).1 b.1 y.1 := by
    intro y hy
    have hyFormula :
        (upperBoundsFormula l
          (polynomialLowerCutFormula o i j l r coefficients)).eval
            (Fin.cons y.1 ρ) := by
      apply (upperBoundsFormula_eval l
        (polynomialLowerCutFormula o i j l r coefficients)
        ρ y.1).mpr
      intro X hfx
      have hCol : Col f.O f.I X := by
        have hParts :=
          (polynomialLowerCutFormula_prefix_eval
            o i j l r coefficients ρ X).mp hfx
        simpa only [hO, hI] using hParts.1
      let x : AxisPoint f := ⟨X, hCol⟩
      have hx : P x :=
        (hPrefix x).mp (by simpa only [x] using hfx)
      have hBound : Bet (σ l).1 X y.1 := hy x hx
      simpa only [hl] using hBound
    simpa only [hl] using hLeastEval y.1 hyFormula
  have hBetween (x y : AxisPoint f)
      (hLy : (σ l) < y) :
      Bet (σ l).1 x.1 y.1 ↔
        (σ l) ≤ x ∧ x ≤ y := by
    have hLyAxis : AxisLt f (σ l) y := hLy
    exact axisBet_iff_directedBounds_of_addLaws_tarski
      f hK hComm hAddAssoc hLyAxis
  have hIdentity (x : AxisPoint f)
      (hx : Bet (σ l).1 x.1 (σ l).1) :
      x = σ l := by
    apply Subtype.ext
    exact (between_identity (σ l).1 x.1 hx).symm
  have hBetSegment : Bet (σ l).1 b.1 (σ r).1 := by
    simpa only [hl, hr] using hSegment
  have hResult :=
    ordered_lub_of_bet_upper_tarski
      (fun A B C : AxisPoint f => Bet A.1 B.1 C.1)
      P (σ l) (σ r) b hLR hBetween hIdentity
      (fun x hx => hx.1) hStrict hBetSegment
      hUpper hLeast
  exact ⟨b, hResult⟩

end TarskiField

#print axioms TarskiField.finiteHorner_A13_ordered_cut_of_parameters_tarski
/-!
## PositiveMulClosed from the two actual geometric projection orders

Canonical natural master §3.2.1.  GeoCoq's project_preserves_bet
specialized to the two projections defining MulGraph has exactly
the following four primitive-Bet implications P1 and P2.  These
are the only outstanding pure-geometric premises here, not added
axioms or an assumption that multiplication preserves positivity.
The concluding proof itself uses no additive or multiplicative law.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- The positive-product goal reduced to the two line-projection
Bet-preservation instances.  Crucially this works for either position
of y relative to I, including equal points; there is no separate
case split on x relative to the unit. -/
theorem positiveMulClosed_of_two_projection_bet_tarski
    (f : Frame Point)
    (hFirst : ∀ (y : AxisPoint f) (W : Point),
      Col f.O f.J W →
      Parallel f.I f.J y.1 W →
      (Bet f.O f.I y.1 → Bet f.O f.J W) ∧
      (Bet f.O y.1 f.I → Bet f.O W f.J))
    (hSecond : ∀ (x z : AxisPoint f) (W : Point),
      Col f.O f.J W →
      Parallel f.J x.1 W z.1 →
      (Bet f.O f.J W → Bet f.O x.1 z.1) ∧
      (Bet f.O W f.J → Bet f.O z.1 x.1)) :
    PositiveMulClosed f := by
  intro x y z hx hy hMul
  have hzNe : z.1 ≠ f.O :=
    mulGraph_output_nonzero_of_inputs_nonzero
      f (colTransitivityGoal_tarski (Point := Point))
        x y z hMul hx.2.1 hy.2.1
  rcases hMul with ⟨hy0, _⟩ | ⟨_, W, hWaxis, hFirstPar, hSecondPar⟩
  · exact False.elim (hy.2.1 hy0)
  · have hFirstBet := hFirst y W hWaxis hFirstPar
    have hSecondBet := hSecond x z W hWaxis hSecondPar
    have hOutXZ : Out f.O x.1 z.1 := by
      refine ⟨hx.2.1, hzNe, ?_⟩
      rcases hy.2.2 with hOIy | hOyI
      · exact Or.inl (hSecondBet.1 (hFirstBet.1 hOIy))
      · exact Or.inr (hSecondBet.2 (hFirstBet.2 hOyI))
    exact out_trans_tarski hx hOutXZ

end TarskiField

#print axioms TarskiField.positiveMulClosed_of_two_projection_bet_tarski
/-!
## All finite A13 cuts and both exact real-closed root clauses

Natural master §3.3.9. This is the last finite-parameter assembly,
which replaces the hA13 hypothesis of the prior root-assembly theorem
by first-order ContinuousPlane itself. All coefficient lists,
including the empty list, use the explicit finite point environment
with the off-axis J point in its designated frame slot.

Only the still pending geometric K, additive/multiplicative, distributive
and positive-product laws remain as explicit *theorem premises*.
They are not new fields of Plane or asserted axioms.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- The original Tarski first-order continuity scheme yields the
finite-Horner ordered-cut property on the original AxisPoint carrier
after the exact geometric field/order laws have been established.
No Dedekind completeness or real-coordinate type is assumed. -/
theorem finiteHorner_A13_ordered_cuts_of_geometric_laws_tarski
    [ContinuousPlane Point]
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hComm : AddCommLaw f)
    (hAddAssoc : AddAssocLaw f)
    (hMulComm : MulCommLaw f)
    (hMulAssoc : MulAssocLaw f)
    (hDistrib : LeftDistributiveLaw f)
    (hPosMul : PositiveMulClosed f) :
    letI : Field (AxisPoint f) :=
      axisFieldOfGeometricLaws_tarski
        f hAddAssoc hMulComm hMulAssoc hDistrib
    letI : LinearOrder (AxisPoint f) :=
      axisLinearOrderOfMidpointAddAssoc_tarski f hK hAddAssoc
    letI : IsStrictOrderedRing (AxisPoint f) :=
      axisStrictOrderedRingOfGeometricLaws_tarski
        f hK hAddAssoc hMulComm hMulAssoc hDistrib hPosMul
    FiniteHornerA13OrderedCuts (F := AxisPoint f) := by
  letI : Field (AxisPoint f) :=
    axisFieldOfGeometricLaws_tarski
      f hAddAssoc hMulComm hMulAssoc hDistrib
  letI : LinearOrder (AxisPoint f) :=
    axisLinearOrderOfMidpointAddAssoc_tarski f hK hAddAssoc
  letI : IsStrictOrderedRing (AxisPoint f) :=
    axisStrictOrderedRingOfGeometricLaws_tarski
      f hK hAddAssoc hMulComm hMulAssoc hDistrib hPosMul
  intro coeff L R hLR hLeft _hRight
  obtain ⟨n, o, i, j, l, r, indices, ρ, σ,
      hO, hI, hJ, hl, hr, hL, hR, hcoeff, hList⟩ :=
    finiteHorner_axis_parameters_tarski f coeff L R
  have hLRaxis : AxisLt f (σ l) (σ r) := by
    change AxisLt f L R at hLR
    simpa only [hL, hR] using hLR
  have hLeftGeom :
      finiteHornerValue (σ l) (indices.map σ) <
        (0 : AxisPoint f) := by
    simpa only [hL, hList] using hLeft
  obtain ⟨b, hbSeg, hbUpper, hbLeast⟩ :=
    finiteHorner_A13_ordered_cut_of_parameters_tarski
      f hK hComm hAddAssoc hMulComm hMulAssoc hDistrib
      hPosMul o i j l r indices ρ σ
      hO hI hJ hl hr hcoeff hLRaxis hLeftGeom
  refine ⟨b, ?_, ?_, ?_⟩
  · simpa only [hL, hR] using hbSeg
  · intro x hx
    apply hbUpper x
    simpa only [hL, hR, hList] using hx
  · intro y hy
    apply hbLeast y
    intro x hx
    apply hy x
    simpa only [hL, hR, hList] using hx

/-- Both root conditions of the original 17-goal structure follow
from genuine first-order A13 after the exact geometric algebraic
premises have been proved. There is no further independent hA13
assumption, analytic completeness principle or coordinate model. -/
theorem tarskiRootProperties_of_continuity_geometric_laws_tarski
    [ContinuousPlane Point]
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hComm : AddCommLaw f)
    (hAddAssoc : AddAssocLaw f)
    (hMulComm : MulCommLaw f)
    (hMulAssoc : MulAssocLaw f)
    (hDistrib : LeftDistributiveLaw f)
    (hPosMul : PositiveMulClosed f) :
    PositiveSquareRootProperty f ∧ OddPolynomialRootProperty f := by
  apply tarskiRootProperties_of_A13_ordered_cuts_tarski
    f hK hAddAssoc hMulComm hMulAssoc hDistrib hPosMul
  exact finiteHorner_A13_ordered_cuts_of_geometric_laws_tarski
    f hK hComm hAddAssoc hMulComm hMulAssoc hDistrib hPosMul

end TarskiField

#print axioms TarskiField.finiteHorner_A13_ordered_cuts_of_geometric_laws_tarski
#print axioms TarskiField.tarskiRootProperties_of_continuity_geometric_laws_tarski
/-!
## Exact interpretation interfaces requested by the additive workstream

These are genuine equivalences about the SAME Tarski scalar AxisPoint.
An unoriented primitive Bet must be interpreted as either increasing
or decreasing ordered betweenness, never just the increasing branch.
The graph and sign results are relative to the constructed, not
imported, field/order typeclass instances.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- The original geometric addition and multiplication graphs agree
with the Field operations chosen from their unique geometric outputs.
This is a conditional assembly interface, not an assumption that
the still-pending synthetic field laws have been proved. -/
theorem axisGraph_iff_field_ops_tarski
    (f : Frame Point)
    (hAddAssoc : AddAssocLaw f)
    (hMulComm : MulCommLaw f)
    (hMulAssoc : MulAssocLaw f)
    (hDistrib : LeftDistributiveLaw f) :
    letI : Field (AxisPoint f) :=
      axisFieldOfGeometricLaws_tarski
        f hAddAssoc hMulComm hMulAssoc hDistrib
    (∀ a b c : AxisPoint f, AddGraph f a b c ↔ c = a + b) ∧
    (∀ a b c : AxisPoint f, MulGraph f a b c ↔ c = a * b) := by
  letI : Field (AxisPoint f) :=
    axisFieldOfGeometricLaws_tarski
      f hAddAssoc hMulComm hMulAssoc hDistrib
  let hAdd : AddTotal f := (operation_graphs_total_tarski f).1
  let hMul : MulTotal f := (operation_graphs_total_tarski f).2
  constructor
  · intro a b c
    change AddGraph f a b c ↔
      c = axisAddOf f hAdd a b
    constructor
    · intro h
      exact ((addGraph_iff_axisAddOf_eq f hAdd a b c).mp h).symm
    · intro h
      exact (addGraph_iff_axisAddOf_eq f hAdd a b c).mpr h.symm
  · intro a b c
    change MulGraph f a b c ↔
      c = axisMulOf f hMul a b
    constructor
    · intro h
      exact ((mulGraph_iff_axisMulOf_eq f hMul a b c).mp h).symm
    · intro h
      exact (mulGraph_iff_axisMulOf_eq f hMul a b c).mpr h.symm

/-- All three points on the scalar axis: primitive Bet is the
disjunction of the two oriented order intervals.  The a=c branch
is determined by Tarski's between-identity axiom. -/
theorem axisBet_iff_unoriented_order_bounds_tarski
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hComm : AddCommLaw f)
    (hAssoc : AddAssocLaw f)
    (a b c : AxisPoint f) :
    letI : LinearOrder (AxisPoint f) :=
      axisLinearOrderOfMidpointAddAssoc_tarski f hK hAssoc
    Bet a.1 b.1 c.1 ↔
      (a ≤ b ∧ b ≤ c) ∨ (c ≤ b ∧ b ≤ a) := by
  letI : LinearOrder (AxisPoint f) :=
    axisLinearOrderOfMidpointAddAssoc_tarski f hK hAssoc
  rcases lt_trichotomy a c with hac | heq | hca
  · have hBounds : Bet a.1 b.1 c.1 ↔
        a ≤ b ∧ b ≤ c := by
      change Bet a.1 b.1 c.1 ↔
        AxisLe f a b ∧ AxisLe f b c
      exact axisBet_iff_directedBounds_of_addLaws_tarski
        f hK hComm hAssoc hac
    constructor
    · intro h
      exact Or.inl (hBounds.mp h)
    · intro h
      rcases h with hForward | hBackward
      · exact hBounds.mpr hForward
      · have hca : c ≤ a := le_trans hBackward.1 hBackward.2
        exact False.elim ((not_le_of_gt hac) hca)
  · subst c
    constructor
    · intro h
      have hab : a = b :=
        Subtype.ext (between_identity a.1 b.1 h)
      subst b
      exact Or.inl ⟨le_refl _, le_refl _⟩
    · intro h
      rcases h with hForward | hBackward
      · have hab : a = b :=
          le_antisymm hForward.1 hForward.2
        subst b
        exact bet_start a.1 a.1
      · have hba : b = a :=
          le_antisymm hBackward.2 hBackward.1
        subst b
        exact bet_start a.1 a.1
  · have hBounds : Bet c.1 b.1 a.1 ↔
        c ≤ b ∧ b ≤ a := by
      change Bet c.1 b.1 a.1 ↔
        AxisLe f c b ∧ AxisLe f b a
      exact axisBet_iff_directedBounds_of_addLaws_tarski
        f hK hComm hAssoc hca
    constructor
    · intro h
      exact Or.inr (hBounds.mp (bet_symm h))
    · intro h
      rcases h with hForward | hBackward
      · have hac : a ≤ c := le_trans hForward.1 hForward.2
        exact False.elim ((not_le_of_gt hca) hac)
      · exact bet_symm (hBounds.mpr hBackward)

/-- The original geometric ray and nonnegative-axis predicates are
exactly the strict and weak comparisons in the selected geometric
LinearOrder.  No field or positive multiplication law is needed. -/
theorem axisPositiveNonneg_iff_order_tarski
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hAssoc : AddAssocLaw f) :
    letI : Zero (AxisPoint f) := ⟨axisZero f⟩
    letI : LinearOrder (AxisPoint f) :=
      axisLinearOrderOfMidpointAddAssoc_tarski f hK hAssoc
    ∀ x : AxisPoint f,
      (Positive f x ↔ (0 : AxisPoint f) < x) ∧
      (AxisNonneg f x ↔ (0 : AxisPoint f) ≤ x) := by
  letI : Zero (AxisPoint f) := ⟨axisZero f⟩
  letI : LinearOrder (AxisPoint f) :=
    axisLinearOrderOfMidpointAddAssoc_tarski f hK hAssoc
  intro x
  constructor
  · change Positive f x ↔ AxisLt f (axisZero f) x
    exact (axisLt_zero_iff_positive_tarski f x).symm
  · change
      (x = axisZero f ∨ AxisLt f (axisZero f) x) ↔
        AxisLe f (axisZero f) x
    constructor
    · intro h
      rcases h with hx | hx
      · exact Or.inl hx.symm
      · exact Or.inr hx
    · intro h
      rcases h with hx | hx
      · exact Or.inl hx.symm
      · exact Or.inr hx

end TarskiField

#print axioms TarskiField.axisGraph_iff_field_ops_tarski
#print axioms TarskiField.axisBet_iff_unoriented_order_bounds_tarski
#print axioms TarskiField.axisPositiveNonneg_iff_order_tarski


/-!
## The six remaining geometric bridges imply the complete 17-clause goal

The canonical natural-language proof §6 now has an exact Lean assembly
of all seventeen clauses. AddCommLaw follows from the existing minimal
Field construction, so it is not another independent geometric premise.
PositiveAddClosed follows from the forward direction of midpoint K.
The two root clauses follow from first-order ContinuousPlane by the
already established finite-Horner A13 route.

The six explicit premises below are exactly the remaining independent
geometric proof obligations, not additional axioms on Plane. This theorem
does not assert that those six have already been proved from Plane.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]

/-- Once the four minimal geometric field laws hold, commutativity of
the ORIGINAL geometric AddGraph is forced by Field.ofMinimalAxioms.
No separately assumed additive-commutativity law is necessary. -/
theorem addCommLaw_of_four_geometric_laws_tarski
    (f : Frame Point)
    (hAddAssoc : AddAssocLaw f)
    (hMulComm : MulCommLaw f)
    (hMulAssoc : MulAssocLaw f)
    (hDistrib : LeftDistributiveLaw f) :
    AddCommLaw f := by
  letI : Field (AxisPoint f) :=
    axisFieldOfGeometricLaws_tarski
      f hAddAssoc hMulComm hMulAssoc hDistrib
  have hGraph :
      ∀ a b c : AxisPoint f,
        AddGraph f a b c ↔ c = a + b :=
    (axisGraph_iff_field_ops_tarski
      f hAddAssoc hMulComm hMulAssoc hDistrib).1
  intro x y z hxy
  have hz : z = x + y := (hGraph x y z).mp hxy
  apply (hGraph y x z).mpr
  calc
    z = x + y := hz
    _ = y + x := add_comm x y

/-- Exactly six unfinished geometric bridges are sufficient to
discharge the complete original RealClosedAxisGoal. All 17 conclusions
use the original point-based AddGraph/MulGraph/Positive/HornerGraph;
the finite-Horner roots come from ContinuousPlane itself. -/
theorem realClosedAxisGoal_of_six_geometric_bridges_tarski
    [ContinuousPlane Point]
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hAddAssoc : AddAssocLaw f)
    (hMulComm : MulCommLaw f)
    (hMulAssoc : MulAssocLaw f)
    (hDistrib : LeftDistributiveLaw f)
    (hPosMul : PositiveMulClosed f) :
    RealClosedAxisGoal f := by
  have hComm : AddCommLaw f :=
    addCommLaw_of_four_geometric_laws_tarski
      f hAddAssoc hMulComm hMulAssoc hDistrib
  have hPosAdd : PositiveAddClosed f :=
    positiveAddClosed_of_midpoint_forward_tarski f
      (fun a b c hAdd => (hK a b c).mp hAdd)
  obtain ⟨hSquareRoot, hOddRoot⟩ :=
    tarskiRootProperties_of_continuity_geometric_laws_tarski
      f hK hComm hAddAssoc hMulComm hMulAssoc hDistrib hPosMul
  exact (realClosedAxisGoal_iff_nine_remaining_tarski f).mpr
    ⟨hComm, hAddAssoc, hMulComm, hMulAssoc,
      hDistrib, hPosAdd, hPosMul, hSquareRoot, hOddRoot⟩

end TarskiField

#print axioms TarskiField.addCommLaw_of_four_geometric_laws_tarski
#print axioms TarskiField.realClosedAxisGoal_of_six_geometric_bridges_tarski


/-!
## Zero inputs and zero output in the additive common-midpoint bridge K

Canonical Japanese natural proof §3.3. The K equivalence is settled
unconditionally whenever the first summand, second summand or output
is the geometric origin. Only the nonzero/nonzero/nonzero incidence
configuration remains for a direct geometric proof of K.

The arguments use the already verified synthetic midpoint existence,
uniqueness of reflection around a fixed midpoint, and the zero-result
characterization of AddGraph. They do not use AddComm, AddAssoc,
the ordered field or any fresh Plane axiom.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- K for a zero first summand, including the fully degenerate case:
two reflections of O around the same midpoint have identical outputs. -/
theorem addGraph_midpoint_left_zero_iff_tarski
    (f : Frame Point) (d b : AxisPoint f) :
    AddGraph f (axisZero f) d b ↔
      ∃ M : Point,
        MulMidpoint M f.O b.1 ∧
        MulMidpoint M (axisZero f).1 d.1 := by
  constructor
  · intro hAdd
    have hb : b = d := add_zero_left_unique f d b hAdd
    subst b
    obtain ⟨M, hMid⟩ := midpoint_existence_tarski f.O d.1
    exact ⟨M, hMid, hMid⟩
  · rintro ⟨M, hOb, hOd⟩
    have hBD : b.1 = d.1 :=
      mul_reflection_involution (mul_midpoint_reverse hOb) hOd
    have hb : b = d := Subtype.ext hBD
    subst b
    exact add_zero_left f d

/-- K for a zero second summand; use the already proved geometric
right-zero law rather than assuming additive commutativity. -/
theorem addGraph_midpoint_right_zero_iff_tarski
    (f : Frame Point) (a b : AxisPoint f) :
    AddGraph f a (axisZero f) b ↔
      ∃ M : Point,
        MulMidpoint M f.O b.1 ∧
        MulMidpoint M a.1 (axisZero f).1 := by
  constructor
  · intro hAdd
    have hb : b = a :=
      (operation_graphs_functional_tarski f).1
        a (axisZero f) b a hAdd (add_zero_right_tarski f a)
    subst b
    obtain ⟨M, hMid⟩ := midpoint_existence_tarski f.O a.1
    exact ⟨M, hMid, mul_midpoint_reverse hMid⟩
  · rintro ⟨M, hOb, hAO⟩
    have hBA : b.1 = a.1 :=
      mul_reflection_involution
        (mul_midpoint_reverse hOb) (mul_midpoint_reverse hAO)
    have hb : b = a := Subtype.ext hBA
    subst b
    exact add_zero_right_tarski f a

/-- K for zero output. The midpoint of OO must be O itself, after
which K is exactly the existing AddGraph-zero midpoint theorem. -/
theorem addGraph_midpoint_output_zero_iff_tarski
    (f : Frame Point) (a d : AxisPoint f) :
    AddGraph f a d (axisZero f) ↔
      ∃ M : Point,
        MulMidpoint M f.O (axisZero f).1 ∧
        MulMidpoint M a.1 d.1 := by
  constructor
  · intro hAdd
    have hAD : MulMidpoint f.O a.1 d.1 :=
      (addGraph_zero_iff_midpoint_tarski f a d).mp hAdd
    refine ⟨f.O, ?_, hAD⟩
    change MulMidpoint f.O f.O f.O
    exact ⟨bet_start f.O f.O, congr_refl f.O f.O⟩
  · rintro ⟨M, hOO, hAD⟩
    have hOOBet : Plane.Bet f.O M f.O := hOO.1
    have hM : M = f.O :=
      (between_identity f.O M hOOBet).symm
    exact (addGraph_zero_iff_midpoint_tarski f a d).mpr
      (by simpa only [hM] using hAD)

/-- The full K goal is reduced to the one strict configuration
a ≠ O, d ≠ O and b ≠ O. Every degeneracy is already discharged
by the preceding unconditional geometric proofs. -/
theorem addGraph_midpoint_iff_of_nonzero_core_tarski
    (f : Frame Point)
    (hCore : ∀ a d b : AxisPoint f,
      a ≠ axisZero f → d ≠ axisZero f → b ≠ axisZero f →
      (AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)) :
    ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1 := by
  intro a d b
  by_cases ha : a = axisZero f
  · subst a
    exact addGraph_midpoint_left_zero_iff_tarski f d b
  by_cases hd : d = axisZero f
  · subst d
    exact addGraph_midpoint_right_zero_iff_tarski f a b
  by_cases hb : b = axisZero f
  · subst b
    exact addGraph_midpoint_output_zero_iff_tarski f a d
  exact hCore a d b ha hd hb

end TarskiField

#print axioms TarskiField.addGraph_midpoint_left_zero_iff_tarski
#print axioms TarskiField.addGraph_midpoint_right_zero_iff_tarski
#print axioms TarskiField.addGraph_midpoint_output_zero_iff_tarski
#print axioms TarskiField.addGraph_midpoint_iff_of_nonzero_core_tarski


/-!
## Primitive Tarski betweenness through a strict parallel projection

This is the essential one-sided "beyond the station" case of
GeoCoq Annexes.project.project_preserves_bet. The reverse endpoint
case follows by exchanging the two parallel lines. This theorem is
constructed using only strict-parallel same-side preservation and
primitive Pasch-derived opposite-side transport. It assumes neither
an ordered field nor a multiplicative positivity law.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- A pair of parallel transversals in a nonflat Tarski wedge preserves
the oriented betweenness O-A-B to O-A'-B'. Degenerate B=A is handled by
line-intersection uniqueness. -/
theorem projected_bet_beyond_of_parallel_tarski
    {O A A' B B' : Point}
    (htri : ¬ Col O A A')
    (hOA : O ≠ A) (hOA' : O ≠ A')
    (hB'axis : Col O A' B')
    (hpar : Parallel A A' B B')
    (hbet : Bet O A B) :
    Bet O A' B' := by
  have htri' : ¬ Col A A' O := by
    intro h
    exact htri (col_rotate (col_rotate h))
  by_cases hBA : B = A
  · subst B
    have hSame : ∀ S : Point, Col A A' S ↔ Col A B' S :=
      parallel_same_of_intersection hpar
        (col_left A A') (col_left A B')
    have hB'eq : B' = A' :=
      line_intersection_unique_tarski
        (A := A) (B := A') (C := O) (D := A')
        (P := B') (Q := A') htri' hOA'
        ((hSame B').mpr (col_right A B'))
        (col_right A A') hB'axis (col_right O A')
    subst B'
    exact bet_end O A'
  · have hBaxis : Col O A B := Or.inl hbet
    have hBoff : ¬ Col A A' B := by
      intro hB
      exact hBA (line_intersection_unique_tarski
        (A := A) (B := A') (C := O) (D := A)
        (P := B) (Q := A) htri' hOA
        hB (col_left A A') hBaxis (col_right O A))
    have hOppOB : OppositeSides A A' O B :=
      ⟨htri', hBoff, A, col_left A A', hbet⟩
    have hSameBB' : SameSides A A' B B' :=
      strict_parallel_sameSides_tarski hpar hBoff
        (col_left B B') (col_right B B')
    have hOppB'O : OppositeSides A A' B' O :=
      oppositeSides_sameSides_transport_tarski
        (oppositeSides_symm_tarski hOppOB) hSameBB'
    have hOppOB' : OppositeSides A A' O B' :=
      oppositeSides_symm_tarski hOppB'O
    have hOB' : O ≠ B' := by
      intro h
      have hContr : OppositeSides A A' O O := by
        simpa [h] using hOppOB'
      exact oppositeSides_irrefl_tarski hContr
    obtain ⟨C, hCpar, hOCB'⟩ := hOppOB'.2.2
    have hline : ∀ S : Point, Col O A' S ↔ Col O B' S :=
      col_line_extensionality_tarski hOA' hOB'
        (col_left O A') hB'axis
    have hA'OB' : Col O B' A' := (hline A').mp (col_right O A')
    have hCOB' : Col O B' C := Or.inr (Or.inl (bet_symm hOCB'))
    have hCeq : C = A' :=
      line_intersection_unique_tarski
        (A := A) (B := A') (C := O) (D := B')
        (P := C) (Q := A') htri' hOB'
        hCpar (col_right A A') hCOB' hA'OB'
    simpa only [hCeq] using hOCB'

end TarskiField

#print axioms TarskiField.projected_bet_beyond_of_parallel_tarski


/-!
## Unconditional strict positivity of the geometric Tarski multiplication

The two parallel projections preserve the origin-side ordering on
their respective rays.  This is a direct consequence of the Tarski
Pasch/parallel same-side theorem above; no field, ring, ordered-space,
or abstract projective-coordinate theorem is used.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- For a positive right factor, the two projections preserve the
ray of the nonzero left factor, irrespective of its sign. -/
theorem mul_same_ray_of_positive_right_tarski
    (f : Frame Point) (x y z : AxisPoint f)
    (hx : x.1 ≠ f.O) (hy : Positive f y)
    (hMul : MulGraph f x y z) :
    Out f.O x.1 z.1 := by
  let hCol : ColTransitivityGoal (Point := Point) :=
    colTransitivityGoal_tarski (Point := Point)
  have hzNe : z.1 ≠ f.O :=
    mulGraph_output_nonzero_of_inputs_nonzero
      f hCol x y z hMul hx hy.2.1
  rcases hMul with ⟨hyZero, _⟩ | ⟨_, W, hWaxis, hFirstPar, hSecondPar⟩
  · exact False.elim (hy.2.1 hyZero)
  · have hWNe : W ≠ f.O :=
      mul_first_projection_nonzero f y W hFirstPar
    have hOIz : Col f.O z.1 x.1 :=
      axis_col_of_colTrans f hCol z x
    have hOIx : Col f.O x.1 z.1 :=
      axis_col_of_colTrans f hCol x z
    have hOWJ : Col f.O W f.J :=
      col_rotate (col_swap hWaxis)
    have hOutXZ : Out f.O x.1 z.1 := by
      refine ⟨hx, hzNe, ?_⟩
      rcases hy.2.2 with hOIy | hOyI
      · have hOJW : Bet f.O f.J W :=
          projected_bet_beyond_of_parallel_tarski
            f.noncol f.O_ne_I f.O_ne_J
            hWaxis hFirstPar hOIy
        have hOJx : ¬ Col f.O f.J x.1 := by
          intro h
          exact (axis_not_col_aux_of_colTrans f hCol x hx)
            (col_rotate (col_swap h))
        have hOxz : Bet f.O x.1 z.1 :=
          projected_bet_beyond_of_parallel_tarski
            hOJx f.O_ne_J hx.symm
            hOIx hSecondPar hOJW
        exact Or.inl hOxz
      · have hOyW : ¬ Col f.O y.1 W := by
          intro h
          have hOIW : Col f.O f.I W :=
            (col_line_extensionality_tarski
              f.O_ne_I hy.2.1.symm
              (col_left f.O f.I) y.2 W).mpr h
          exact hWNe
            (frame_axes_intersection_only_origin_tarski f W hOIW hWaxis)
        have hOWJBet : Bet f.O W f.J :=
          projected_bet_beyond_of_parallel_tarski
            hOyW hy.2.1.symm hWNe.symm
            hOWJ (parallel_symm hFirstPar) hOyI
        have hOWz : ¬ Col f.O W z.1 := by
          intro h
          have hOJz : Col f.O f.J z.1 :=
            (col_line_extensionality_tarski
              f.O_ne_J hWNe.symm
              (col_left f.O f.J) hWaxis z.1).mpr h
          exact (axis_not_col_aux_of_colTrans f hCol z hzNe)
            (col_rotate (col_swap hOJz))
        have hOzx : Bet f.O z.1 x.1 :=
          projected_bet_beyond_of_parallel_tarski
            hOWz hWNe.symm hzNe.symm
            hOIz (parallel_symm hSecondPar) hOWJBet
        exact Or.inr hOzx
    exact hOutXZ

/-- The actual positive cone of the geometric multiplication graph
is closed under products, unconditionally in the Tarski plane. -/
theorem positiveMulClosed_tarski (f : Frame Point) :
    PositiveMulClosed f := by
  intro x y z hx hy hMul
  exact out_trans_tarski hx
    (mul_same_ray_of_positive_right_tarski f x y z hx.2.1 hy hMul)

end TarskiField

#print axioms TarskiField.positiveMulClosed_tarski


/-!
## Final Mathlib real-closed-field conclusion on the geometric Tarski axis

The largest target is Mathlib's actual IsRealClosed instance for
AxisPoint f, whose Field, LinearOrder and IsStrictOrderedRing are made
from the original Tarski AddGraph, MulGraph and positive displacement.
The proof translates first-order A13 finite Horner roots to roots of
arbitrary Mathlib polynomials, including zero, and applies
IsRealClosed.of_linearOrderedField. No extra bridge hypotheses are
introduced: precisely the five geometric obligations of the preceding
17-clause result are still displayed in the theorem statement.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]

/-- The ORIGINAL Tarski axis carries a Mathlib real-closed field
once the five remaining synthetic-geometric inputs are established.
In particular this conclusion is IsRealClosed, not merely the earlier
17-component relational specification RealClosedAxisGoal. -/
theorem axis_isRealClosed_of_five_geometric_bridges_tarski
    [ContinuousPlane Point]
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point,
          MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hAddAssoc : AddAssocLaw f)
    (hMulComm : MulCommLaw f)
    (hMulAssoc : MulAssocLaw f)
    (hDistrib : LeftDistributiveLaw f) :
    letI : Field (AxisPoint f) :=
      axisFieldOfGeometricLaws_tarski
        f hAddAssoc hMulComm hMulAssoc hDistrib
    letI : LinearOrder (AxisPoint f) :=
      axisLinearOrderOfMidpointAddAssoc_tarski f hK hAddAssoc
    letI : IsStrictOrderedRing (AxisPoint f) :=
      axisStrictOrderedRingOfGeometricLaws_tarski
        f hK hAddAssoc hMulComm hMulAssoc hDistrib (positiveMulClosed_tarski f)
    IsRealClosed (AxisPoint f) := by
  letI : Field (AxisPoint f) :=
    axisFieldOfGeometricLaws_tarski
      f hAddAssoc hMulComm hMulAssoc hDistrib
  letI : LinearOrder (AxisPoint f) :=
    axisLinearOrderOfMidpointAddAssoc_tarski f hK hAddAssoc
  letI : IsStrictOrderedRing (AxisPoint f) :=
    axisStrictOrderedRingOfGeometricLaws_tarski
      f hK hAddAssoc hMulComm hMulAssoc hDistrib (positiveMulClosed_tarski f)
  have hComm : AddCommLaw f :=
    addCommLaw_of_four_geometric_laws_tarski
      f hAddAssoc hMulComm hMulAssoc hDistrib
  have hA13 : FiniteHornerA13OrderedCuts (F := AxisPoint f) :=
    finiteHorner_A13_ordered_cuts_of_geometric_laws_tarski
      f hK hComm hAddAssoc hMulComm hMulAssoc hDistrib (positiveMulClosed_tarski f)
  have hIVT : FiniteHornerIVT (F := AxisPoint f) :=
    finiteHornerIVT_of_A13_ordered_cuts hA13
  have hEval (coeff : List (AxisPoint f)) (x : AxisPoint f) :
      finiteHornerValue x coeff =
        (Polynomial.ofCoeffList coeff).eval x := by
    induction coeff with
    | nil =>
        simp [finiteHornerValue]
    | cons a rest ih =>
        simp only [finiteHornerValue, Polynomial.ofCoeffList_cons,
          Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
          Polynomial.eval_X, ih]
  apply IsRealClosed.of_linearOrderedField
  · intro a ha
    obtain ⟨b, _, hb⟩ :=
      nonnegative_sqrt_of_finiteHornerIVT hIVT a ha
    exact ⟨b, hb.symm⟩
  · intro p hp
    classical
    have hp0 : p ≠ 0 := by
      intro hz
      simp [hz] at hp
    obtain ⟨k, hk⟩ := hp
    have hlen : (p.coeffList.reverse).length = 2 * k + 2 := by
      simp [Polynomial.length_coeffList_eq_ite, hp0, hk]
    have hlast :
        (p.coeffList.reverse).getLast? ≠
          some (0 : AxisPoint f) := by
      have hhead :
          p.coeffList.head? = some p.leadingCoeff :=
        Polynomial.head?_coeffList hp0
      have hlast_eq :
          (p.coeffList.reverse).getLast? =
            some p.leadingCoeff := by
        simpa [List.getLast?_reverse] using hhead
      intro hz
      rw [hlast_eq] at hz
      exact ((Polynomial.leadingCoeff_ne_zero).2 hp0) (Option.some.inj hz)
    obtain ⟨x, hx⟩ :=
      finiteHorner_odd_degree_root_of_IVT
        hIVT p.coeffList.reverse k hlen hlast
    refine ⟨x, ?_⟩
    change p.eval x = 0
    calc
      p.eval x =
          (Polynomial.ofCoeffList p.coeffList.reverse).eval x := by
            rw [Polynomial.ofCoeffList_reverse_coeffList]
      _ = finiteHornerValue x p.coeffList.reverse := (hEval _ x).symm
      _ = 0 := hx

end TarskiField

#print axioms TarskiField.axis_isRealClosed_of_five_geometric_bridges_tarski


/-!
The exact top-down additive interface.  Every case of K, commutativity,
and associativity is discharged here from a *single* primitive-geometric
obligation: composition of two quadrilaterals with bisected diagonals.
No field law, positivity assumption, or coordinate representation is used.
The composition premise is not claimed as proved in this theorem.
-/
namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

theorem additive_laws_of_midpoint_quadrilateral_composition_tarski
    (f : Frame Point)
    (hCore :
      ∀ A B C D E F : Point,
        (A ≠ C ∨ B ≠ D) →
        (C ≠ E ∨ D ≠ F) →
        (∃ M : Point, MulMidpoint M A C ∧ MulMidpoint M B D) →
        (∃ N : Point, MulMidpoint N C E ∧ MulMidpoint N D F) →
        (∃ P : Point, MulMidpoint P A F ∧ MulMidpoint P B E)) :
    (∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point, MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1) ∧
      AddCommLaw f ∧ AddAssocLaw f := by
  have hCompose :
      ∀ A B C D E F : Point,
        (∃ M : Point, MulMidpoint M A C ∧ MulMidpoint M B D) →
        (∃ N : Point, MulMidpoint N C E ∧ MulMidpoint N D F) →
        (∃ P : Point, MulMidpoint P A F ∧ MulMidpoint P B E) := by
    intro A B C D E F hFirst hSecond
    by_cases hTrivialFirst : A = C ∧ B = D
    · rcases hTrivialFirst with ⟨hAC, hBD⟩
      subst C
      subst D
      obtain ⟨M, hMAA, hMBB⟩ := hFirst
      have hAM : A = M := between_identity A M hMAA.1
      have hBM : B = M := between_identity B M hMBB.1
      have hAB : A = B := hAM.trans hBM.symm
      obtain ⟨N, hNAE, hNBF⟩ := hSecond
      have hNAF : MulMidpoint N A F := by
        simpa only [← hAB] using hNBF
      have hEF : E = F :=
        mul_reflection_involution
          (mul_midpoint_reverse hNAE) hNAF
      refine ⟨N, ?_, ?_⟩
      · simpa only [← hEF] using hNAE
      · simpa only [← hEF] using hNBF
    by_cases hTrivialSecond : C = E ∧ D = F
    · rcases hTrivialSecond with ⟨hCE, hDF⟩
      subst E
      subst F
      obtain ⟨N, hNCC, hNDD⟩ := hSecond
      have hCN : C = N := between_identity C N hNCC.1
      have hDN : D = N := between_identity D N hNDD.1
      have hCD : C = D := hCN.trans hDN.symm
      obtain ⟨M, hMAC, hMBD⟩ := hFirst
      exact ⟨M,
        by simpa only [hCD] using hMAC,
        by simpa only [hCD] using hMBD⟩
    have hNontrivialFirst : A ≠ C ∨ B ≠ D := by
      by_cases hAC : A = C
      · exact Or.inr (fun hBD => hTrivialFirst ⟨hAC, hBD⟩)
      · exact Or.inl hAC
    have hNontrivialSecond : C ≠ E ∨ D ≠ F := by
      by_cases hCE : C = E
      · exact Or.inr (fun hDF => hTrivialSecond ⟨hCE, hDF⟩)
      · exact Or.inl hCE
    exact hCore A B C D E F
      hNontrivialFirst hNontrivialSecond hFirst hSecond
  have hForward : ∀ a d b : AxisPoint f,
      AddGraph f a d b →
        ∃ M : Point, MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1 := by
    intro a d b hAdd
    by_cases ha : a = axisZero f
    · subst a
      exact (addGraph_midpoint_left_zero_iff_tarski f d b).mp hAdd
    · obtain ⟨T, hVert, hHorz, hDiag⟩ :=
        (addGraph_nonzero_iff f a d b ha).mp hAdd
      have haO : a.1 ≠ f.O := by
        intro h
        exact ha (Subtype.ext h)
      have hLineOa : ∀ S, Col f.O f.I S ↔ Col f.O a.1 S :=
        col_line_extensionality_tarski f.O_ne_I haO.symm
          (col_left f.O f.I) a.2
      have hJT_Oa : Parallel f.J T f.O a.1 :=
        parallel_retarget_right_of_line_eq
          (parallel_symm hHorz) haO.symm hLineOa
      have hNoncolOJT : ¬ Col f.O f.J T := by
        intro hT
        have hLine : ∀ S, Col f.J T S ↔ Col f.O f.J S := by
          intro S
          exact (col_line_extensionality_tarski
            f.O_ne_J hHorz.2.1 (col_right f.O f.J) hT S).symm
        have hBad : Parallel f.O f.I f.O f.J :=
          parallel_retarget_right_of_line_extensionality_tarski
            hHorz f.O_ne_J hLine
        exact frame_axes_not_parallel f hBad
      obtain ⟨M, hMOT, hMJa⟩ :=
        parallelogram_diagonal_midpoint_exists_tarski
          hNoncolOJT (parallel_reverse_right hVert)
          (parallel_reverse_right hJT_Oa)
      have hFirst :
          ∃ M : Point,
            MulMidpoint M f.O T ∧ MulMidpoint M a.1 f.J :=
        ⟨M, hMOT, mul_midpoint_reverse hMJa⟩
      have hdb : d.1 ≠ b.1 :=
        addGraph_strong_target_ne_input_tarski f d b T hHorz hDiag
      have hLineBd : ∀ S, Col f.O f.I S ↔ Col b.1 d.1 S :=
        col_line_extensionality_tarski f.O_ne_I hdb.symm
          b.2 d.2
      have hJT_Bd : Parallel f.J T b.1 d.1 :=
        parallel_retarget_right_of_line_extensionality_tarski
          (parallel_symm hHorz) hdb.symm hLineBd
      have hNoncolJTb : ¬ Col f.J T b.1 := by
        intro hB
        have hDisjoint : ∀ S,
            ¬ (Col f.O f.I S ∧ Col f.J T S) :=
          playfair_strict_of_off_reference_tarski
            hHorz f.noncol (col_left f.J T)
        exact hDisjoint b.1 ⟨b.2, hB⟩
      obtain ⟨N, hNJb, hNTd⟩ :=
        parallelogram_diagonal_midpoint_exists_tarski
          hNoncolJTb hJT_Bd
          (parallel_reverse_right (parallel_symm hDiag))
      have hSecond :
          ∃ N : Point,
            MulMidpoint N T d.1 ∧ MulMidpoint N f.J b.1 :=
        ⟨N, hNTd, hNJb⟩
      exact hCompose f.O a.1 T f.J d.1 b.1 hFirst hSecond
  have hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point, MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1 := by
    intro a d b
    constructor
    · exact hForward a d b
    · intro hQ
      obtain ⟨w, hw, _⟩ := (operation_graphs_total_tarski f).1 a d
      obtain ⟨M, hMOb, hMad⟩ := hForward a d w hw
      obtain ⟨N, hNOb, hNad⟩ := hQ
      have hMN : M = N :=
        mul_midpoint_center_unique_tarski hMad hNad
      subst N
      have hwb : w.1 = b.1 :=
        mul_reflection_involution
          (mul_midpoint_reverse hMOb) hNOb
      have heq : w = b := Subtype.ext hwb
      simpa only [← heq] using hw
  refine ⟨hK, ?_, ?_⟩
  · intro x y z hxy
    obtain ⟨M, hMOz, hMxy⟩ := (hK x y z).mp hxy
    exact (hK y x z).mpr
      ⟨M, hMOz, mul_midpoint_reverse hMxy⟩
  · intro x y z xy yz lhs rhs hxy hxy_z hyz hx_yz
    obtain ⟨M, hMOxy, hMxy⟩ := (hK x y xy).mp hxy
    obtain ⟨N, hMOyz, hMyz⟩ := (hK y z yz).mp hyz
    obtain ⟨P, hMOrhs, hMx_yz⟩ := (hK x yz rhs).mp hx_yz
    have hOne :
        ∃ W : Point,
          MulMidpoint W y.1 x.1 ∧ MulMidpoint W xy.1 f.O :=
      ⟨M, mul_midpoint_reverse hMxy, mul_midpoint_reverse hMOxy⟩
    have hTwo :
        ∃ W : Point,
          MulMidpoint W x.1 yz.1 ∧ MulMidpoint W f.O rhs.1 :=
      ⟨P, hMx_yz, hMOrhs⟩
    obtain ⟨R, hMyrhs, hMxyyz⟩ :=
      hCompose y.1 xy.1 x.1 f.O yz.1 rhs.1 hOne hTwo
    have hThree :
        ∃ W : Point,
          MulMidpoint W z.1 y.1 ∧ MulMidpoint W f.O yz.1 :=
      ⟨N, mul_midpoint_reverse hMyz, hMOyz⟩
    have hFour :
        ∃ W : Point,
          MulMidpoint W y.1 rhs.1 ∧ MulMidpoint W yz.1 xy.1 :=
      ⟨R, hMyrhs, mul_midpoint_reverse hMxyyz⟩
    obtain ⟨S, hMzxy, hMOrhs'⟩ :=
      hCompose z.1 f.O y.1 yz.1 rhs.1 xy.1 hThree hFour
    have hWanted :
        ∃ W : Point,
          MulMidpoint W f.O rhs.1 ∧ MulMidpoint W xy.1 z.1 :=
      ⟨S, hMOrhs', mul_midpoint_reverse hMzxy⟩
    have hGraph : AddGraph f xy z rhs := (hK xy z rhs).mpr hWanted
    exact (operation_graphs_functional_tarski f).1
      xy z lhs rhs hxy_z hGraph

end TarskiField

#print axioms TarskiField.additive_laws_of_midpoint_quadrilateral_composition_tarski




/-!
## Distributivity: all zero-operand and unit-factor configurations

The remaining configuration of the unconditional LeftDistributiveLaw
contains no zero factor and a multiplier different from the unit.  These
four exhaustive exceptional branches use only previously proved
functionality, identity and zero theorems of the Tarski diagrams.
The nondegenerate problem is separate: it requires the actual affine
projection-preserves-sum and auxiliary-axis change constructions.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]

/-- The geometric multiplication distributes over addition whenever
the multiplier is zero or the geometric unit, or either summand is zero.
These are actual Tarski consequences, with no field-law hypothesis. -/
theorem leftDistrib_degenerate_tarski
    (f : Frame Point)
    (a b c bc ab ac lhs rhs : AxisPoint f)
    (hdeg : a = axisZero f ∨ a = axisOne f ∨
      b = axisZero f ∨ c = axisZero f)
    (hbc : AddGraph f b c bc)
    (hMulBC : MulGraph f a bc lhs)
    (hMulAB : MulGraph f a b ab)
    (hMulAC : MulGraph f a c ac)
    (hR : AddGraph f ab ac rhs) :
    lhs = rhs := by
  have hAddFun : AddFunctional f :=
    (operation_graphs_functional_tarski f).1
  have hMulFun : MulFunctional f :=
    (operation_graphs_functional_tarski f).2
  rcases hdeg with ha0 | ha1 | hb0 | hc0
  · subst a
    have hlhs : lhs = axisZero f :=
      mulGraph_zero_left_unique_tarski f bc lhs hMulBC
    have hab : ab = axisZero f :=
      mulGraph_zero_left_unique_tarski f b ab hMulAB
    have hac : ac = axisZero f :=
      mulGraph_zero_left_unique_tarski f c ac hMulAC
    have hrhs : rhs = axisZero f :=
      add_zero_left_unique f (axisZero f) rhs
        (by simpa only [hab, hac] using hR)
    exact hlhs.trans hrhs.symm
  · subst a
    have hOne : MulLeftOneLaw f := (mulKernel_tarski f).2.2.1
    have hlhs : lhs = bc :=
      hMulFun (axisOne f) bc lhs bc hMulBC (hOne bc)
    have hab : ab = b :=
      hMulFun (axisOne f) b ab b hMulAB (hOne b)
    have hac : ac = c :=
      hMulFun (axisOne f) c ac c hMulAC (hOne c)
    have hrhs : rhs = bc :=
      hAddFun b c rhs bc (by simpa only [hab, hac] using hR) hbc
    exact hlhs.trans hrhs.symm
  · subst b
    have hbc' : bc = c :=
      add_zero_left_unique f c bc hbc
    have hab : ab = axisZero f :=
      mul_zero_right_unique f a ab hMulAB
    have hrhs : rhs = ac :=
      add_zero_left_unique f ac rhs
        (by simpa only [hab] using hR)
    have hlhs : lhs = ac :=
      hMulFun a c lhs ac
        (by simpa only [hbc'] using hMulBC) hMulAC
    exact hlhs.trans hrhs.symm
  · subst c
    have hbc' : bc = b :=
      hAddFun b (axisZero f) bc b hbc
        (add_zero_right_tarski f b)
    have hac : ac = axisZero f :=
      mul_zero_right_unique f a ac hMulAC
    have hrhs : rhs = ab :=
      hAddFun ab (axisZero f) rhs ab
        (by simpa only [hac] using hR)
        (add_zero_right_tarski f ab)
    have hlhs : lhs = ab :=
      hMulFun a b lhs ab
        (by simpa only [hbc'] using hMulBC) hMulAB
    exact hlhs.trans hrhs.symm

end TarskiField

#print axioms TarskiField.leftDistrib_degenerate_tarski


/-!
## The horizontal unit change in GeoCoq's distributivity construction

The last step of GeoCoq Ch14_prod.distr_l changes the point naming the
horizontal axis without changing the geometric sum.  Our RawAddGraph
records that choice in only one line OI: it is consequently invariant
under replacement of I by any other non-origin point K on the same
line.  This is an unconditional Tarski incidence theorem.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Exact horizontal-axis-unit invariance of the original raw Tarski
addition graph.  No additive law, field, midpoint characterization,
or parallel-projection sum theorem is assumed. -/
theorem rawAddGraph_horizontal_unit_change_tarski
    {O I J K X Y Z : Point}
    (hOI : O ≠ I) (hOK : O ≠ K)
    (hKaxis : Col O I K) :
    RawAddGraph O I J X Y Z ↔
      RawAddGraph O K J X Y Z := by
  have hLines : ∀ P : Point, Col O I P ↔ Col O K P :=
    col_line_extensionality_tarski hOI hOK
      (col_left O I) hKaxis
  constructor
  · intro h
    rcases h with ⟨hZero, hResult⟩ | ⟨hNonzero, T, hVert, hHoriz, hDiag⟩
    · exact Or.inl ⟨hZero, hResult⟩
    · have hHoriz' : Parallel O K J T :=
        parallel_symm
          (parallel_retarget_right_of_line_eq
            (parallel_symm hHoriz) hOK hLines)
      exact Or.inr ⟨hNonzero, T, hVert, hHoriz', hDiag⟩
  · intro h
    rcases h with ⟨hZero, hResult⟩ | ⟨hNonzero, T, hVert, hHoriz, hDiag⟩
    · exact Or.inl ⟨hZero, hResult⟩
    · have hHoriz' : Parallel O I J T :=
        parallel_symm
          (parallel_retarget_right_of_line_eq
            (parallel_symm hHoriz) hOI
            (fun P => (hLines P).symm))
      exact Or.inr ⟨hNonzero, T, hVert, hHoriz', hDiag⟩

end TarskiField

#print axioms TarskiField.rawAddGraph_horizontal_unit_change_tarski


/-!
## GeoCoq projection-preserves-sum: the nonzero affine core

This is the geometric portion of GeoCoq Ch14_sum.proj_preserves_sum.
The two shared quadrilateral facts are explicit hypotheses:
* hSource supplies the common midpoint already used in bridge K;
* hG is the common-midpoint quadrilateral composition owned by the
  additive-geometry proof, not reproduced or assumed as a Plane axiom.

The proof constructs the parallelogram joining the projected B' to A,
composes its bisected diagonals with the source sum, and uses Playfair's
uniqueness to transport the output onto the projected C'.  It concludes
the actual four-projection GeoCoqSum on the exchanged coordinate frame.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Coq proj_preserves_sum's nonzero, non-flat affine transport, expressed
at the exact common-midpoint API boundary shared with bridge K. -/
theorem geoCoqSum_projected_of_midpoint_composition_tarski
    (f : Frame Point)
    (A B C : AxisPoint f)
    (A' B' C' : Point)
    (hANe : A.1 ≠ f.O)
    (_hBNe : B.1 ≠ f.O)
    (hA'axis : Col f.O f.J A')
    (hB'axis : Col f.O f.J B')
    (hC'axis : Col f.O f.J C')
    (hProjA : Parallel f.I f.J A.1 A')
    (hProjB : Parallel f.I f.J B.1 B')
    (hProjC : GeoCoqPj f.I f.J C.1 C')
    (hSource : ∃ M : Point,
      MulMidpoint M f.O C.1 ∧ MulMidpoint M A.1 B.1)
    (hG : ∀ U V W X Y Z : Point,
      (∃ M : Point, MulMidpoint M U W ∧ MulMidpoint M V X) →
      (∃ M : Point, MulMidpoint M W Y ∧ MulMidpoint M X Z) →
      (∃ M : Point, MulMidpoint M U Z ∧ MulMidpoint M V Y)) :
    let g : Frame Point :=
      ⟨f.O, f.J, f.I, fun h => f.noncol (col_swap_last h)⟩
    GeoCoqSum g ⟨A', hA'axis⟩ ⟨B', hB'axis⟩ ⟨C', hC'axis⟩ := by
  let g : Frame Point :=
    ⟨f.O, f.J, f.I, fun h => f.noncol (col_swap_last h)⟩
  have hB'Ne : B' ≠ f.O :=
    geoCoq_firstPj_not_origin f B B' _hBNe (Or.inl hProjB)
  have hTri : ¬ Col f.O B' A.1 := by
    intro h
    have hOA : Col f.O A.1 B' := col_swap_last h
    have hOI : Col f.O f.I B' :=
      (col_line_extensionality_tarski
        f.O_ne_I hANe.symm (col_left f.O f.I) A.2 B').mpr hOA
    exact hB'Ne
      (frame_axes_intersection_only_origin_tarski f B' hOI hB'axis)
  obtain ⟨M, hMB'A⟩ := midpoint_existence_tarski B' A.1
  obtain ⟨D, hMOD, _⟩ := mul_reflection_exists_unique M f.O
  have hSides :=
    midpoint_diagonals_parallelogram_tarski
      hTri hMB'A hMOD
  have hLineOB' : ∀ S : Point,
      Col f.O B' S ↔ Col f.O f.J S := by
    intro S
    exact (col_line_extensionality_tarski
      f.O_ne_J hB'Ne.symm
      (col_left f.O f.J) hB'axis S).symm
  have hVert0 : Parallel f.O B' D A.1 := hSides.1
  have hVert1 : Parallel f.O f.J D A.1 :=
    parallel_symm
      (parallel_retarget_right_of_line_extensionality_tarski
        (parallel_symm hVert0) f.O_ne_J hLineOB')
  have hVert : Parallel f.O f.J A.1 D :=
    parallel_reverse_right hVert1
  have hLineAO : ∀ S : Point,
      Col A.1 f.O S ↔ Col f.O f.I S := by
    intro S
    exact (col_line_extensionality_tarski
      f.O_ne_I hANe A.2 (col_left f.O f.I) S).symm
  have hHoriz : Parallel f.O f.I B' D :=
    parallel_symm
      (parallel_retarget_right_of_line_extensionality_tarski
        hSides.2 f.O_ne_I hLineAO)
  obtain ⟨N, hNOC, hNAB⟩ := hSource
  obtain ⟨P, hPB'C, hPDB⟩ :=
    hG B' D A.1 f.O B.1 C.1
      ⟨M, hMB'A, mul_midpoint_reverse hMOD⟩
      ⟨N, hNAB, hNOC⟩
  have hB'DC : ¬ Col B' D C.1 := by
    intro hCol
    have hSame : ∀ S : Point,
        Col f.O f.I S ↔ Col B' D S :=
      parallel_same_of_intersection hHoriz C.2 hCol
    have hOI : Col f.O f.I B' :=
      (hSame B').mpr (col_left B' D)
    exact hB'Ne
      (frame_axes_intersection_only_origin_tarski f B' hOI hB'axis)
  have hDB'C : ¬ Col D B' C.1 := by
    intro h
    exact hB'DC (col_swap h)
  have hProjectionDC : Parallel B' B.1 C.1 D :=
    (midpoint_diagonals_parallelogram_tarski
      hDB'C hPB'C hPDB).2
  have hProjectionCD : Parallel f.I f.J C.1 D :=
    parallelTransitivityGoal_tarski f.I f.J B' B.1 C.1 D
      (parallel_reverse_right hProjB) hProjectionDC
  have hLast : GeoCoqPj f.I f.J D C' := by
    by_cases hDC' : D = C'
    · exact Or.inr hDC'
    · rcases hProjC with hCC' | hCC'
      · have hLineCC' : ∀ S : Point,
            Col C.1 D S ↔ Col C.1 C' S :=
          tarski_playfair f.I f.J C.1 D C.1 C' C.1
            hProjectionCD hCC'
            (col_left C.1 D) (col_left C.1 C')
        have hC'D : Col C.1 D C' :=
          (hLineCC' C').mpr (col_right C.1 C')
        have hLineDC' : ∀ S : Point,
            Col C.1 D S ↔ Col D C' S :=
          col_line_extensionality_tarski
            hProjectionCD.2.1 hDC'
            (col_right C.1 D) hC'D
        exact Or.inl
          (parallel_retarget_right_of_line_extensionality_tarski
            hProjectionCD hDC' hLineDC')
      · have hPar : Parallel f.I f.J D C.1 :=
          parallel_reverse_right hProjectionCD
        exact Or.inl (by simpa only [← hCC'] using hPar)
  change GeoCoqSum g
    (⟨A', hA'axis⟩ : AxisPoint g)
    (⟨B', hB'axis⟩ : AxisPoint g)
    (⟨C', hC'axis⟩ : AxisPoint g)
  exact ⟨A.1, D,
    Or.inl (parallel_reverse_both hProjA),
    A.2,
    Or.inl hVert,
    Or.inl hHoriz,
    hLast⟩

end TarskiField

#print axioms TarskiField.geoCoqSum_projected_of_midpoint_composition_tarski


/-!
## GeoCoq sum to the common-midpoint quadrilateral

The four strict projections form two genuine parallelograms:
O-y-C-P and C-P-x-z. Their bisected diagonals give
Q(O,y,C,P) and Q(C,P,x,z). One application of the shared
quadrilateral-composition core G gives Q(O,y,z,x), hence K's
common-midpoint characterization of x+y=z. This implements the
GeoCoqSum-to-Q direction; no additive ring law or new axiom is used.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Nonzero GeoCoqSum yields a common midpoint of O,z and x,y
from the shared, explicitly stated quadrilateral composition. -/
theorem geoCoqSum_midpoint_of_quadrilateral_composition_tarski
    (f : Frame Point) (x y z : AxisPoint f)
    (hx : x.1 ≠ f.O) (hy : y.1 ≠ f.O)
    (hSum : GeoCoqSum f x y z)
    (hG : ∀ U V W X Y Z : Point,
      (∃ M : Point, MulMidpoint M U W ∧ MulMidpoint M V X) →
      (∃ M : Point, MulMidpoint M W Y ∧ MulMidpoint M X Z) →
      (∃ M : Point, MulMidpoint M U Z ∧ MulMidpoint M V Y)) :
    ∃ M : Point,
      MulMidpoint M f.O z.1 ∧ MulMidpoint M x.1 y.1 := by
  obtain ⟨P, C, hPaxis, hFirst, hSecond,
    hThird, hCoff, hLast⟩ :=
    geoCoqSum_nonzero_strict_projections_tarski f x y z hx hy hSum
  have hPNe : P ≠ f.O :=
    geoCoq_firstPj_not_origin f x P hx (Or.inl hFirst)
  have hLineOI_y : ∀ S : Point,
      Col f.O f.I S ↔ Col f.O y.1 S :=
    col_line_extensionality_tarski
      f.O_ne_I hy.symm (col_left f.O f.I) y.2
  have hTri1 : ¬ Col f.O y.1 C := by
    intro h
    exact hCoff ((hLineOI_y C).mpr h)
  have hParOyPC : Parallel f.O y.1 P C :=
    parallel_symm
      (parallel_retarget_right_of_line_extensionality_tarski
        (parallel_symm hSecond) hy.symm hLineOI_y)
  have hParOyCP : Parallel f.O y.1 C P :=
    parallel_reverse_right hParOyPC
  have hLineOJ_PO : ∀ S : Point,
      Col f.O f.J S ↔ Col P f.O S :=
    col_line_extensionality_tarski
      f.O_ne_J hPNe hPaxis (col_left f.O f.J)
  have hParYCPO : Parallel y.1 C P f.O :=
    parallel_retarget_right_of_line_extensionality_tarski
      (parallel_symm hThird) hPNe hLineOJ_PO
  have hQ1 : ∃ M : Point,
      MulMidpoint M f.O C ∧ MulMidpoint M y.1 P :=
    parallelogram_diagonal_midpoint_exists_tarski
      hTri1 hParOyCP hParYCPO
  have hTri2 : ¬ Col C P x.1 := by
    intro hCPx
    have hSame : ∀ S : Point,
        Col f.O f.I S ↔ Col P C S :=
      parallel_same_of_intersection hSecond x.2 (col_swap hCPx)
    have hOnOI : Col f.O f.I P :=
      (hSame P).mpr (col_left P C)
    exact hPNe
      (frame_axes_intersection_only_origin_tarski f P hOnOI hPaxis)
  have hxz : x.1 ≠ z.1 := by
    intro heq
    have hLast' : Parallel f.I f.J C x.1 := by
      simpa only [← heq] using (parallel_reverse_left hLast)
    have hLine : ∀ S : Point,
        Col x.1 P S ↔ Col C x.1 S :=
      tarski_playfair f.I f.J x.1 P C x.1 x.1
        hFirst hLast' (col_left x.1 P) (col_right C x.1)
    have hCxP : Col x.1 P C :=
      (hLine C).mpr (col_left C x.1)
    exact hTri2 (col_swap (col_rotate hCxP))
  have hLineOI_xz : ∀ S : Point,
      Col f.O f.I S ↔ Col x.1 z.1 S :=
    col_line_extensionality_tarski
      f.O_ne_I hxz x.2 z.2
  have hParCP_xz : Parallel C P x.1 z.1 :=
    parallel_reverse_left
      (parallel_retarget_right_of_line_extensionality_tarski
        (parallel_symm hSecond) hxz hLineOI_xz)
  have hParPx_zC : Parallel P x.1 z.1 C :=
    parallel_reverse_both
      (parallelTransitivityGoal_tarski x.1 P f.J f.I C z.1
        (parallel_symm (parallel_reverse_left hFirst)) hLast)
  have hQ2 : ∃ N : Point,
      MulMidpoint N C x.1 ∧ MulMidpoint N P z.1 :=
    parallelogram_diagonal_midpoint_exists_tarski
      hTri2 hParCP_xz hParPx_zC
  obtain ⟨M, hMOz, hMyx⟩ :=
    hG f.O y.1 C P x.1 z.1 hQ1 hQ2
  exact ⟨M, hMOz, mul_midpoint_reverse hMyx⟩

end TarskiField

#print axioms TarskiField.geoCoqSum_midpoint_of_quadrilateral_composition_tarski


/-!
## Complete GeoCoqSum / common-midpoint bridge relative to G

The strict case is the two-parallelogram argument above. A zero input
reduces to the already established zero-input common-midpoint identities.
The reverse implication uses GeoCoqSum's unconditional existence and
uniqueness of a midpoint relative to a fixed diagonal. Therefore no
separate final-grid or AddGraph↔GeoCoqSum hypothesis is required.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]

/-- The full GeoCoq sum diagram and the midpoint definition of addition
coincide once the ONE shared synthetic quadrilateral-composition core G
is proved. All zero cases and the converse are included. -/
theorem geoCoqSum_iff_common_midpoint_of_composition_tarski
    (f : Frame Point)
    (hG : ∀ U V W X Y Z : Point,
      (∃ M : Point, MulMidpoint M U W ∧ MulMidpoint M V X) →
      (∃ M : Point, MulMidpoint M W Y ∧ MulMidpoint M X Z) →
      (∃ M : Point, MulMidpoint M U Z ∧ MulMidpoint M V Y))
    (x y z : AxisPoint f) :
    GeoCoqSum f x y z ↔
      ∃ M : Point,
        MulMidpoint M f.O z.1 ∧ MulMidpoint M x.1 y.1 := by
  by_cases hx0 : x = axisZero f
  · subst x
    constructor
    · intro hSum
      have hz : z = y :=
        geoCoqSum_left_zero_unique_tarski f y z hSum
      subst z
      obtain ⟨M, hMid⟩ := midpoint_existence_tarski f.O y.1
      exact ⟨M, hMid, hMid⟩
    · intro hQ
      have hAdd : AddGraph f (axisZero f) y z :=
        (addGraph_midpoint_left_zero_iff_tarski f y z).mpr hQ
      have hz : z = y := add_zero_left_unique f y z hAdd
      subst z
      exact geoCoqSum_left_zero_tarski f y
  by_cases hy0 : y = axisZero f
  · subst y
    constructor
    · intro hSum
      have hz : z = x :=
        geoCoqSum_right_zero_unique_tarski f x z hSum
      subst z
      obtain ⟨M, hMid⟩ := midpoint_existence_tarski f.O x.1
      exact ⟨M, hMid, mul_midpoint_reverse hMid⟩
    · intro hQ
      have hAdd : AddGraph f x (axisZero f) z :=
        (addGraph_midpoint_right_zero_iff_tarski f x z).mpr hQ
      have hz : z = x :=
        (operation_graphs_functional_tarski f).1
          x (axisZero f) z x hAdd (add_zero_right_tarski f x)
      subst z
      exact geoCoqSum_right_zero_tarski f x
  have hx : x.1 ≠ f.O := by
    intro h
    exact hx0 (Subtype.ext h)
  have hy : y.1 ≠ f.O := by
    intro h
    exact hy0 (Subtype.ext h)
  constructor
  · intro hSum
    exact geoCoqSum_midpoint_of_quadrilateral_composition_tarski
      f x y z hx hy hSum hG
  · intro hQ
    obtain ⟨w, hW, _⟩ := geoCoqSum_existsUnique_tarski f x y
    have hWQ :
        ∃ N : Point,
          MulMidpoint N f.O w.1 ∧ MulMidpoint N x.1 y.1 :=
      geoCoqSum_midpoint_of_quadrilateral_composition_tarski
        f x y w hx hy hW hG
    obtain ⟨M, hMOz, hMxy⟩ := hQ
    obtain ⟨N, hNOw, hNxy⟩ := hWQ
    have hzw : z.1 = w.1 :=
      diagonal_midpoints_fourth_vertex_unique_tarski
        (A := x.1) (B := f.O) (C := y.1)
        ⟨M, hMxy, hMOz⟩ ⟨N, hNxy, hNOw⟩
    have hzwAxis : z = w := Subtype.ext hzw
    simpa only [hzwAxis] using hW

end TarskiField

#print axioms TarskiField.geoCoqSum_iff_common_midpoint_of_composition_tarski


/-!
## Left distributivity from the shared additive midpoint bridge and G

This is GeoCoq Ch14_prod.distr_l, with two literal applications of the
projection-preserves-sum theorem above. The first application projects
b,c,b+c from OI onto OJ along IJ. The second projects those three
intermediate points from OJ back onto the scalar line Oa along Ja.
Each projected GeoCoqSum is converted to the same common-midpoint
equation via G. The output is the original LeftDistributiveLaw.

The parameters hK and hG are the two still-separate additive-geometric
facts owned by the additive companion work; no standalone affine axiom,
ring law or unrelated incidence hypothesis is assumed here.
-/

namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- Full left distributivity follows from exactly the existing additive
midpoint characterization K and its shared quadrilateral-composition
principle G. All nonzero products and zero-sum outputs are included. -/
theorem leftDistrib_of_midpoint_and_composition_tarski
    (f : Frame Point)
    (hK : ∀ x y z : AxisPoint f,
      AddGraph f x y z ↔
        ∃ M : Point,
          MulMidpoint M f.O z.1 ∧ MulMidpoint M x.1 y.1)
    (hG : ∀ U V W X Y Z : Point,
      (∃ M : Point, MulMidpoint M U W ∧ MulMidpoint M V X) →
      (∃ M : Point, MulMidpoint M W Y ∧ MulMidpoint M X Z) →
      (∃ M : Point, MulMidpoint M U Z ∧ MulMidpoint M V Y)) :
    LeftDistributiveLaw f := by
  intro a b c bc ab ac lhs rhs hbc hMulBC hMulAB hMulAC hR
  by_cases ha0 : a = axisZero f
  · exact leftDistrib_degenerate_tarski
      f a b c bc ab ac lhs rhs (Or.inl ha0)
        hbc hMulBC hMulAB hMulAC hR
  by_cases hb0 : b = axisZero f
  · exact leftDistrib_degenerate_tarski
      f a b c bc ab ac lhs rhs
        (Or.inr (Or.inr (Or.inl hb0)))
        hbc hMulBC hMulAB hMulAC hR
  by_cases hc0 : c = axisZero f
  · exact leftDistrib_degenerate_tarski
      f a b c bc ab ac lhs rhs
        (Or.inr (Or.inr (Or.inr hc0)))
        hbc hMulBC hMulAB hMulAC hR
  have ha : a.1 ≠ f.O := by
    intro h
    exact ha0 (Subtype.ext h)
  have hb : b.1 ≠ f.O := by
    intro h
    exact hb0 (Subtype.ext h)
  have hc : c.1 ≠ f.O := by
    intro h
    exact hc0 (Subtype.ext h)
  obtain ⟨Wb, hWbaxis, hProjB, hResultB⟩ : ∃ Wb : Point,
      Col f.O f.J Wb ∧
      Parallel f.I f.J b.1 Wb ∧
      Parallel f.J a.1 Wb ab.1 := by
    rcases hMulAB with ⟨h0, _⟩ | ⟨_, Wb, hWbaxis, hProjB, hResultB⟩
    · exact False.elim (hb h0)
    · exact ⟨Wb, hWbaxis, hProjB, hResultB⟩
  obtain ⟨Wc, hWcaxis, hProjC, hResultC⟩ : ∃ Wc : Point,
      Col f.O f.J Wc ∧
      Parallel f.I f.J c.1 Wc ∧
      Parallel f.J a.1 Wc ac.1 := by
    rcases hMulAC with ⟨h0, _⟩ | ⟨_, Wc, hWcaxis, hProjC, hResultC⟩
    · exact False.elim (hc h0)
    · exact ⟨Wc, hWcaxis, hProjC, hResultC⟩
  obtain ⟨Wd, hWdaxis, hProjD, hResultD⟩ : ∃ Wd : Point,
      Col f.O f.J Wd ∧
      GeoCoqPj f.I f.J bc.1 Wd ∧
      GeoCoqPj f.J a.1 Wd lhs.1 := by
    rcases hMulBC with ⟨hZero, hLhsZero⟩ |
      ⟨_, Wd, hWdaxis, hProjD, hResultD⟩
    · have hLhsO : lhs.1 = f.O := by
        exact congrArg Subtype.val hLhsZero
      exact ⟨f.O, col_left f.O f.J, Or.inr hZero,
        Or.inr hLhsO.symm⟩
    · exact ⟨Wd, hWdaxis, Or.inl hProjD, Or.inl hResultD⟩
  have hSource : ∃ M : Point,
      MulMidpoint M f.O bc.1 ∧ MulMidpoint M b.1 c.1 :=
    (hK b c bc).mp hbc
  let g : Frame Point :=
    ⟨f.O, f.J, f.I, fun h => f.noncol (col_swap_last h)⟩
  let wb : AxisPoint g := ⟨Wb, hWbaxis⟩
  let wc : AxisPoint g := ⟨Wc, hWcaxis⟩
  let wd : AxisPoint g := ⟨Wd, hWdaxis⟩
  have hSumW : GeoCoqSum g wb wc wd := by
    exact geoCoqSum_projected_of_midpoint_composition_tarski
      f b c bc Wb Wc Wd hb hc
        hWbaxis hWcaxis hWdaxis
        hProjB hProjC hProjD hSource hG
  have hQW : ∃ M : Point,
      MulMidpoint M f.O Wd ∧ MulMidpoint M Wb Wc :=
    (geoCoqSum_iff_common_midpoint_of_composition_tarski
      g hG wb wc wd).mp hSumW
  have hCol : ColTransitivityGoal (Point := Point) :=
    colTransitivityGoal_tarski (Point := Point)
  have hNoOJa : ¬ Col f.O f.J a.1 := by
    intro h
    exact (axis_not_col_aux_of_colTrans f hCol a ha)
      (col_swap_last h)
  let g2 : Frame Point := ⟨f.O, f.J, a.1, hNoOJa⟩
  let g3 : Frame Point :=
    ⟨f.O, a.1, f.J, axis_not_col_aux_of_colTrans f hCol a ha⟩
  let wb2 : AxisPoint g2 := ⟨Wb, hWbaxis⟩
  let wc2 : AxisPoint g2 := ⟨Wc, hWcaxis⟩
  let wd2 : AxisPoint g2 := ⟨Wd, hWdaxis⟩
  have hABaxis : Col f.O a.1 ab.1 :=
    axis_col_of_colTrans f hCol a ab
  have hACaxis : Col f.O a.1 ac.1 :=
    axis_col_of_colTrans f hCol a ac
  have hLHSaxis : Col f.O a.1 lhs.1 :=
    axis_col_of_colTrans f hCol a lhs
  let ab3 : AxisPoint g3 := ⟨ab.1, hABaxis⟩
  let ac3 : AxisPoint g3 := ⟨ac.1, hACaxis⟩
  let lhs3 : AxisPoint g3 := ⟨lhs.1, hLHSaxis⟩
  have hSumFinal : GeoCoqSum g3 ab3 ac3 lhs3 := by
    exact geoCoqSum_projected_of_midpoint_composition_tarski
      g2 wb2 wc2 wd2 ab.1 ac.1 lhs.1
        (geoCoq_firstPj_not_origin f b Wb hb (Or.inl hProjB))
        (geoCoq_firstPj_not_origin f c Wc hc (Or.inl hProjC))
        hABaxis hACaxis hLHSaxis
        hResultB hResultC hResultD hQW hG
  have hQResult : ∃ M : Point,
      MulMidpoint M f.O lhs.1 ∧ MulMidpoint M ab.1 ac.1 :=
    (geoCoqSum_iff_common_midpoint_of_composition_tarski
      g3 hG ab3 ac3 lhs3).mp hSumFinal
  have hResult : AddGraph f ab ac lhs :=
    (hK ab ac lhs).mpr hQResult
  exact (operation_graphs_functional_tarski f).1
    ab ac lhs rhs hResult hR

end TarskiField

#print axioms TarskiField.leftDistrib_of_midpoint_and_composition_tarski


/-!
## The largest conclusion from precisely three geometric cores

This is deliberately top-down: the exact final IsRealClosed theorem follows
from quadrilateral midpoint composition G plus the genuine geometric
commutativity and associativity of multiplication. K, additive associativity
and left distributivity are derived rather than added as independent inputs.
The three remaining geometric premises must still be discharged from Plane.
-/
namespace TarskiField

variable {Point : Type u} [Plane Point]

/-- The Tarski axis is a Mathlib real-closed field once only the three
synthetic-geometric cores G, Pappus and Desargues are available.
All Field, LinearOrder and ordered-ring data are constructed from the
ORIGINAL AddGraph, MulGraph and geometric positive ray of the Tarski frame. -/
theorem axis_isRealClosed_of_three_geometric_cores_tarski
    [ContinuousPlane Point]
    (f : Frame Point)
    (hG : ∀ A B C D E F : Point,
      (∃ M : Point, MulMidpoint M A C ∧ MulMidpoint M B D) →
      (∃ N : Point, MulMidpoint N C E ∧ MulMidpoint N D F) →
      (∃ P : Point, MulMidpoint P A F ∧ MulMidpoint P B E))
    (hMulComm : MulCommLaw f)
    (hMulAssoc : MulAssocLaw f) :
    let hAdditive :=
      additive_laws_of_midpoint_quadrilateral_composition_tarski f
        (fun A B C D E F _ _ hQ₁ hQ₂ =>
          hG A B C D E F hQ₁ hQ₂)
    let hK := hAdditive.1
    let hAddAssoc := hAdditive.2.2
    let hDistrib :=
      leftDistrib_of_midpoint_and_composition_tarski f hK hG
    letI : Field (AxisPoint f) :=
      axisFieldOfGeometricLaws_tarski
        f hAddAssoc hMulComm hMulAssoc hDistrib
    letI : LinearOrder (AxisPoint f) :=
      axisLinearOrderOfMidpointAddAssoc_tarski f hK hAddAssoc
    letI : IsStrictOrderedRing (AxisPoint f) :=
      axisStrictOrderedRingOfGeometricLaws_tarski
        f hK hAddAssoc hMulComm hMulAssoc hDistrib
          (positiveMulClosed_tarski f)
    IsRealClosed (AxisPoint f) := by
  let hAdditive :=
    additive_laws_of_midpoint_quadrilateral_composition_tarski f
      (fun A B C D E F _ _ hQ₁ hQ₂ =>
        hG A B C D E F hQ₁ hQ₂)
  let hK := hAdditive.1
  let hAddAssoc := hAdditive.2.2
  let hDistrib :=
    leftDistrib_of_midpoint_and_composition_tarski f hK hG
  exact axis_isRealClosed_of_five_geometric_bridges_tarski
    f hK hAddAssoc hMulComm hMulAssoc hDistrib

end TarskiField

#print axioms TarskiField.axis_isRealClosed_of_three_geometric_cores_tarski


/-!
## A13 route: rigidity of a locally bounded additive map

Natural master §0.4. The two LUB hypotheses are precisely the finite
definable cuts to be supplied from A13, not completeness of all subsets.
No multiplication, division, Archimedean axiom, topology or field
instance is used in this lemma.
-/

namespace TarskiField

section A13AdditiveRigidity

variable {A : Type*} [AddCommGroup A] [LinearOrder A]
  [IsOrderedCancelAddMonoid A]

def rigidityRange (F : A →+ A) (u : A) : Set A :=
  {v | 0 ≤ v ∧ ∃ x, 0 ≤ x ∧ x ≤ u ∧ F x = v}

def rigidityKernel (F : A →+ A) (t : A) : Set A :=
  {x | 0 ≤ x ∧ x ≤ t ∧ F x = 0}

/-- Doubling modulo the distinguished positive period stays in the
nonnegative part of the image of the unit interval. -/
theorem rigidityRange_double
    (F : A →+ A) (u : A) (hFu : F u = 0)
    {v : A} (hv : v ∈ rigidityRange F u) :
    v + v ∈ rigidityRange F u := by
  obtain ⟨hv0, x, hx0, hxu, hxv⟩ := hv
  refine ⟨add_nonneg hv0 hv0, ?_⟩
  by_cases h : x + x ≤ u
  · exact ⟨x+x, add_nonneg hx0 hx0, h, by rw [map_add, hxv]⟩
  · refine ⟨x+x-u, sub_nonneg.mpr (le_of_lt (lt_of_not_ge h)),
      (sub_le_iff_le_add).mpr (add_le_add hxu hxu), ?_⟩
    rw [map_sub, map_add, hFu, sub_zero, hxv]

/-- A locally bounded additive map with a positive period is zero if
the image cut and the bounded kernel cuts have least upper bounds. -/
theorem additive_rigidity_of_two_lub_families
    (F : A →+ A) (u : A) (hu : 0 < u) (hFu : F u = 0)
    (hRange : ∃ b, IsLUB (rigidityRange F u) b)
    (hKernel : ∀ t : A, 0 ≤ t → ∃ b, IsLUB (rigidityKernel F t) b) :
    ∀ x : A, F x = 0 := by
  obtain ⟨b, hb⟩ := hRange
  have hRangeZero : ∀ v ∈ rigidityRange F u, v = 0 := by
    intro v hv
    by_contra hne
    have hvpos : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hne)
    have hUpper : b-v ∈ upperBounds (rigidityRange F u) := by
      intro w hw
      apply (le_sub_iff_add_le).mpr
      rcases le_total w v with h | h
      · exact (add_le_add_left h v).trans
          (hb.1 (rigidityRange_double F u hFu hv))
      · exact (add_le_add_right h w).trans
          (hb.1 (rigidityRange_double F u hFu hw))
    exact (not_lt_of_ge (hb.2 hUpper)) (sub_lt_self b hvpos)
  have hUnit : ∀ x : A, 0 ≤ x → x ≤ u → F x = 0 := by
    intro x hx0 hxu
    by_cases h : 0 ≤ F x
    · exact hRangeZero (F x) ⟨h, x, hx0, hxu, rfl⟩
    · have hneg : 0 ≤ F (u-x) := by
        rw [map_sub, hFu, zero_sub]
        exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge h))
      have hz := hRangeZero (F (u-x))
        ⟨hneg, u-x, sub_nonneg.mpr hxu, sub_le_self u hx0, rfl⟩
      simpa [map_sub, hFu] using hz
  have hNonneg : ∀ t : A, 0 ≤ t → F t = 0 := by
    intro t ht
    obtain ⟨c, hc⟩ := hKernel t ht
    have hc0 : 0 ≤ c := hc.1
      (show (0 : A) ∈ rigidityKernel F t from ⟨le_rfl, ht, map_zero F⟩)
    have hct : c ≤ t := hc.2 (by
      intro k hk
      exact hk.2.1)
    have hNear : ∀ d : A, d < c →
        ∃ k ∈ rigidityKernel F t, d < k := by
      intro d hd
      by_contra hn
      have hUpper : d ∈ upperBounds (rigidityKernel F t) := by
        intro k hk
        exact le_of_not_gt (fun h => hn ⟨k,hk,h⟩)
      exact (not_lt_of_ge (hc.2 hUpper)) hd
    have hEq : c = t := by
      by_contra hne
      have hgap : 0 < t-c := sub_pos.mpr (lt_of_le_of_ne hct hne)
      let s := min u (t-c)
      have hs : 0 < s := lt_min hu hgap
      have hsu : s ≤ u := min_le_left _ _
      have hsgap : s ≤ t-c := min_le_right _ _
      have hsF := hUnit s hs.le hsu
      obtain ⟨k,hk,hkl⟩ := hNear (c-s) (sub_lt_self c hs)
      have hksle : k+s ≤ t := calc
        k+s ≤ c+(t-c) := add_le_add (hc.1 hk) hsgap
        _ = t := by abel
      have hks : k+s ∈ rigidityKernel F t :=
        ⟨add_nonneg hk.1 hs.le, hksle, by rw [map_add,hk.2.2,hsF,add_zero]⟩
      have hlt : c < k+s := (sub_lt_iff_lt_add).mp hkl
      exact (not_lt_of_ge (hc.1 hks)) hlt
    obtain ⟨k,hk,hkl⟩ := hNear (t-u) (by rw [hEq]; exact sub_lt_self t hu)
    have htu : t-k ≤ u := by
      apply (sub_le_iff_le_add).mpr
      exact le_of_lt (by simpa [add_comm] using (sub_lt_iff_lt_add).mp hkl)
    have hz := hUnit (t-k) (sub_nonneg.mpr hk.2.1) htu
    simpa [map_sub, hk.2.2] using hz
  intro x
  by_cases hx : 0 ≤ x
  · exact hNonneg x hx
  · have hz := hNonneg (-x) (neg_nonneg.mpr (le_of_lt (lt_of_not_ge hx)))
    simpa using hz

end A13AdditiveRigidity
end TarskiField

#print axioms TarskiField.rigidityRange_double
#print axioms TarskiField.additive_rigidity_of_two_lub_families


namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

/-- A13 on a nonnegative, bounded, first-order definable subset of the
original axis containing O. This is the general cut needed for both
families in additive rigidity; no Field instance is used. -/
theorem axis_definable_nonnegative_lub_tarski
    [ContinuousPlane Point]
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point, MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hComm : AddCommLaw f) (hAssoc : AddAssocLaw f)
    {n : Nat} (l : Fin n) (lower : Formula (n+1))
    (params : Fin n → Point) (R : AxisPoint f)
    (hl : params l = f.O)
    (hZero : lower.eval (Fin.cons f.O params))
    (hAxis : ∀ X : Point, lower.eval (Fin.cons X params) → Col f.O f.I X)
    (hNonneg : ∀ x : AxisPoint f, lower.eval (Fin.cons x.1 params) →
      AxisLe f (axisZero f) x)
    (hBound : ∀ x : AxisPoint f, lower.eval (Fin.cons x.1 params) →
      AxisLe f x R) :
    letI : LinearOrder (AxisPoint f) :=
      axisLinearOrderOfMidpointAddAssoc_tarski f hK hAssoc
    ∃ b : AxisPoint f, IsLUB
      {x : AxisPoint f | lower.eval (Fin.cons x.1 params)} b := by
  letI : LinearOrder (AxisPoint f) :=
    axisLinearOrderOfMidpointAddAssoc_tarski f hK hAssoc
  have hBet (x y : AxisPoint f) (hy : axisZero f ≤ y) :
      Bet f.O x.1 y.1 ↔ axisZero f ≤ x ∧ x ≤ y := by
    have h := axisBet_iff_unoriented_order_bounds_tarski
      f hK hComm hAssoc (axisZero f) x y
    change Bet f.O x.1 y.1 ↔
      (axisZero f ≤ x ∧ x ≤ y) ∨ (y ≤ x ∧ x ≤ axisZero f) at h
    constructor
    · intro hb
      rcases h.mp hb with hf | hr
      · exact hf
      · exact ⟨le_trans hy hr.1, le_trans hr.2 hy⟩
    · intro hx
      exact h.mpr (Or.inl hx)
  have hR0 : axisZero f ≤ R := hBound (axisZero f) hZero
  have hUpperR : (upperBoundsFormula l lower).eval (Fin.cons R.1 params) := by
    apply (upperBoundsFormula_eval l lower params R.1).mpr
    intro X hX
    let x : AxisPoint f := ⟨X, hAxis X hX⟩
    rw [hl]
    exact (hBet x R hR0).mpr ⟨hNonneg x hX, hBound x hX⟩
  have hlAxis : Col f.O f.I (params l) := by
    rw [hl]
    exact (axisZero f).2
  have hlZero : lower.eval (Fin.cons (params l) params) := by
    rw [hl]
    exact hZero
  obtain ⟨b, ⟨hbSegment, hbUpper, hbLeast⟩, _⟩ :=
    upperBounds_cut_A13_internal_scalar_tarski
      f l lower params R.1 hlAxis R.2 hlZero hUpperR
  have hb0 : axisZero f ≤ b := by
    apply ((hBet b R hR0).mp ?_).1
    simpa only [hl] using hbSegment
  refine ⟨b, ?_, ?_⟩
  · intro x hx
    have h := (upperBoundsFormula_eval l lower params b.1).mp hbUpper x.1 hx
    rw [hl] at h
    exact ((hBet x b hb0).mp h).2
  · intro y hy
    have hy0 : axisZero f ≤ y := hy hZero
    have hyUpper : (upperBoundsFormula l lower).eval (Fin.cons y.1 params) := by
      apply (upperBoundsFormula_eval l lower params y.1).mpr
      intro X hX
      let x : AxisPoint f := ⟨X, hAxis X hX⟩
      rw [hl]
      exact (hBet x y hy0).mpr ⟨hNonneg x hX, hy hX⟩
    have h := hbLeast y.1 hyUpper
    rw [hl] at h
    exact ((hBet b y hy0).mp h).2

end TarskiField

#print axioms TarskiField.axis_definable_nonnegative_lub_tarski


namespace TarskiField
variable {Point : Type u} [Plane Point]

/-- Only the additive laws are needed for this stage. The operations
are definitionally the original geometric ones. -/
@[instance_reducible] noncomputable def axisAddCommGroupOfLaws_tarski
    (f : Frame Point) (hComm : AddCommLaw f) (hAssoc : AddAssocLaw f) :
    AddCommGroup (AxisPoint f) := by
  let hAdd := (operation_graphs_total_tarski f).1
  letI : Add (AxisPoint f) := ⟨axisAddOf f hAdd⟩
  letI : Neg (AxisPoint f) := ⟨axisNegOf f⟩
  letI : Zero (AxisPoint f) := ⟨axisZero f⟩
  let G : AddGroup (AxisPoint f) := AddGroup.ofLeftAxioms
    (axisAddOf_assoc_of_law f hAdd hAssoc)
    (axisAddOf_zero_left f hAdd)
    (fun x => (addGraph_iff_axisAddOf_eq f hAdd
      (axisNegOf f x) x (axisZero f)).mp (axisNegOf_left_inverse_tarski f x))
  exact { G with add_comm := axisAddOf_comm_of_law f hAdd hComm }

/-- The geometric positive displacement is invariant under addition.
This is the ordered group portion of the existing ordered field proof,
with the multiplication hypotheses removed. -/
theorem axisOrderedAddGroupCompatibility_tarski
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point, MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hComm : AddCommLaw f) (hAssoc : AddAssocLaw f) :
    letI : AddCommGroup (AxisPoint f) :=
      axisAddCommGroupOfLaws_tarski f hComm hAssoc
    letI : LinearOrder (AxisPoint f) :=
      axisLinearOrderOfMidpointAddAssoc_tarski f hK hAssoc
    IsOrderedCancelAddMonoid (AxisPoint f) := by
  letI : AddCommGroup (AxisPoint f) :=
    axisAddCommGroupOfLaws_tarski f hComm hAssoc
  letI : LinearOrder (AxisPoint f) :=
    axisLinearOrderOfMidpointAddAssoc_tarski f hK hAssoc
  apply IsOrderedCancelAddMonoid.of_add_lt_add_left
  intro t x y hxy
  change AxisLt f x y at hxy
  obtain ⟨d, hd, hp⟩ := hxy
  let hAdd := (operation_graphs_total_tarski f).1
  have hxy' : x + d = y := (addGraph_iff_axisAddOf_eq f hAdd x d y).mp hd
  change AxisLt f (t+x) (t+y)
  refine ⟨d, ?_, hp⟩
  apply (addGraph_iff_axisAddOf_eq f hAdd (t+x) d (t+y)).mpr
  change (t+x)+d = t+y
  rw [add_assoc, hxy']

end TarskiField

#print axioms TarskiField.axisAddCommGroupOfLaws_tarski
#print axioms TarskiField.axisOrderedAddGroupCompatibility_tarski


namespace TarskiField
variable {Point : Type u} [Plane Point]

/-- Interpretation of finite expressions without using a Field instance. -/
noncomputable def axisExprValue_tarski
    (f : Frame Point) {n : Nat} (σ : Fin n → AxisPoint f) :
    ScalarExpr n → AxisPoint f
  | .var v => σ v
  | .zero => axisZero f
  | .one => axisOne f
  | .add e d => axisAddOf f (operation_graphs_total_tarski f).1
      (axisExprValue_tarski f σ e) (axisExprValue_tarski f σ d)
  | .mul e d => axisMulOf f (operation_graphs_total_tarski f).2
      (axisExprValue_tarski f σ e) (axisExprValue_tarski f σ d)

theorem axisExprValue_iff_geomValue_tarski
    (f : Frame Point) {n : Nat} (σ : Fin n → AxisPoint f)
    (e : ScalarExpr n) (z : AxisPoint f) :
    e.geomValue f.O f.I f.J (fun v => (σ v).1) z.1 ↔
      axisExprValue_tarski f σ e = z := by
  induction e generalizing z with
  | var v =>
    change (Col f.O f.I z.1 ∧ z.1 = (σ v).1) ↔ σ v = z
    exact ⟨fun h => Subtype.ext h.2.symm,
      fun h => ⟨z.2, congrArg Subtype.val h.symm⟩⟩
  | zero =>
    change (Col f.O f.I z.1 ∧ z.1 = f.O) ↔ axisZero f = z
    exact ⟨fun h => Subtype.ext h.2.symm,
      fun h => ⟨z.2, congrArg Subtype.val h.symm⟩⟩
  | one =>
    change (Col f.O f.I z.1 ∧ z.1 = f.I) ↔ axisOne f = z
    exact ⟨fun h => Subtype.ext h.2.symm,
      fun h => ⟨z.2, congrArg Subtype.val h.symm⟩⟩
  | add e d ihe ihd =>
    constructor
    · rintro ⟨_, p, q, hp, hq, hraw⟩
      let a : AxisPoint f := ⟨p, e.geomValue_axis f.O f.I f.J _ p hp⟩
      let b : AxisPoint f := ⟨q, d.geomValue_axis f.O f.I f.J _ q hq⟩
      have ha := (ihe a).mp hp
      have hb := (ihd b).mp hq
      change axisAddOf f (operation_graphs_total_tarski f).1
        (axisExprValue_tarski f σ e) (axisExprValue_tarski f σ d) = z
      rw [ha,hb]
      exact (addGraph_iff_axisAddOf_eq f _ a b z).mp
        ((rawAddGraph_axis_iff f a b z).mp hraw)
    · intro h
      let a := axisExprValue_tarski f σ e
      let b := axisExprValue_tarski f σ d
      refine ⟨z.2,a.1,b.1,(ihe a).mpr rfl,(ihd b).mpr rfl,?_⟩
      apply (rawAddGraph_axis_iff f a b z).mpr
      exact (addGraph_iff_axisAddOf_eq f _ a b z).mpr h
  | mul e d ihe ihd =>
    constructor
    · rintro ⟨_, p, q, hp, hq, hraw⟩
      let a : AxisPoint f := ⟨p, e.geomValue_axis f.O f.I f.J _ p hp⟩
      let b : AxisPoint f := ⟨q, d.geomValue_axis f.O f.I f.J _ q hq⟩
      have ha := (ihe a).mp hp
      have hb := (ihd b).mp hq
      change axisMulOf f (operation_graphs_total_tarski f).2
        (axisExprValue_tarski f σ e) (axisExprValue_tarski f σ d) = z
      rw [ha,hb]
      exact (mulGraph_iff_axisMulOf_eq f _ a b z).mp
        ((rawMulGraph_axis_iff f a b z).mp hraw)
    · intro h
      let a := axisExprValue_tarski f σ e
      let b := axisExprValue_tarski f σ d
      refine ⟨z.2,a.1,b.1,(ihe a).mpr rfl,(ihd b).mpr rfl,?_⟩
      apply (rawMulGraph_axis_iff f a b z).mpr
      exact (mulGraph_iff_axisMulOf_eq f _ a b z).mpr h

/-- The difference relation E-D=v is expressed without subtraction:
evaluate E and D and require D+v=E. -/
def exprDifferenceFormula {n m : Nat} (o i j v : Fin m)
    (vars : Fin n → Fin m) (e d : ScalarExpr n) : Formula m :=
  .ex (.ex (.conj
    (scalarExprFormula o.succ.succ i.succ.succ j.succ.succ 1
      (fun k => (vars k).succ.succ) e)
    (.conj
      (scalarExprFormula o.succ.succ i.succ.succ j.succ.succ 0
        (fun k => (vars k).succ.succ) d)
      (addGraphFormula o.succ.succ i.succ.succ j.succ.succ
        0 v.succ.succ 1))))

theorem exprDifferenceFormula_eval_tarski
    (f : Frame Point) {n m : Nat} (o i j v : Fin m)
    (vars : Fin n → Fin m) (e d : ScalarExpr n)
    (ρ : Fin m → Point) (σ : Fin n → AxisPoint f) (a : AxisPoint f)
    (ho : ρ o = f.O) (hi : ρ i = f.I) (hj : ρ j = f.J)
    (hv : ρ v = a.1) (hvars : ∀ k, ρ (vars k) = (σ k).1) :
    (exprDifferenceFormula o i j v vars e d).eval ρ ↔
      AddGraph f (axisExprValue_tarski f σ d) a (axisExprValue_tarski f σ e) := by
  simp only [exprDifferenceFormula, Formula.eval, scalarExprFormula_eval,
    addGraphFormula_raw_eval, Fin.cons_zero, Fin.cons_succ, ho, hi, hj, hv, hvars]
  constructor
  · rintro ⟨p,q,hp,hq,hraw⟩
    let x : AxisPoint f := ⟨p, e.geomValue_axis f.O f.I f.J _ p hp⟩
    let y : AxisPoint f := ⟨q, d.geomValue_axis f.O f.I f.J _ q hq⟩
    have hx := (axisExprValue_iff_geomValue_tarski f σ e x).mp hp
    have hy := (axisExprValue_iff_geomValue_tarski f σ d y).mp hq
    rw [hx,hy]
    exact (rawAddGraph_axis_iff f y a x).mp hraw
  · intro h
    let x := axisExprValue_tarski f σ e
    let y := axisExprValue_tarski f σ d
    exact ⟨x.1,y.1,
      (axisExprValue_iff_geomValue_tarski f σ e x).mpr rfl,
      (axisExprValue_iff_geomValue_tarski f σ d y).mpr rfl,
      (rawAddGraph_axis_iff f y a x).mpr h⟩

end TarskiField

#print axioms TarskiField.axisExprValue_iff_geomValue_tarski
#print axioms TarskiField.exprDifferenceFormula_eval_tarski


namespace TarskiField
variable {Point : Type u} [Plane Point]
open Plane

-- Free slots after the varying point: O,I,J,a,b,t.
def rigidityCutParams (f : Frame Point) (a b t : AxisPoint f) :
    Fin 6 → Point := ![f.O,f.I,f.J,a.1,b.1,t.1]

-- The three expression variables are x,a,b. The range formula
-- existentially quantifies x while its free point is the output v.
def axisRigidityRangeFormula (e d : ScalarExpr 3) : Formula 7 :=
  .conj (nonnegPointFormula 1 2 0)
    (.ex (.conj (colFormula 2 3 0)
      (.conj (.bet 2 0 3)
        (exprDifferenceFormula 2 3 4 1 ![0,5,6] e d))))

def axisRigidityKernelFormula (e d : ScalarExpr 3) : Formula 7 :=
  .conj (colFormula 1 2 0)
    (.conj (.bet 1 0 6)
      (exprDifferenceFormula 1 2 3 1 ![0,4,5] e d))

theorem axisRigidityRangeFormula_axis_tarski
    (f : Frame Point) (a b t : AxisPoint f) (e d : ScalarExpr 3)
    (V : Point) (h : (axisRigidityRangeFormula e d).eval
      (Fin.cons V (rigidityCutParams f a b t))) : Col f.O f.I V := by
  have hh := (nonnegPointFormula_eval (1 : Fin 7) 2 0
    (Fin.cons V (rigidityCutParams f a b t))).mp h.1
  exact hh.1

theorem axisRigidityKernelFormula_axis_tarski
    (f : Frame Point) (a b t : AxisPoint f) (e d : ScalarExpr 3)
    (X : Point) (h : (axisRigidityKernelFormula e d).eval
      (Fin.cons X (rigidityCutParams f a b t))) : Col f.O f.I X := by
  exact (colFormula_eval (1 : Fin 7) 2 0
    (Fin.cons X (rigidityCutParams f a b t))).mp h.1

/-- Exact finite formula for the nonnegative error image. -/
theorem axisRigidityRangeFormula_eval_tarski
    (f : Frame Point) (a b t v : AxisPoint f) (e d : ScalarExpr 3) :
    (axisRigidityRangeFormula e d).eval
        (Fin.cons v.1 (rigidityCutParams f a b t)) ↔
    AxisNonneg f v ∧ ∃ x : AxisPoint f, Bet f.O x.1 f.I ∧
      AddGraph f (axisExprValue_tarski f ![x,a,b] d) v
        (axisExprValue_tarski f ![x,a,b] e) := by
  have hNonneg :
      (nonnegPointFormula (1 : Fin 7) 2 0).eval
        (Fin.cons v.1 (rigidityCutParams f a b t)) ↔ AxisNonneg f v := by
    rw [axis_nonneg_iff_ray_or_origin]
    constructor
    · intro h
      exact ((nonnegPointFormula_eval _ _ _ _).mp h).2
    · intro h
      exact (nonnegPointFormula_eval _ _ _ _).mpr ⟨v.2,h⟩
  have hDiff (x : AxisPoint f) :=
    exprDifferenceFormula_eval_tarski f (2 : Fin 8) 3 4 1
      ![0,5,6] e d
      (Fin.cons x.1 (Fin.cons v.1 (rigidityCutParams f a b t)))
      ![x,a,b] v rfl rfl rfl rfl (by intro k; fin_cases k <;> rfl)
  change (nonnegPointFormula (1 : Fin 7) 2 0).eval
      (Fin.cons v.1 (rigidityCutParams f a b t)) ∧
    (∃ X : Point,
      (colFormula (2 : Fin 8) 3 0).eval
        (Fin.cons X (Fin.cons v.1 (rigidityCutParams f a b t))) ∧
      Bet f.O X f.I ∧
      (exprDifferenceFormula (2 : Fin 8) 3 4 1 ![0,5,6] e d).eval
        (Fin.cons X (Fin.cons v.1 (rigidityCutParams f a b t)))) ↔ _
  rw [hNonneg]
  constructor
  · rintro ⟨hv,X,hX,hBet,hE⟩
    let x : AxisPoint f := ⟨X,(colFormula_eval _ _ _ _).mp hX⟩
    exact ⟨hv,x,hBet,(hDiff x).mp hE⟩
  · rintro ⟨hv,x,hBet,hE⟩
    exact ⟨hv,x.1,(colFormula_eval _ _ _ _).mpr x.2,hBet,(hDiff x).mpr hE⟩

theorem axisRigidityKernelFormula_eval_tarski
    (f : Frame Point) (a b t x : AxisPoint f) (e d : ScalarExpr 3) :
    (axisRigidityKernelFormula e d).eval
        (Fin.cons x.1 (rigidityCutParams f a b t)) ↔
    Bet f.O x.1 t.1 ∧
      AddGraph f (axisExprValue_tarski f ![x,a,b] d) (axisZero f)
        (axisExprValue_tarski f ![x,a,b] e) := by
  have hDiff := exprDifferenceFormula_eval_tarski f (1 : Fin 7) 2 3 1
    ![0,4,5] e d (Fin.cons x.1 (rigidityCutParams f a b t))
    ![x,a,b] (axisZero f) rfl rfl rfl rfl (by intro k; fin_cases k <;> rfl)
  change (colFormula (1 : Fin 7) 2 0).eval
      (Fin.cons x.1 (rigidityCutParams f a b t)) ∧
    Bet f.O x.1 t.1 ∧
    (exprDifferenceFormula (1 : Fin 7) 2 3 1 ![0,4,5] e d).eval
      (Fin.cons x.1 (rigidityCutParams f a b t)) ↔ _
  rw [hDiff]
  exact ⟨fun h => h.2, fun h => ⟨(colFormula_eval _ _ _ _).mpr x.2,h⟩⟩

end TarskiField
#print axioms TarskiField.axisRigidityRangeFormula_eval_tarski
#print axioms TarskiField.axisRigidityKernelFormula_eval_tarski


namespace TarskiField
variable {Point : Type u} [Plane Point]
open Plane

/-- A13 rigidity for precisely the differences of finite expressions
needed by the three multiplication laws. The only analytic premise
is a bound on the error on the geometric unit interval. -/
theorem axis_expr_difference_rigidity_tarski
    [ContinuousPlane Point]
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point, MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hComm : AddCommLaw f) (hAssoc : AddAssocLaw f)
    (a b : AxisPoint f) (e d : ScalarExpr 3) :
    letI : AddCommGroup (AxisPoint f) :=
      axisAddCommGroupOfLaws_tarski f hComm hAssoc
    letI : LinearOrder (AxisPoint f) :=
      axisLinearOrderOfMidpointAddAssoc_tarski f hK hAssoc
    ∀ F : AxisPoint f →+ AxisPoint f,
      (∀ x : AxisPoint f, F x =
        axisExprValue_tarski f ![x,a,b] e -
        axisExprValue_tarski f ![x,a,b] d) →
      F (axisOne f) = 0 →
      (∃ R : AxisPoint f, ∀ x : AxisPoint f,
        0 ≤ x → x ≤ axisOne f → F x ≤ R) →
      ∀ x : AxisPoint f, F x = 0 := by
  letI : AddCommGroup (AxisPoint f) :=
    axisAddCommGroupOfLaws_tarski f hComm hAssoc
  letI : LinearOrder (AxisPoint f) :=
    axisLinearOrderOfMidpointAddAssoc_tarski f hK hAssoc
  letI : IsOrderedCancelAddMonoid (AxisPoint f) :=
    axisOrderedAddGroupCompatibility_tarski f hK hComm hAssoc
  intro F hF hFu hBound
  have hu : (0 : AxisPoint f) < axisOne f :=
    (axisPositiveNonneg_iff_order_tarski f hK hAssoc (axisOne f)).1.mp
      (axisOne_positive f)
  have hBet (x t : AxisPoint f) (ht : 0 ≤ t) :
      Bet f.O x.1 t.1 ↔ 0 ≤ x ∧ x ≤ t := by
    have h := axisBet_iff_unoriented_order_bounds_tarski
      f hK hComm hAssoc (axisZero f) x t
    change Bet f.O x.1 t.1 ↔
      (0 ≤ x ∧ x ≤ t) ∨ (t ≤ x ∧ x ≤ 0) at h
    constructor
    · intro hb
      rcases h.mp hb with hh | hh
      · exact hh
      · exact ⟨le_trans ht hh.1, le_trans hh.2 ht⟩
    · intro hb
      exact h.mpr (Or.inl hb)
  have hDifference (x v : AxisPoint f) :
      AddGraph f (axisExprValue_tarski f ![x,a,b] d) v
        (axisExprValue_tarski f ![x,a,b] e) ↔ F x = v := by
    rw [hF x, addGraph_iff_axisAddOf_eq f (operation_graphs_total_tarski f).1]
    change _ + v = _ ↔ _ - _ = v
    rw [sub_eq_iff_eq_add]
    constructor <;> intro h <;> simpa [add_comm] using h.symm
  obtain ⟨R,hR⟩ := hBound
  let ρ := rigidityCutParams f a b R
  have hRange (v : AxisPoint f) :
      (axisRigidityRangeFormula e d).eval (Fin.cons v.1 ρ) ↔
      v ∈ rigidityRange F (axisOne f) := by
    rw [axisRigidityRangeFormula_eval_tarski]
    change AxisNonneg f v ∧ _ ↔ 0 ≤ v ∧ _
    rw [(axisPositiveNonneg_iff_order_tarski f hK hAssoc v).2]
    constructor
    · rintro ⟨hv,x,hx,hE⟩
      exact ⟨hv,x,((hBet x _ hu.le).mp hx).1,
        ((hBet x _ hu.le).mp hx).2,(hDifference x v).mp hE⟩
    · rintro ⟨hv,x,hx0,hxu,hE⟩
      exact ⟨hv,x,(hBet x _ hu.le).mpr ⟨hx0,hxu⟩,(hDifference x v).mpr hE⟩
  have hRangeLub : ∃ c, IsLUB (rigidityRange F (axisOne f)) c := by
    have hz : (axisRigidityRangeFormula e d).eval (Fin.cons f.O ρ) :=
      (hRange (axisZero f)).mpr ⟨le_rfl,axisZero f,le_rfl,hu.le,map_zero F⟩
    obtain ⟨c,hc⟩ := axis_definable_nonnegative_lub_tarski
      f hK hComm hAssoc (0 : Fin 6) (axisRigidityRangeFormula e d)
      ρ R rfl hz
      (axisRigidityRangeFormula_axis_tarski f a b R e d)
      (fun v hv => ((hRange v).mp hv).1)
      (by
        intro v hv
        obtain ⟨_,x,hx0,hxu,hxv⟩ := (hRange v).mp hv
        rw [← hxv]
        exact hR x hx0 hxu)
    have heq : {v : AxisPoint f |
        (axisRigidityRangeFormula e d).eval (Fin.cons v.1 ρ)} =
        rigidityRange F (axisOne f) :=
      Set.ext hRange
    rw [heq] at hc
    exact ⟨c,hc⟩
  have hKernelLub : ∀ t : AxisPoint f, 0 ≤ t →
      ∃ c, IsLUB (rigidityKernel F t) c := by
    intro t ht
    let σ := rigidityCutParams f a b t
    have hKernel (x : AxisPoint f) :
        (axisRigidityKernelFormula e d).eval (Fin.cons x.1 σ) ↔
        x ∈ rigidityKernel F t := by
      rw [axisRigidityKernelFormula_eval_tarski, hBet x t ht,
        hDifference x (axisZero f)]
      exact and_assoc
    have hz : (axisRigidityKernelFormula e d).eval (Fin.cons f.O σ) :=
      (hKernel (axisZero f)).mpr ⟨le_rfl,ht,map_zero F⟩
    obtain ⟨c,hc⟩ := axis_definable_nonnegative_lub_tarski
      f hK hComm hAssoc (0 : Fin 6) (axisRigidityKernelFormula e d)
      σ t rfl hz
      (axisRigidityKernelFormula_axis_tarski f a b t e d)
      (fun x hx => ((hKernel x).mp hx).1)
      (fun x hx => ((hKernel x).mp hx).2.1)
    have heq : {x : AxisPoint f |
        (axisRigidityKernelFormula e d).eval (Fin.cons x.1 σ)} =
        rigidityKernel F t := Set.ext hKernel
    rw [heq] at hc
    exact ⟨c,hc⟩
  exact additive_rigidity_of_two_lub_families
    F (axisOne f) hu hFu hRangeLub hKernelLub

end TarskiField
#print axioms TarskiField.axis_expr_difference_rigidity_tarski


namespace TarskiField

section SignedAdditiveBounds
variable {A : Type*} [AddCommGroup A] [LinearOrder A]
  [IsOrderedCancelAddMonoid A]

/-- A signed additive map is monotone or antitone, hence bounded on
each closed interval by its two endpoint values. -/
theorem additiveHom_interval_bounds_of_sign
    (H : A →+ A)
    (hSign : (∀ d : A, 0 < d → 0 ≤ H d) ∨
      (∀ d : A, 0 < d → H d ≤ 0))
    (l r x : A) (hl : l ≤ x) (hr : x ≤ r) :
    min (H l) (H r) ≤ H x ∧ H x ≤ max (H l) (H r) := by
  rcases hSign with hs | hs
  · have hm : Monotone H := by
      intro p q hpq
      rcases lt_or_eq_of_le hpq with hpq | heq
      · have h := hs (q-p) (sub_pos.mpr hpq)
        rw [map_sub] at h
        exact sub_nonneg.mp h
      · rw [heq]
    exact ⟨(min_le_left _ _).trans (hm hl), (hm hr).trans (le_max_right _ _)⟩
  · have hm : Antitone H := by
      intro p q hpq
      rcases lt_or_eq_of_le hpq with hpq | heq
      · have h := hs (q-p) (sub_pos.mpr hpq)
        rw [map_sub] at h
        exact sub_nonpos.mp h
      · rw [heq]
    exact ⟨(min_le_right _ _).trans (hm hr), (hm hl).trans (le_max_left _ _)⟩
end SignedAdditiveBounds

variable {Point : Type u} [Plane Point]
open Plane

/-- Natural master §0.4: A13 replaces the two independent Pappus and
Desargues geometric cores. The only input laws are those supplied by G. -/
theorem mulLaws_of_A13_additive_rigidity_tarski
    [ContinuousPlane Point]
    (f : Frame Point)
    (hK : ∀ a d b : AxisPoint f,
      AddGraph f a d b ↔
        ∃ M : Point, MulMidpoint M f.O b.1 ∧ MulMidpoint M a.1 d.1)
    (hComm : AddCommLaw f) (hAssoc : AddAssocLaw f)
    (hDistrib : LeftDistributiveLaw f) :
    MulCommLaw f ∧ MulAssocLaw f := by
  letI : AddCommGroup (AxisPoint f) :=
    axisAddCommGroupOfLaws_tarski f hComm hAssoc
  letI : LinearOrder (AxisPoint f) :=
    axisLinearOrderOfMidpointAddAssoc_tarski f hK hAssoc
  letI : IsOrderedCancelAddMonoid (AxisPoint f) :=
    axisOrderedAddGroupCompatibility_tarski f hK hComm hAssoc
  let hAdd := (operation_graphs_total_tarski f).1
  let hMul := (operation_graphs_total_tarski f).2
  let m := axisMulOf f hMul
  let u := axisOne f
  have hOneRight : ∀ a : AxisPoint f, m a u = a :=
    axisMulOf_one_right f hMul
  have hOneLeft : ∀ a : AxisPoint f, m u a = a :=
    axisMulOf_one_left_of_law f hMul (mulKernel_tarski f).2.2.1
  have hZeroRight : ∀ a : AxisPoint f, m a 0 = 0 :=
    axisMulOf_zero_right f hMul
  have hZeroLeft : ∀ a : AxisPoint f, m 0 a = 0 :=
    axisMulOf_zero_left_tarski f hMul
  let L : AxisPoint f → (AxisPoint f →+ AxisPoint f) :=
    fun a => { toFun := m a
               map_zero' := hZeroRight a
               map_add' := axisMulOf_left_distrib_of_law f hAdd hMul hDistrib a }
  have hPos (x : AxisPoint f) : Positive f x ↔ 0 < x :=
    (axisPositiveNonneg_iff_order_tarski f hK hAssoc x).1
  have hMulPos (a d : AxisPoint f) (ha : 0 < a) (hd : 0 < d) :
      0 < m a d :=
    (hPos (m a d)).mp
      (positiveMulClosed_tarski f a d (m a d)
        ((hPos a).mpr ha) ((hPos d).mpr hd) (axisMulOf_spec f hMul a d))
  have hMulNegLeft (a d : AxisPoint f) (ha : a < 0) (hd : 0 < d) :
      m a d < 0 := by
    have haNe : a.1 ≠ f.O := by
      intro h
      exact (ne_of_lt ha) (Subtype.ext h)
    have hOut := mul_same_ray_of_positive_right_tarski
      f a d (m a d) haNe ((hPos d).mpr hd) (axisMulOf_spec f hMul a d)
    rcases lt_trichotomy (m a d) 0 with h | h | h
    · exact h
    · exact False.elim (hOut.2.1 (congrArg Subtype.val h))
    · have hRev : Out f.O (m a d).1 a.1 :=
        ⟨hOut.2.1,hOut.1,hOut.2.2.symm⟩
      have hpa := (hPos a).mp (out_trans_tarski ((hPos (m a d)).mpr h) hRev)
      exact False.elim ((not_lt_of_ge ha.le) hpa)
  have hLBound (a l r x : AxisPoint f) (hl : l ≤ x) (hr : x ≤ r) :
      min (m a l) (m a r) ≤ m a x ∧
        m a x ≤ max (m a l) (m a r) := by
    apply additiveHom_interval_bounds_of_sign (L a) ?_ l r x hl hr
    rcases lt_trichotomy a 0 with ha | ha | ha
    · exact Or.inr (fun d hd => (hMulNegLeft a d ha hd).le)
    · exact Or.inl (fun d _ => by change 0 ≤ m a d; rw [ha,hZeroLeft])
    · exact Or.inl (fun d hd => (hMulPos a d ha hd).le)
  -- Associativity: compare the two additive maps x ↦ a*(b*x), (a*b)*x.
  have hMulAssoc (a b x : AxisPoint f) :
      m (m a b) x = m a (m b x) := by
    let F := (L a).comp (L b) - L (m a b)
    have hFu : F u = 0 := by
      change m a (m b u) - m (m a b) u = 0
      rw [hOneRight b,hOneRight (m a b),sub_self]
    have hBound : ∃ R : AxisPoint f, ∀ x : AxisPoint f,
        0 ≤ x → x ≤ u → F x ≤ R := by
      let l := min (m b 0) (m b u)
      let r := max (m b 0) (m b u)
      refine ⟨max (m a l) (m a r) -
        min (m (m a b) 0) (m (m a b) u),?_⟩
      intro x hx0 hxu
      have hb := hLBound b 0 u x hx0 hxu
      have hab := hLBound a l r (m b x) hb.1 hb.2
      have hc := hLBound (m a b) 0 u x hx0 hxu
      exact sub_le_sub hab.2 hc.1
    have h := axis_expr_difference_rigidity_tarski f hK hComm hAssoc a b
      (.mul (.var 1) (.mul (.var 2) (.var 0)))
      (.mul (.mul (.var 1) (.var 2)) (.var 0))
      F (by intro x; rfl) hFu hBound x
    exact (sub_eq_zero.mp (show m a (m b x) - m (m a b) x = 0 from h)).symm
  -- Right distributivity: compare L_(a+b) to L_a + L_b.
  have hRightDistrib (a b x : AxisPoint f) :
      m (a+b) x = m a x + m b x := by
    let F := L (a+b) - (L a + L b)
    have hFu : F u = 0 := by
      change m (a+b) u - (m a u + m b u) = 0
      rw [hOneRight,hOneRight,hOneRight,sub_self]
    have hBound : ∃ R : AxisPoint f, ∀ x : AxisPoint f,
        0 ≤ x → x ≤ u → F x ≤ R := by
      refine ⟨max (m (a+b) 0) (m (a+b) u) -
        (min (m a 0) (m a u) + min (m b 0) (m b u)),?_⟩
      intro x hx0 hxu
      have hab := hLBound (a+b) 0 u x hx0 hxu
      have ha := hLBound a 0 u x hx0 hxu
      have hb := hLBound b 0 u x hx0 hxu
      exact sub_le_sub hab.2 (add_le_add ha.1 hb.1)
    have h := axis_expr_difference_rigidity_tarski f hK hComm hAssoc a b
      (.mul (.add (.var 1) (.var 2)) (.var 0))
      (.add (.mul (.var 1) (.var 0)) (.mul (.var 2) (.var 0)))
      F (by intro x; rfl) hFu hBound x
    exact sub_eq_zero.mp (show m (a+b) x - (m a x + m b x) = 0 from h)
  let R : AxisPoint f → (AxisPoint f →+ AxisPoint f) :=
    fun a => { toFun := fun x => m x a
               map_zero' := hZeroLeft a
               map_add' := fun x y => hRightDistrib x y a }
  have hRBound (a l r x : AxisPoint f) (hl : l ≤ x) (hr : x ≤ r) :
      min (m l a) (m r a) ≤ m x a ∧
        m x a ≤ max (m l a) (m r a) := by
    apply additiveHom_interval_bounds_of_sign (R a) ?_ l r x hl hr
    rcases lt_trichotomy a 0 with ha | ha | ha
    · refine Or.inr (fun d hd => ?_)
      have hp := hMulPos d (-a) hd (neg_pos.mpr ha)
      have hn : m d (-a) = -(m d a) := map_neg (L d) a
      rw [hn] at hp
      exact (neg_pos.mp hp).le
    · exact Or.inl (fun d _ => by change 0 ≤ m d a; rw [ha,hZeroRight])
    · exact Or.inl (fun d hd => (hMulPos d a hd ha).le)
  -- Commutativity: both right and left multiplication are now additive.
  have hMulComm (a x : AxisPoint f) : m x a = m a x := by
    let F := R a - L a
    have hFu : F u = 0 := by
      change m u a - m a u = 0
      rw [hOneLeft,hOneRight,sub_self]
    have hBound : ∃ B : AxisPoint f, ∀ x : AxisPoint f,
        0 ≤ x → x ≤ u → F x ≤ B := by
      refine ⟨max (m 0 a) (m u a) - min (m a 0) (m a u),?_⟩
      intro x hx0 hxu
      exact sub_le_sub (hRBound a 0 u x hx0 hxu).2
        (hLBound a 0 u x hx0 hxu).1
    have h := axis_expr_difference_rigidity_tarski f hK hComm hAssoc a (axisZero f)
      (.mul (.var 0) (.var 1)) (.mul (.var 1) (.var 0))
      F (by intro x; rfl) hFu hBound x
    exact sub_eq_zero.mp (show m x a - m a x = 0 from h)
  constructor
  · intro a b z hab
    apply (mulGraph_iff_axisMulOf_eq f hMul b a z).mpr
    exact (hMulComm a b).trans ((mulGraph_iff_axisMulOf_eq f hMul a b z).mp hab)
  · intro a b c ab bc lhs rhs hab hl hbc hr
    have eab := (mulGraph_iff_axisMulOf_eq f hMul a b ab).mp hab
    have ebc := (mulGraph_iff_axisMulOf_eq f hMul b c bc).mp hbc
    calc
      lhs = m ab c := ((mulGraph_iff_axisMulOf_eq f hMul ab c lhs).mp hl).symm
      _ = m (m a b) c := congrArg (fun z => m z c) eab.symm
      _ = m a (m b c) := hMulAssoc a b c
      _ = m a bc := congrArg (m a) ebc
      _ = rhs := (mulGraph_iff_axisMulOf_eq f hMul a bc rhs).mp hr

/-- The final target reduced to one remaining geometric theorem G.
The multiplicative laws are consequences of A13, not hypotheses. -/
theorem axis_isRealClosed_of_G_A13_tarski
    [ContinuousPlane Point]
    (f : Frame Point)
    (hG : ∀ A B C D E F : Point,
      (∃ M : Point, MulMidpoint M A C ∧ MulMidpoint M B D) →
      (∃ N : Point, MulMidpoint N C E ∧ MulMidpoint N D F) →
      (∃ P : Point, MulMidpoint P A F ∧ MulMidpoint P B E)) :
    let hAdditive :=
      additive_laws_of_midpoint_quadrilateral_composition_tarski f
        (fun A B C D E F _ _ hQ₁ hQ₂ => hG A B C D E F hQ₁ hQ₂)
    let hK := hAdditive.1
    let hComm := hAdditive.2.1
    let hAssoc := hAdditive.2.2
    let hDistrib := leftDistrib_of_midpoint_and_composition_tarski f hK hG
    let hMul := mulLaws_of_A13_additive_rigidity_tarski f hK hComm hAssoc hDistrib
    letI : Field (AxisPoint f) :=
      axisFieldOfGeometricLaws_tarski f hAssoc hMul.1 hMul.2 hDistrib
    letI : LinearOrder (AxisPoint f) :=
      axisLinearOrderOfMidpointAddAssoc_tarski f hK hAssoc
    letI : IsStrictOrderedRing (AxisPoint f) :=
      axisStrictOrderedRingOfGeometricLaws_tarski f hK hAssoc
        hMul.1 hMul.2 hDistrib (positiveMulClosed_tarski f)
    IsRealClosed (AxisPoint f) := by
  let hAdditive :=
    additive_laws_of_midpoint_quadrilateral_composition_tarski f
      (fun A B C D E F _ _ hQ₁ hQ₂ => hG A B C D E F hQ₁ hQ₂)
  let hK := hAdditive.1
  let hComm := hAdditive.2.1
  let hAssoc := hAdditive.2.2
  let hDistrib := leftDistrib_of_midpoint_and_composition_tarski f hK hG
  let hMul := mulLaws_of_A13_additive_rigidity_tarski f hK hComm hAssoc hDistrib
  exact axis_isRealClosed_of_three_geometric_cores_tarski f hG hMul.1 hMul.2

end TarskiField
#print axioms TarskiField.mulLaws_of_A13_additive_rigidity_tarski
#print axioms TarskiField.axis_isRealClosed_of_G_A13_tarski


/-!
GeoCoq l12_17, exactly the reflection-to-parallel kernel needed for the
direct two-reflection proof of midpoint-quadrilateral composition G.  The existing
centered_reflection_parallel_tarski handles a center off the source line;
when the center is on that line both images stay on the same line.
-/
namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

theorem reflection_parallel_including_collinear_center_tarski
    {M A B A' B' : Point}
    (hAB : A ≠ B)
    (hA : MulMidpoint M A A')
    (hB : MulMidpoint M B B') :
    Parallel A B A' B' := by
  by_cases hOff : ¬ Col A B M
  · exact centered_reflection_parallel_tarski hAB hOff hA hB
  · have hMon : Col A B M := Classical.byContradiction hOff
    have hCong : Cong A B A' B' :=
      mul_reflection_preserves_cong
        (mul_midpoint_reverse hA) (mul_midpoint_reverse hB)
    have hA'B' : A' ≠ B' := by
      intro heq
      exact hAB (cong_identity A B A'
        (by simpa only [heq] using hCong))
    have hA'on : Col A B A' := by
      by_cases hAM : A = M
      · have hCongAA' : Cong A A A A' := by
          simpa only [← hAM] using hA.2
        have hAA' : A = A' :=
          cong_identity A A' A (cong_symm hCongAA')
        simpa only [← hAA'] using (col_left A B)
      · have hline : ∀ X : Point, Col A B X ↔ Col A M X :=
          col_line_extensionality_tarski
            hAB hAM (col_left A B) hMon
        exact (hline A').mpr (Or.inl hA.1)
    have hB'on : Col A B B' := by
      by_cases hBM : B = M
      · have hCongBB' : Cong B B B B' := by
          simpa only [← hBM] using hB.2
        have hBB' : B = B' :=
          cong_identity B B' B (cong_symm hCongBB')
        simpa only [← hBB'] using (col_right A B)
      · have hline : ∀ X : Point, Col A B X ↔ Col B M X :=
          col_line_extensionality_tarski
            hAB hBM (col_right A B) hMon
        exact (hline B').mpr (Or.inl hB.1)
    exact ⟨hAB, hA'B', Or.inl
      (col_line_extensionality_tarski
        hAB hA'B' hA'on hB'on)⟩

end TarskiField

#print axioms TarskiField.reflection_parallel_including_collinear_center_tarski



/-!
## General midpoint composition G directly by two central reflections

Natural master §1. No angle congruence or classification of the input
quadrilaterals is needed. Two reflections preserve the direction of
every nondegenerate line. With distinct centers their composite has
no fixed point; consequently its displacement lines are all parallel.
-/
namespace TarskiField

variable {Point : Type u} [Plane Point]
open Plane

theorem midpoint_quadrilateral_composition_tarski
    (A B C D E F : Point)
    (hFirst : ∃ M : Point, MulMidpoint M A C ∧ MulMidpoint M B D)
    (hSecond : ∃ N : Point, MulMidpoint N C E ∧ MulMidpoint N D F) :
    ∃ K : Point, MulMidpoint K A F ∧ MulMidpoint K B E := by
  classical
  obtain ⟨M,hMAC,hMBD⟩ := hFirst
  obtain ⟨N,hNCE,hNDF⟩ := hSecond
  by_cases hMN : M = N
  · subst N
    have hAE := mul_reflection_involution hMAC hNCE
    have hBF := mul_reflection_involution hMBD hNDF
    subst E
    subst F
    obtain ⟨K,hK⟩ := midpoint_existence_tarski A B
    exact ⟨K,hK,mul_midpoint_reverse hK⟩
  let r (S X : Point) : Point :=
    Classical.choose (ExistsUnique.exists (mul_reflection_exists_unique S X))
  have hr (S X : Point) : MulMidpoint S X (r S X) :=
    Classical.choose_spec (ExistsUnique.exists (mul_reflection_exists_unique S X))
  have hrEq (S X Y : Point) (h : MulMidpoint S X Y) : r S X = Y :=
    mul_reflection_involution (mul_midpoint_reverse (hr S X)) h
  let T (X : Point) := r N (r M X)
  have hTA : T A = E := by
    change r N (r M A) = E
    rw [hrEq M A C hMAC,hrEq N C E hNCE]
  have hTB : T B = F := by
    change r N (r M B) = F
    rw [hrEq M B D hMBD,hrEq N D F hNDF]
  have hFixed (X : Point) : X ≠ T X := by
    intro h
    have hN : MulMidpoint N X (r M X) := by
      have h' := mul_midpoint_reverse (hr N (r M X))
      change MulMidpoint N (T X) (r M X) at h'
      rw [← h] at h'
      exact h'
    exact hMN (mul_midpoint_center_unique_tarski (hr M X) hN)
  have hCong (X Y : Point) : Cong X Y (T X) (T Y) :=
    cong_trans
      (mul_reflection_preserves_cong
        (mul_midpoint_reverse (hr M X)) (mul_midpoint_reverse (hr M Y)))
      (mul_reflection_preserves_cong
        (mul_midpoint_reverse (hr N (r M X)))
        (mul_midpoint_reverse (hr N (r M Y))))
  have hCol (X Y Z : Point) (h : Col X Y Z) :
      Col (T X) (T Y) (T Z) :=
    mul_reflection_preserves_col (hr N (r M X)) (hr N (r M Y))
      (hr N (r M Z)) (mul_reflection_preserves_col (hr M X) (hr M Y) (hr M Z) h)
  have hMid (P X Y : Point) (h : MulMidpoint P X Y) :
      MulMidpoint (T P) (T X) (T Y) :=
    mul_reflection_preserves_midpoint (hr N (r M X)) (hr N (r M P))
      (hr N (r M Y))
      (mul_reflection_preserves_midpoint (hr M X) (hr M P) (hr M Y) h)
  have hPar (X Y : Point) (h : X ≠ Y) : Parallel X Y (T X) (T Y) := by
    have h₁ := reflection_parallel_including_collinear_center_tarski
      h (hr M X) (hr M Y)
    have h₂ := reflection_parallel_including_collinear_center_tarski
      h₁.2.1 (hr N (r M X)) (hr N (r M Y))
    exact parallel_trans_of_playfair tarski_playfair h₁ h₂
  have hStable (X P : Point) (hP : Col X (T X) P) :
      Col X (T X) (T P) := by
    have hline := parallel_same_of_intersection
      (hPar X (T X) (hFixed X)) (col_right X (T X)) (col_left (T X) (T (T X)))
    exact (hline (T P)).mpr (hCol X (T X) P hP)
  have hMove (X Y : Point) : Parallel X (T X) Y (T Y) := by
    refine ⟨hFixed X,hFixed Y,?_⟩
    by_cases h : ∃ P : Point, Col X (T X) P ∧ Col Y (T Y) P
    · obtain ⟨P,hPX,hPY⟩ := h
      left
      have hx := col_line_extensionality_tarski (hFixed X) (hFixed P)
        hPX (hStable X P hPX)
      have hy := col_line_extensionality_tarski (hFixed Y) (hFixed P)
        hPY (hStable Y P hPY)
      intro Z
      exact (hx Z).trans (hy Z).symm
    · right
      intro P hP
      exact h ⟨P,hP⟩
  by_cases hAB : A = B
  · have hEF : E = F := hTA.symm.trans ((congrArg T hAB).trans hTB)
    obtain ⟨K,hK⟩ := midpoint_existence_tarski A E
    refine ⟨K, ?_, ?_⟩
    · rw [← hEF]
      exact hK
    · rw [← hAB]
      exact hK
  have hAE : A ≠ E := by simpa only [hTA] using hFixed A
  have hBF : B ≠ F := by simpa only [hTB] using hFixed B
  have hABEF : Parallel A B E F := by simpa only [hTA,hTB] using hPar A B hAB
  have hAEBF : Parallel A E B F := by simpa only [hTA,hTB] using hMove A B
  by_cases hFlat : Col A B F
  · have hline := parallel_same_of_intersection hABEF hFlat (col_right E F)
    have hE : Col A B E := (hline E).mpr (col_left E F)
    have hAEline := col_line_extensionality_tarski hAB hAE (col_left A B) hE
    have hBFline := col_line_extensionality_tarski hAB hBF (col_right A B) hFlat
    obtain ⟨X,hX⟩ := off_line_point_exists_tarski hAB
    let Y := T X
    have hXY : X ≠ Y := hFixed X
    have hAEXY : Parallel A E X Y := by simpa only [hTA] using hMove A X
    have hBFXY : Parallel B F X Y := by simpa only [hTB] using hMove B X
    have hXAE : ¬ Col A E X := fun h => hX ((hAEline X).mpr h)
    have hXBF : ¬ Col B F X := fun h => hX ((hBFline X).mpr h)
    have hYAE := parallel_off_line_disjoint hAEXY hXAE (col_right X Y)
    have hYBF := parallel_off_line_disjoint hBFXY hXBF (col_right X Y)
    have hAX : A ≠ X := by
      intro h
      exact hX (by simpa only [← h] using col_left A B)
    have hBX : B ≠ X := by
      intro h
      exact hX (by simpa only [← h] using col_right A B)
    have hAXEY : Parallel A X E Y := by simpa only [hTA] using hPar A X hAX
    have hBXFY : Parallel B X F Y := by simpa only [hTB] using hPar B X hBX
    have hCongAE := (strict_parallelogram_opposite_cong_tarski hYAE
      (parallel_reverse_right hAEXY) (parallel_reverse_right (parallel_symm hAXEY))).1
    have hCongBF := (strict_parallelogram_opposite_cong_tarski hYBF
      (parallel_reverse_right hBFXY) (parallel_reverse_right (parallel_symm hBXFY))).1
    have hCongAB : Cong A B F E := cong_reverse_right (by
      simpa only [hTA,hTB] using hCong A B)
    have hCongAEB : Cong A E F B :=
      cong_reverse_right (cong_trans hCongAE (cong_symm hCongBF))
    have hNontrivial : A ≠ F ∨ B ≠ E := by
      by_contra hn
      have hAF : A = F := by by_contra hh; exact hn (Or.inl hh)
      have hBE : B = E := by by_contra hh; exact hn (Or.inr hh)
      obtain ⟨P,hP⟩ := midpoint_existence_tarski A B
      have hTP := hMid P A B hP
      rw [hTA,hTB,← hAF,← hBE] at hTP
      exact hFixed P (mul_midpoint_center_unique_tarski
        (mul_midpoint_reverse hP) hTP)
    exact geoCoqFlatParallelogram_midpoint_tarski
      ⟨hFlat,hE,hCongAB,hCongAEB,hNontrivial⟩
  · exact parallelogram_diagonal_midpoint_exists_tarski hFlat
      (parallel_reverse_right hABEF)
      (parallel_reverse_right (parallel_symm hAEBF))

end TarskiField

#print axioms TarskiField.midpoint_quadrilateral_composition_tarski

/-! ## Final theorem: only the original Tarski plane and A13 -/
namespace TarskiField
variable {Point : Type u} [Plane Point]

/-- The geometrically interpreted axis is a real-closed field under A13.
    The local algebraic instances are proved from the primitive plane axioms;
    the statement makes no ambient coordinate field assumption. -/
theorem axis_isRealClosed_tarski
    [ContinuousPlane Point] (f : Frame Point) :
    let hG := midpoint_quadrilateral_composition_tarski (Point := Point)
    let hAdditive :=
      additive_laws_of_midpoint_quadrilateral_composition_tarski f
        (fun A B C D E F _ _ hQ₁ hQ₂ => hG A B C D E F hQ₁ hQ₂)
    let hK := hAdditive.1
    let hComm := hAdditive.2.1
    let hAssoc := hAdditive.2.2
    let hDistrib := leftDistrib_of_midpoint_and_composition_tarski f hK hG
    let hMul := mulLaws_of_A13_additive_rigidity_tarski f hK hComm hAssoc hDistrib
    letI : Field (AxisPoint f) :=
      axisFieldOfGeometricLaws_tarski f hAssoc hMul.1 hMul.2 hDistrib
    letI : LinearOrder (AxisPoint f) :=
      axisLinearOrderOfMidpointAddAssoc_tarski f hK hAssoc
    letI : IsStrictOrderedRing (AxisPoint f) :=
      axisStrictOrderedRingOfGeometricLaws_tarski f hK hAssoc
        hMul.1 hMul.2 hDistrib (positiveMulClosed_tarski f)
    IsRealClosed (AxisPoint f) := by
  exact axis_isRealClosed_of_G_A13_tarski f
    (midpoint_quadrilateral_composition_tarski (Point := Point))

end TarskiField
#print axioms TarskiField.axis_isRealClosed_tarski
