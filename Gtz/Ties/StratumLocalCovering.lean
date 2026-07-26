/-
# Local covering at the split-tetrahedron tie stratum

`Gtz.Ties.StratumFirstOrder` proves the Farkas identity at `splitSevenDesign` and names
the residual it does not close, `SplitSevenNeighbourhoodCovering`.
`Gtz.Ties.StratumSharpMaximum` attaches a constant to the certificate.  This file does
three further things: it computes the FLAT SPACE of the certificate exactly — nine named
directions, proved flat, proved independent, proved to span — it upgrades the sign
statement to an exact dichotomy, and it reduces the residual to one scalar polynomial
inequality per design.

## PROVED here (kernel-checked, zero `sorry`, zero new axiom)

* `parsevalMatrixVelocity` and `parsevalMatrix_ray_expansion` — the FULL matrix Parseval
  constraint's step-linear coefficient, and the exact cubic ray expansion that makes the
  word "velocity" a theorem.  `Gtz.parsevalTraceVelocity` is its trace
  (`parsevalTraceVelocity_eq_trace`), so the admissible directions of this file are a
  SUBSET of the ones `Gtz.Ties.StratumFirstOrder` works with: every theorem there
  applies here unchanged, and the flat space computed here is the true tangent-and-tie
  kernel, not a trace-only relaxation.
* `IsSplitSevenTraceTangent`, `IsSplitSevenTangent`, `IsSplitSevenFlat` — the two
  admissibility notions (mass-preserving with the TRACE of Parseval stationary; the
  stronger one with the full MATRIX stationary) and the flat directions (matrix-tangent
  with all twenty rainbow tie forms stationary).
* **THE RELATIVE-INTERIOR DICHOTOMY**, `rainbowSeven_supVelocity_eq_zero_iff`: along
  every TRACE-tangent direction the largest of the twenty tie-form velocities is `≥ 0`
  (`rainbowSeven_supVelocity_nonneg`), with equality EXACTLY when all twenty vanish.
  The hypothesis is deliberately the weak one — mass plus the trace, which is all the
  Farkas certificate consumes — and `rainbowSeven_supVelocity_eq_zero_iff_flat` is the
  matrix-tangent corollary phrased in `IsSplitSevenFlat`.
  The mechanism is the finite positive-combination argument and nothing else: twenty
  strictly positive multipliers summing a quantity to zero cannot have one summand
  negative unless another is positive, so `∀ T, v_T ≤ 0` forces `∀ T, v_T = 0`
  (`rainbowSeven_velocity_eq_zero_of_all_nonpos`).  That is the statement that `0` lies
  in the RELATIVE INTERIOR of the tangent-restricted tie-gradient hull, in the only form
  that needs no inradius: the support function of the hull is nonnegative and vanishes
  exactly on the hull's own annihilator.
* **THE FLAT SPACE, NINE EXPLICIT DIRECTIONS** — `stratumFlatDirectionAtom` and
  `stratumFlatDirectionWeight`, nine exactly rational admissible directions, each killing
  all twenty tie forms (`stratumFlatDirection_isFlat`), in three families of three:
  - `weightSplitWeightVelocity` — moving weight between the two copies of one split
    direction.  The atoms do not move at all, so Parseval is preserved because the two
    copies carry the SAME rank-one moment.
  - `bundleTotalAtomVelocity` / `bundleTotalWeightVelocity` — moving weight between one
    split bundle and the unsplit atom, with the atom compensation in closed form.
    Writing `delta_d` for the bundle weight increments (`∑_d delta_d = 0`) the
    compensation is `k_d = −2 delta_d v_d + (1/6) ∑_e delta_e v_e`, derived from the
    symmetric ansatz `k_d = A v_d + mu_d v_d` with `mu_d = −(4/3) delta_d` and
    `A = −(1/6) ∑_d delta_d v_d v_dᵀ`.  [DERIVED outside Lean; what is mechanized is
    that the resulting nine numbers are flat.]
  - `gaugeRotationAtomVelocity` — `dg_c = e_a × g_c`, the infinitesimal rotations.  These
    are flat for a structural reason: Parseval is preserved because `Omega + Omegaᵀ = 0`
    against `∑ t_c g_c g_cᵀ = I`, and every tie form is preserved because the three
    atoms of a rainbow triple sum to `−v_miss`, so the tie velocity collapses to
    `−⟨v_miss, Omega v_miss⟩ = 0`.
  `stratumFlatDirection_independent` reads six atom coordinates and three weight
  coordinates off them through an invertible `9 × 9` rational block, so the nine are
  linearly independent.
* **BUNDLE RIGIDITY**, `rainbowSeven_bundleRigid_of_velocity_zero` — the structural half
  of the matching upper bound, and it needs no admissibility at all.  A direction killing
  all twenty tie forms moves the two copies of a split direction TOGETHER: differencing
  two rainbow triples that agree except on which copy they take makes `dg_0 − dg_4`
  orthogonal to `v_1, v_2, v_3`, a basis, hence zero.  That kills nine of the twenty-one
  atom coordinates outright.
* **THE NINE SPAN**, `stratumFlat_eq_combination` — the matching upper bound, with the
  inverse readout `stratumFlatCoefficient` exhibited in closed form: nine explicit linear
  functionals of a flat direction that reproduce it.  `stratumFlat_coefficient_unique`
  says those coefficients are the only ones.  So the flat space has dimension EXACTLY
  nine and the nine directions are a BASIS of it.
* **RANK EXACTLY NINETEEN**, `stratumStackedJacobian_finrank_range` — the number the
  campaign measured, as a theorem rather than a reader's corollary.
  `stratumStackedJacobian` is the stacked Jacobian as an honest linear map (twenty tie
  velocities, the matrix Parseval velocity, the mass velocity), built on the linearity
  lemmas `parsevalMatrixVelocity_add` / `_smul` and `rainbowSevenVelocityFamily_add` /
  `_smul`.  `mem_ker_stratumStackedJacobian_iff` identifies its kernel with the flat
  space, `stratumFlatKernelBasis` turns the nine directions into a basis of that kernel
  (`stratumStackedJacobian_finrank_ker = 9`), the direction space is `28`-dimensional
  (`stratumDirectionSpace_finrank`), and rank–nullity finishes.
  The codomain is deliberately unreduced — the Parseval component is the whole `3 x 3`
  matrix, not its six independent entries, and nothing here says which `27` coordinates
  are independent.  That is free: rank is `dim(domain) − dim(ker)`, so padding the
  codomain cannot change it.

## Why the elimination is small, and which rows do the work

The `27 × 28` stacked Jacobian has rank `19`, so its rows span an `8`-dimensional space
of linear relations.  The constraint rows are independent among themselves
(`rank = 7` on `7` rows), so every one of those eight relations involves tie rows.  The
Farkas identity is the distinguished element of that eight-dimensional space, and reads
`∑_T lambda_T · grad tie_T = (trace Parseval gradient) − 3 · (mass gradient)`;  it is
`splitSevenDesign_farkasIdentity` together with `splitSevenDesign_leverage`.
The tie block alone has rank `13 = 4 + 3 + 3 + 3`, forced by a block decomposition in the
coordinates `y_{c,d} = ⟨v_d, dg_c⟩`, in which the tie Jacobian is `−2` times the incidence
matrix of "triple `T` contains atom `c` and misses direction `d`" — block diagonal over
the missed direction.  `rainbowSeven_bundleRigid_of_velocity_zero` is exactly the
differencing rows of that decomposition.

The spanning proof therefore never touches all twenty-seven rows.  Counting honestly at
the level of the PROOFS and not of the summary: `rainbowSeven_bundleRigid_of_velocity_zero`
instantiates the tie hypothesis at the thirteen indices
`0,1,2,4,8,9,10,12,13,14,16,17,18` to produce the nine rigidity equations, and
`stratumFlat_eq_combination` re-uses four of those same thirteen (`T_0, T_8, T_12, T_16`,
one per missed direction, which between them touch only the atoms `0,1,2,3`) alongside the
six Parseval entries and the mass.  So THIRTEEN tie rows are used and SEVEN —
`T_3, T_5, T_6, T_7, T_11, T_15, T_19` — are never touched at all.  The elimination that
actually reconstructs the direction is the twenty-row system (nine rigidity, four tie, six
Parseval, mass); the thirteen tie instantiations are what buys the nine rigidity rows.

## PROVED here — covering on the whole tie class through the split tetrahedron

`splitSevenClassDesign` puts the corank-one atom of each tetrahedron direction on the
atoms carrying it, at the class totals, for an ARBITRARY weight vector in the open
simplex.  `splitSevenClassDesign_isTie` and `splitSevenClassDesign_exists_dominatingTriple`
say the whole class — an `m − 1 = 6`-parameter section over the open weight simplex, not
one point — is covered.  The word THROUGH is a theorem and not a naming convention:
`splitSevenClassDesign_eq_splitSevenDesign` says the section evaluated at
`splitSevenDesign.weight` IS `splitSevenDesign`, because at the class totals
`(1/4, 1/4, 1/4, 1/4)` the Householder reflector has unit length and
`simplexTieAtom` reproduces `tetraAtom` on the nose
(`simplexTieAtom_uniformQuarter_eq_tetraAtom`).
`bundledCycle_exists_dominatingSubset` is the same statement for the graphic realization
at every rank, with the spanning tree named as the witness — which the upstream tie
theorem does not give.  The tie half is a packaging of `Gtz.splitClassDesign_isTie`; the
work was done upstream and is cited, not re-proved.

SCOPE OF THAT SECTION, precisely: `Gtz.splitClassDesign` is indexed by a map
`Fin m → Fin (k + 1)`, so it carries at most `k + 1 = 4` distinct atom directions.  The
diamond primitive `M(K4 − e)` has FIVE.  So no diamond class is a `splitClassDesign`, and
this section covers exactly the bundled-cycle half of the `(7,3)` equality locus and none
of the diamond half.

## PROVED here — the tube reduction, and the ONE named hypothesis

`rainbowSeven_dominates_of_tube_of_determinant`: at radius `1/16` around the split
tetrahedron, a rainbow triple DOMINATES as soon as its gap determinant is nonnegative.
Everything else Sylvester needs is proved from the radius: the entrywise deviation of a
rainbow gap is at most `99/256` (`rainbowSeven_gapEntry_dist_le`, a sum-of-absolute-
coefficients bound, linear in the radius), the tie gap is `3·I − v v^ᵀ` with diagonal
`2` and off-diagonal `±1`, and `413/256 > 355/256` closes the three two-by-two minors.
`Gtz.posSemidef_three_of_principalMinors` then gives positive semidefiniteness with no
strictness anywhere, which is what a boundary problem needs.

So `SplitSevenNeighbourhoodCovering` follows from ONE named hypothesis,
`SplitSevenTubeDeterminantWitness`: *every design in the tube has a rainbow triple whose
gap determinant is nonnegative* (`splitSevenNeighbourhoodCovering_of_determinantWitness`).
That is a single scalar polynomial sign per design, and it is the right shape because a
negative determinant already refutes THAT TRIPLE's domination — in every dimension, not
only in odd ones.  Only the direction `witness ⟹ covering` is proved.  The converse is
MEASURED, not proved: inside the tube the fifteen direction-repeating triples have
`lambda_min ≈ −0.99` throughout, so no non-rainbow triple can dominate there and the
witness is in fact equivalent to covering — but "no non-rainbow triple dominates in the
tube" is not a theorem here.  The reduction therefore changes the obligation's SHAPE
(three principal minors, per triple, become one polynomial sign) rather than its content.

The tube's WEIGHT condition is load-bearing and is not decoration.  The weights of
`splitSevenDesign` are `1/8` and `1/4`, so a weight radius of at most `1/16` pins
`t_min > 1/16` throughout the tube.  That matters because the slack constant of the tie
locus degenerates like `Theta(t_min)` as the weight simplex's boundary is approached
(MEASURED; constants in the ledger below), so a tube with no weight floor would have no
uniform constant to work with.

The remainder-shaped statement that pairs with the reduction is
`rainbowSeven_displacement_frozenForm`, and it is an IDENTITY, not an estimate: the tie
form of a rainbow triple at a nearby design, probed at its own missed direction, equals
the tie-form VELOCITY of the displacement plus an exact sum of squares.  There is no
remainder to bound — the quadratic term is present with the right sign.

What that identity does NOT say — and an earlier draft of this header said it, wrongly —
is that the sign of the linear term decides covering.  The frozen form is ONE probe,
`v_miss`; domination is an ALL-probe property.  A genuine Parseval design inside the tube
can have a rainbow triple whose linear term and whose frozen form are both POSITIVE while
its gap determinant is NEGATIVE, so that the triple does not dominate: MEASURED at
sup-norm distance `0.0481` from the split tetrahedron, with linear term `+2.1e-3`, frozen
form `+3.9e-3` and gap determinant `−3.2e-3` (re-verified at 80 digits, Parseval residual
`1.1e-81`).  This is why the reduction above is stated in the DETERMINANT and not in the
form.

The genuinely missing ingredient is a Hoffman/error-bound constant converting
`max_T ⟨grad tie_T, u⟩` into `dist(u, flat space)`, which Mathlib has no machinery for and
which at this size is a facet enumeration of a `12`-dimensional hull in a `21`-dimensional
tangent.  It is also not sufficient by itself: when the class-tangent excursion is left
free inside the tube and only the transverse distance is held fixed, the realized ratio
falls well below the pure-transverse one (MEASURED, ledger below), so a proof of the shape
"error bound plus remainder" needs a uniform bound on the bilinear class-tangent by
transverse cross term as well.

## MEASURED (numerics and exact-rational elimination; NOT kernel-checked here)

Every number below was produced by exact rational linear algebra unless marked otherwise,
and every threshold-crossing or refuting finding was re-verified at 80 digits.

* Ranks at `splitSevenDesign`, exact over the rationals: constraint block `7`, tie block
  `13`, stacked `19`, kernel `9`.  The reduced twenty-row system has the same rank and the
  same kernel as the full twenty-seven.  The nine shipped directions are a rational basis
  of that kernel.
* The dimension count is not special to this point: `dim(flat space) = m + 2` was
  reproduced at `(2,2,2,1)` with uneven splits and skewed class totals, at `(3,2,1,1)`,
  and at `(4,1,1,1)` — nine in each `(7,3)` case, eight at `(6,3)` — and a strictly
  positive Farkas certificate over the ACTIVE triples exists at every point tested.
* THREE DIFFERENT `7`s AND `8`s, which prose has repeatedly conflated.  The left kernel of
  the `20 × 28` tie Jacobian, `{lambda : ∑_T lambda_T · grad tie_T = 0}`, has dimension
  `7`.  The certificate space
  `{lambda : ∑_T lambda_T · grad tie_T ∈ rowspan(constraint Jacobian)}` — the linear space
  a Farkas certificate can actually live in — has dimension `8`.  Its mass-one affine
  slice has dimension `7`.  The shipped `Gtz.rainbowSevenMultiplier` lies in the SECOND
  and not in the first, which is exactly why the Farkas identity has a nonzero right-hand
  side.  All three are exact.
* The inradius of the tangent-restricted tie-gradient hull is `c = 0.469383091992` (polar
  vertex enumeration over all `C(20,12) = 125970` candidate facets).  Since
  `adj(3I − v vᵀ) = 3 v vᵀ`, a pure-transverse curve must realize determinant slope
  `3c = 1.40815`; measured `1.40848 / 1.41147 / 1.41475` at steps `1e-3 / 1e-2 / 2e-2`.
  With the class-tangent excursion left free and only the transverse distance fixed, the
  realized ratio drops to `0.563 / 0.623 / 0.610` at distance `1e-2 / 3e-2 / 1e-1` — a
  factor of about `2.3`, the cross term named in the tube section above.
* Slack degeneration toward the weight-simplex boundary: `c = Theta(t_min)`, with
  `c / t_min → 1.14` for intra-class dust and `1.06` for class-total dust, stable across
  `t_min = 1e-2 … 1e-5`; `c / sqrt(t_min) → 0`.  This is what the tube's weight radius
  buys.
* `SplitSevenTubeDeterminantWitness` at radius `1/16` survived roughly `2.6e5` targeted
  probes (epigraph minimax over the Parseval manifold at several radii, boundary-hugging
  draws, random tangent rays, mixed class-tangent curves, and second order along the nine
  flat directions).  Every float-negative was roundoff and turned positive at 80 digits.
  It is NOT strictly feasible: equality holds at `splitSevenDesign` itself, which any
  future proof must handle.  Its two-by-two arithmetic closes up to radius `0.080123`, so
  `1/16` carries about `1.28x` of headroom.

## HONEST SCOPE

Everything is about ONE point of ONE tie stratum at `(7,3)`, except the class-covering
section, which is about the whole class through it, and the tube reduction, which is
about a `1/16` neighbourhood of it.  Nothing here closes
`SplitSevenNeighbourhoodCovering`, and nothing here bears on the other tie classes at
`(7,3)`, on the diamond `M(K4 − e)` primitive (`Gtz.Ties.DiamondTie`,
`Gtz.Design.DiamondPrimitive`), on rank `≥ 4`, or on `GtzWeighted 7 3`.  The closed form
behind `bundleTotalAtomVelocity` was derived outside Lean; only its output is used, and
what is mechanized is that the resulting numbers are flat.
-/
import Mathlib
import Gtz.Ties.StratumSharpMaximum
import Gtz.Ties.SplitClassTieFamily
import Gtz.Design.EqualityLocus
import Gtz.Reduction.CertificateBall
import Gtz.Reduction.PrincipalMinorsThree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The full matrix Parseval velocity -/

/-- The `step`-linear coefficient of the FULL matrix Parseval constraint
`∑_c t_c g_c g_cᵀ = I`, as the design moves along
`(weight + step * weightVelocity, atom + step • atomVelocity)`. -/
noncomputable def parsevalMatrixVelocity (design : WeightedDesign m k)
    (atomVelocity : Fin m → Fin k → ℝ) (weightVelocity : Fin m → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  ∑ atomIndex, (weightVelocity atomIndex • atomMatrix (design.atom atomIndex)
    + design.weight atomIndex •
        (Matrix.vecMulVec (atomVelocity atomIndex) (design.atom atomIndex)
          + Matrix.vecMulVec (design.atom atomIndex) (atomVelocity atomIndex)))

/-- The Parseval velocity entry by entry. -/
theorem parsevalMatrixVelocity_apply (design : WeightedDesign m k)
    (atomVelocity : Fin m → Fin k → ℝ) (weightVelocity : Fin m → ℝ)
    (rowIndex colIndex : Fin k) :
    parsevalMatrixVelocity design atomVelocity weightVelocity rowIndex colIndex
      = ∑ atomIndex, (weightVelocity atomIndex
            * (design.atom atomIndex rowIndex * design.atom atomIndex colIndex)
          + design.weight atomIndex
            * (atomVelocity atomIndex rowIndex * design.atom atomIndex colIndex
              + design.atom atomIndex rowIndex * atomVelocity atomIndex colIndex)) := by
  simp only [parsevalMatrixVelocity, Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply,
    atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]

/-- **The shipped trace velocity is the trace of the matrix velocity.**  So the
admissible directions of this file refine the ones `Gtz.Ties.StratumFirstOrder` works
with, and every theorem there applies to them unchanged. -/
theorem parsevalTraceVelocity_eq_trace (design : WeightedDesign m k)
    (atomVelocity : Fin m → Fin k → ℝ) (weightVelocity : Fin m → ℝ) :
    parsevalTraceVelocity design atomVelocity weightVelocity
      = (parsevalMatrixVelocity design atomVelocity weightVelocity).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, parsevalMatrixVelocity_apply,
    parsevalTraceVelocity]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  have hterm : ∀ coord : Fin k,
      weightVelocity atomIndex * (design.atom atomIndex coord * design.atom atomIndex coord)
          + design.weight atomIndex * (atomVelocity atomIndex coord * design.atom atomIndex coord
            + design.atom atomIndex coord * atomVelocity atomIndex coord)
        = weightVelocity atomIndex * design.atom atomIndex coord ^ 2
          + 2 * (design.weight atomIndex
            * (design.atom atomIndex coord * atomVelocity atomIndex coord)) := by
    intro coord; ring
  rw [Finset.sum_congr rfl (fun coord _ => hterm coord), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, leverageOf, dotProduct]

/-- **The Parseval matrix along a ray is an exact cubic in the step**, with constant term
the identity and linear coefficient `parsevalMatrixVelocity`.  No derivative is taken:
this is a polynomial identity, so calling the coefficient a velocity is a theorem. -/
theorem parsevalMatrix_ray_expansion (design : WeightedDesign m k)
    (atomVelocity : Fin m → Fin k → ℝ) (weightVelocity : Fin m → ℝ) (step : ℝ) :
    (∑ atomIndex, (design.weight atomIndex + step * weightVelocity atomIndex)
        • atomMatrix (design.atom atomIndex + step • atomVelocity atomIndex))
      = 1 + step • parsevalMatrixVelocity design atomVelocity weightVelocity
        + step ^ 2 • (∑ atomIndex,
            (weightVelocity atomIndex •
                (Matrix.vecMulVec (atomVelocity atomIndex) (design.atom atomIndex)
                  + Matrix.vecMulVec (design.atom atomIndex) (atomVelocity atomIndex))
              + design.weight atomIndex • atomMatrix (atomVelocity atomIndex)))
        + step ^ 3 • (∑ atomIndex,
            weightVelocity atomIndex • atomMatrix (atomVelocity atomIndex)) := by
  ext rowIndex colIndex
  simp only [Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
    parsevalMatrixVelocity_apply, Finset.mul_sum]
  rw [← design.isParseval]
  simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
    smul_eq_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun atomIndex _ => by ring

/-! ## Admissible and flat directions at the split tetrahedron -/

/-- **A trace-admissible direction**: mass-preserving, with the TRACE of the Parseval
constraint stationary.  This is the weakest hypothesis the Farkas certificate consumes,
and every dichotomy statement below is stated on it. -/
def IsSplitSevenTraceTangent (atomVelocity : Fin 7 → Fin 3 → ℝ)
    (weightVelocity : Fin 7 → ℝ) : Prop :=
  (∑ atomIndex, weightVelocity atomIndex = 0)
    ∧ parsevalTraceVelocity splitSevenDesign atomVelocity weightVelocity = 0

/-- **An admissible tangent direction**: mass-preserving and Parseval-preserving to
first order, the FULL matrix and not only its trace.  Every curve of designs through
`splitSevenDesign` has its velocity here. -/
def IsSplitSevenTangent (atomVelocity : Fin 7 → Fin 3 → ℝ)
    (weightVelocity : Fin 7 → ℝ) : Prop :=
  (∑ atomIndex, weightVelocity atomIndex = 0)
    ∧ parsevalMatrixVelocity splitSevenDesign atomVelocity weightVelocity = 0

/-- **A flat direction**: admissible, with all twenty rainbow tie forms stationary.
This is the critical cone the first-order certificate is silent on. -/
def IsSplitSevenFlat (atomVelocity : Fin 7 → Fin 3 → ℝ)
    (weightVelocity : Fin 7 → ℝ) : Prop :=
  IsSplitSevenTangent atomVelocity weightVelocity
    ∧ ∀ tripleIndex : Fin 20, rainbowSevenVelocityFamily atomVelocity tripleIndex = 0

theorem IsSplitSevenTangent.parsevalTraceVelocity_eq_zero
    {atomVelocity : Fin 7 → Fin 3 → ℝ} {weightVelocity : Fin 7 → ℝ}
    (htangent : IsSplitSevenTangent atomVelocity weightVelocity) :
    parsevalTraceVelocity splitSevenDesign atomVelocity weightVelocity = 0 := by
  rw [parsevalTraceVelocity_eq_trace, htangent.2, Matrix.trace_zero]

/-- Matrix-tangency is strictly stronger than trace-tangency, so every statement proved
on the weak hypothesis specialises. -/
theorem IsSplitSevenTangent.isTraceTangent
    {atomVelocity : Fin 7 → Fin 3 → ℝ} {weightVelocity : Fin 7 → ℝ}
    (htangent : IsSplitSevenTangent atomVelocity weightVelocity) :
    IsSplitSevenTraceTangent atomVelocity weightVelocity :=
  ⟨htangent.1, htangent.parsevalTraceVelocity_eq_zero⟩

/-- The tie-form velocity of a rainbow triple, in atom coordinates: each of the three
atoms pairs to `−1` with the missed direction, so the whole form collapses. -/
theorem rainbowSevenVelocityFamily_eq (atomVelocity : Fin 7 → Fin 3 → ℝ)
    (tripleIndex : Fin 20) :
    rainbowSevenVelocityFamily atomVelocity tripleIndex
      = -2 * (atomVelocity (rainbowSevenFirst tripleIndex)
              ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex)
            + atomVelocity (rainbowSevenSecond tripleIndex)
              ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex)
            + atomVelocity (rainbowSevenThird tripleIndex)
              ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex)) := by
  rw [rainbowSevenVelocityFamily, gapFormVelocity]
  have hpairing : ∀ atomIndex ∈ rainbowSevenTriple tripleIndex,
      2 * ((splitSevenDesign.atom atomIndex
              ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex))
          * (atomVelocity atomIndex ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex)))
        = -2 * (atomVelocity atomIndex
            ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex)) := by
    intro atomIndex hmem
    rw [splitSevenDesign_atom,
      tetraAtom_dot_of_ne (rainbowSevenTriple_direction_ne_missed hmem)]
    ring
  rw [Finset.mul_sum, Finset.sum_congr rfl hpairing, ← Finset.mul_sum,
    sum_rainbowSevenTriple]

/-! ## The relative-interior dichotomy -/

/-- The certificate fires on every trace-admissible direction. -/
theorem rainbowSeven_multiplierSum_velocity_eq_zero
    {atomVelocity : Fin 7 → Fin 3 → ℝ} {weightVelocity : Fin 7 → ℝ}
    (htangent : IsSplitSevenTraceTangent atomVelocity weightVelocity) :
    ∑ tripleIndex : Fin 20,
        rainbowSevenMultiplier tripleIndex * rainbowSevenVelocityFamily atomVelocity tripleIndex
      = 0 :=
  splitSevenDesign_farkasIdentity_zero atomVelocity weightVelocity htangent.1 htangent.2

/-- **THE RELATIVE-INTERIOR LEMMA.**  Along a trace-admissible direction, if no rainbow
tie form rises then none moves at all.

Twenty STRICTLY POSITIVE multipliers sum the twenty tie-form velocities to zero.  A sum
of nonnegative terms that vanishes has every term zero, and no multiplier is zero, so
every velocity is zero.  This is the finite-dimensional statement that `0` lies in the
relative interior of the tangent-restricted tie-gradient hull: the hull's support
function vanishes exactly on the hull's annihilator and nowhere else. -/
theorem rainbowSeven_velocity_eq_zero_of_all_nonpos
    {atomVelocity : Fin 7 → Fin 3 → ℝ} {weightVelocity : Fin 7 → ℝ}
    (htangent : IsSplitSevenTraceTangent atomVelocity weightVelocity)
    (hnonpos : ∀ tripleIndex : Fin 20, rainbowSevenVelocityFamily atomVelocity tripleIndex ≤ 0) :
    ∀ tripleIndex : Fin 20, rainbowSevenVelocityFamily atomVelocity tripleIndex = 0 := by
  have hnonneg : ∀ tripleIndex ∈ (Finset.univ : Finset (Fin 20)),
      0 ≤ rainbowSevenMultiplier tripleIndex
        * (-rainbowSevenVelocityFamily atomVelocity tripleIndex) := fun tripleIndex _ =>
    mul_nonneg (rainbowSevenMultiplier_pos tripleIndex).le (neg_nonneg.mpr (hnonpos tripleIndex))
  have hzero : ∑ tripleIndex : Fin 20, rainbowSevenMultiplier tripleIndex
      * (-rainbowSevenVelocityFamily atomVelocity tripleIndex) = 0 := by
    have hneg : ∑ tripleIndex : Fin 20, rainbowSevenMultiplier tripleIndex
        * (-rainbowSevenVelocityFamily atomVelocity tripleIndex)
        = -∑ tripleIndex : Fin 20, rainbowSevenMultiplier tripleIndex
            * rainbowSevenVelocityFamily atomVelocity tripleIndex := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun tripleIndex _ => by ring
    rw [hneg, rainbowSeven_multiplierSum_velocity_eq_zero htangent, neg_zero]
  intro tripleIndex
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero tripleIndex
    (Finset.mem_univ tripleIndex)
  rcases mul_eq_zero.mp hterm with hmul | hvel
  · exact absurd hmul (ne_of_gt (rainbowSevenMultiplier_pos tripleIndex))
  · linarith [neg_eq_zero.mp hvel]

/-- The largest of the twenty tie-form velocities is nonnegative along every
trace-admissible direction. -/
theorem rainbowSeven_supVelocity_nonneg
    {atomVelocity : Fin 7 → Fin 3 → ℝ} {weightVelocity : Fin 7 → ℝ}
    (htangent : IsSplitSevenTraceTangent atomVelocity weightVelocity) :
    0 ≤ (Finset.univ : Finset (Fin 20)).sup' ⟨0, Finset.mem_univ 0⟩
      (rainbowSevenVelocityFamily atomVelocity) := by
  obtain ⟨tripleIndex, hnonneg⟩ := rainbowSeven_exists_nonnegative_velocity atomVelocity
    weightVelocity htangent.1 htangent.2
  exact hnonneg.trans (Finset.le_sup' (rainbowSevenVelocityFamily atomVelocity)
    (Finset.mem_univ tripleIndex))

/-- **THE DICHOTOMY.**  Along every trace-admissible direction the largest tie-form
velocity is nonnegative, and it is zero EXACTLY when all twenty are stationary.  Off that
cone some rainbow tie form strictly rises. -/
theorem rainbowSeven_supVelocity_eq_zero_iff
    {atomVelocity : Fin 7 → Fin 3 → ℝ} {weightVelocity : Fin 7 → ℝ}
    (htangent : IsSplitSevenTraceTangent atomVelocity weightVelocity) :
    (Finset.univ : Finset (Fin 20)).sup' ⟨0, Finset.mem_univ 0⟩
        (rainbowSevenVelocityFamily atomVelocity) = 0
      ↔ ∀ tripleIndex : Fin 20, rainbowSevenVelocityFamily atomVelocity tripleIndex = 0 := by
  constructor
  · intro hsup
    refine rainbowSeven_velocity_eq_zero_of_all_nonpos htangent fun tripleIndex => ?_
    rw [← hsup]
    exact Finset.le_sup' (rainbowSevenVelocityFamily atomVelocity) (Finset.mem_univ tripleIndex)
  · intro hstationary
    refine le_antisymm (Finset.sup'_le _ _ fun tripleIndex _ => (hstationary tripleIndex).le)
      (rainbowSeven_supVelocity_nonneg htangent)

/-- **THE DICHOTOMY, IN THE FLAT-SPACE VOCABULARY.**  For a matrix-tangent direction the
vanishing of the largest tie-form velocity is exactly flatness. -/
theorem rainbowSeven_supVelocity_eq_zero_iff_flat
    {atomVelocity : Fin 7 → Fin 3 → ℝ} {weightVelocity : Fin 7 → ℝ}
    (htangent : IsSplitSevenTangent atomVelocity weightVelocity) :
    (Finset.univ : Finset (Fin 20)).sup' ⟨0, Finset.mem_univ 0⟩
        (rainbowSevenVelocityFamily atomVelocity) = 0
      ↔ IsSplitSevenFlat atomVelocity weightVelocity := by
  rw [rainbowSeven_supVelocity_eq_zero_iff htangent.isTraceTangent]
  exact ⟨fun hstationary => ⟨htangent, hstationary⟩, fun hflat => hflat.2⟩

/-- **THE STRICT DICHOTOMY.**  Off the stationary cone some rainbow tie form rises
strictly. -/
theorem rainbowSeven_exists_strictly_positive_velocity_of_not_stationary
    {atomVelocity : Fin 7 → Fin 3 → ℝ} {weightVelocity : Fin 7 → ℝ}
    (htangent : IsSplitSevenTraceTangent atomVelocity weightVelocity)
    (hmoves : ¬ ∀ tripleIndex : Fin 20,
      rainbowSevenVelocityFamily atomVelocity tripleIndex = 0) :
    ∃ tripleIndex : Fin 20, 0 < rainbowSevenVelocityFamily atomVelocity tripleIndex := by
  by_contra hnone
  push Not at hnone
  exact hmoves (rainbowSeven_velocity_eq_zero_of_all_nonpos htangent hnone)

/-- The strict dichotomy in the flat-space vocabulary. -/
theorem rainbowSeven_exists_strictly_positive_velocity_of_not_flat
    {atomVelocity : Fin 7 → Fin 3 → ℝ} {weightVelocity : Fin 7 → ℝ}
    (htangent : IsSplitSevenTangent atomVelocity weightVelocity)
    (hnotflat : ¬ IsSplitSevenFlat atomVelocity weightVelocity) :
    ∃ tripleIndex : Fin 20, 0 < rainbowSevenVelocityFamily atomVelocity tripleIndex :=
  rainbowSeven_exists_strictly_positive_velocity_of_not_stationary htangent.isTraceTangent
    fun hstationary => hnotflat ⟨htangent, hstationary⟩

/-! ## The flat space: nine explicit directions

Three families of three.  The atoms of the split tetrahedron are `g_c = v_{d(c)}` with
`d = (0,1,2,3,0,1,2)`, so direction `3` carries the single atom `3` and each of `0,1,2`
carries two.  Every direction below is written with integer entries; the scale is
irrelevant to flatness and is chosen to clear denominators. -/

/-- **Weight split `j`**: move weight from atom `j` to its copy `j + 4`.  The atoms do
not move at all.  Parseval survives because the two copies carry the SAME rank-one
moment, so the moved weight cancels; the tie forms survive because they see only the
atom velocity, which is zero. -/
def weightSplitWeightVelocity : Fin 3 → Fin 7 → ℝ :=
  ![![1, 0, 0, 0, -1, 0, 0],
    ![0, 1, 0, 0, 0, -1, 0],
    ![0, 0, 1, 0, 0, 0, -1]]

/-- **Bundle total `j`**: move weight between split bundle `j` and the unsplit atom `3`,
with the atom compensation in closed form.  With `delta` the bundle weight increments
(`delta_j = +1`, `delta_3 = −1`, the rest zero) the compensation of bundle `d` is
`k_d = −2 delta_d v_d + (1/6) ∑_e delta_e v_e`, and the whole direction is scaled by `6`
to clear the denominator.  [The closed form is DERIVED outside Lean from the symmetric
ansatz; what is mechanized is that the nine numbers below are flat.] -/
def bundleTotalAtomVelocity : Fin 3 → Fin 7 → Fin 3 → ℝ :=
  ![![![-10, -10, -12], ![2, 2, 0], ![2, 2, 0], ![-10, -10, 12], ![-10, -10, -12],
      ![2, 2, 0], ![2, 2, 0]],
    ![![2, 0, -2], ![-10, 12, 10], ![2, 0, -2], ![-10, -12, 10], ![2, 0, -2],
      ![-10, 12, 10], ![2, 0, -2]],
    ![![0, 2, -2], ![0, 2, -2], ![12, -10, 10], ![-12, -10, 10], ![0, 2, -2],
      ![0, 2, -2], ![12, -10, 10]]]

/-- The weight part of `bundleTotalAtomVelocity`: `+3` on each of the two copies of
bundle `j`, `−6` on the unsplit atom.  Total zero, and the bundle totals move by `+6`
and `−6`. -/
def bundleTotalWeightVelocity : Fin 3 → Fin 7 → ℝ :=
  ![![3, 0, 0, -6, 3, 0, 0],
    ![0, 3, 0, -6, 0, 3, 0],
    ![0, 0, 3, -6, 0, 0, 3]]

/-- **Gauge rotation about axis `a`**: `dg_c = e_a × g_c`, the infinitesimal rotations of
the whole configuration.  These are flat for a structural reason.  Parseval survives
because the generator is antisymmetric and `∑_c t_c g_c g_cᵀ = I`, so the velocity is
`Omega + Omegaᵀ = 0`.  Every tie form survives because the three atoms of a rainbow
triple sum to `−v_miss`, so the tie velocity collapses to `−⟨v_miss, Omega v_miss⟩ = 0`.
The weight part is zero. -/
def gaugeRotationAtomVelocity : Fin 3 → Fin 7 → Fin 3 → ℝ :=
  ![![![0, -1, 1], ![0, 1, -1], ![0, 1, 1], ![0, -1, -1], ![0, -1, 1], ![0, 1, -1],
      ![0, 1, 1]],
    ![![1, 0, -1], ![-1, 0, -1], ![-1, 0, 1], ![1, 0, 1], ![1, 0, -1], ![-1, 0, -1],
      ![-1, 0, 1]],
    ![![-1, 1, 0], ![1, 1, 0], ![-1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, 0],
      ![-1, -1, 0]]]

/-- Nine-term expansion, so the readout below reads coordinates off numeral indices. -/
private theorem sum_over_nine (summand : Fin 9 → ℝ) :
    ∑ index, summand index
      = summand 0 + summand 1 + summand 2 + summand 3 + summand 4 + summand 5
        + summand 6 + summand 7 + summand 8 := by
  simp [Fin.sum_univ_succ]
  ring

/-- The atom parts of the nine flat directions: three weight splits (which do not move
the atoms), three bundle totals, three gauge rotations. -/
def stratumFlatDirectionAtom : Fin 9 → Fin 7 → Fin 3 → ℝ :=
  ![0, 0, 0,
    bundleTotalAtomVelocity 0, bundleTotalAtomVelocity 1, bundleTotalAtomVelocity 2,
    gaugeRotationAtomVelocity 0, gaugeRotationAtomVelocity 1, gaugeRotationAtomVelocity 2]

/-- The weight parts of the nine flat directions. -/
def stratumFlatDirectionWeight : Fin 9 → Fin 7 → ℝ :=
  ![weightSplitWeightVelocity 0, weightSplitWeightVelocity 1, weightSplitWeightVelocity 2,
    bundleTotalWeightVelocity 0, bundleTotalWeightVelocity 1, bundleTotalWeightVelocity 2,
    0, 0, 0]

/-- Each of the nine directions preserves the total weight. -/
theorem stratumFlatDirection_mass_zero (directionIndex : Fin 9) :
    ∑ atomIndex, stratumFlatDirectionWeight directionIndex atomIndex = 0 := by
  fin_cases directionIndex <;>
    simp [Fin.sum_univ_succ, stratumFlatDirectionWeight, weightSplitWeightVelocity,
      bundleTotalWeightVelocity] <;> norm_num

/-- Each of the nine directions annihilates the FULL matrix Parseval constraint. -/
theorem stratumFlatDirection_parsevalMatrixVelocity_zero (directionIndex : Fin 9) :
    parsevalMatrixVelocity splitSevenDesign (stratumFlatDirectionAtom directionIndex)
      (stratumFlatDirectionWeight directionIndex) = 0 := by
  ext rowIndex colIndex
  rw [parsevalMatrixVelocity_apply]
  fin_cases directionIndex <;> fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Fin.sum_univ_succ, stratumFlatDirectionAtom, stratumFlatDirectionWeight,
      weightSplitWeightVelocity, bundleTotalAtomVelocity, bundleTotalWeightVelocity,
      gaugeRotationAtomVelocity, splitSevenDesign, splitSevenAtom, splitSevenDirection,
      tetraAtom] <;> norm_num

/-- Each of the nine directions leaves all twenty rainbow tie forms stationary. -/
theorem stratumFlatDirection_velocity_zero (directionIndex : Fin 9)
    (tripleIndex : Fin 20) :
    rainbowSevenVelocityFamily (stratumFlatDirectionAtom directionIndex) tripleIndex = 0 := by
  rw [rainbowSevenVelocityFamily_eq]
  fin_cases directionIndex <;> fin_cases tripleIndex <;>
    simp [dotProduct, Fin.sum_univ_three, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity, rainbowSevenFirst, rainbowSevenSecond, rainbowSevenThird,
      rainbowSevenMissedDirection, tetraAtom] <;> norm_num

/-- **THE NINE FLAT DIRECTIONS.**  Every one of them is an admissible tangent direction
at the split tetrahedron on which all twenty rainbow tie forms are stationary. -/
theorem stratumFlatDirection_isFlat (directionIndex : Fin 9) :
    IsSplitSevenFlat (stratumFlatDirectionAtom directionIndex)
      (stratumFlatDirectionWeight directionIndex) :=
  ⟨⟨stratumFlatDirection_mass_zero directionIndex,
      stratumFlatDirection_parsevalMatrixVelocity_zero directionIndex⟩,
    stratumFlatDirection_velocity_zero directionIndex⟩

/-- **THE NINE ARE LINEARLY INDEPENDENT.**  Six atom coordinates and three weight
coordinates read them off through an invertible `9 x 9` rational block, so the flat space
has dimension at least nine.  [The matching upper bound is `stratumFlat_eq_combination`
below, so the dimension is exactly nine.] -/
theorem stratumFlatDirection_independent (coefficient : Fin 9 → ℝ)
    (hatom : ∀ (atomIndex : Fin 7) (coord : Fin 3),
        ∑ directionIndex, coefficient directionIndex
          * stratumFlatDirectionAtom directionIndex atomIndex coord = 0)
    (hweight : ∀ atomIndex : Fin 7,
        ∑ directionIndex, coefficient directionIndex
          * stratumFlatDirectionWeight directionIndex atomIndex = 0) :
    ∀ directionIndex : Fin 9, coefficient directionIndex = 0 := by
  have hzeroZero := hatom 0 0
  have hzeroOne := hatom 0 1
  have hzeroTwo := hatom 0 2
  have honeZero := hatom 1 0
  have honeOne := hatom 1 1
  have htwoZero := hatom 2 0
  have hweightZero := hweight 0
  have hweightOne := hweight 1
  have hweightTwo := hweight 2
  rw [sum_over_nine] at hzeroZero hzeroOne hzeroTwo honeZero honeOne htwoZero
  rw [sum_over_nine] at hweightZero hweightOne hweightTwo
  simp [stratumFlatDirectionAtom, bundleTotalAtomVelocity, gaugeRotationAtomVelocity]
    at hzeroZero hzeroOne hzeroTwo honeZero honeOne htwoZero
  simp [stratumFlatDirectionWeight, weightSplitWeightVelocity, bundleTotalWeightVelocity]
    at hweightZero hweightOne hweightTwo
  have hsplitZero : coefficient 0 = 0 := by linarith
  have hsplitOne : coefficient 1 = 0 := by linarith
  have hsplitTwo : coefficient 2 = 0 := by linarith
  have hbundleZero : coefficient 3 = 0 := by linarith
  have hbundleOne : coefficient 4 = 0 := by linarith
  have hbundleTwo : coefficient 5 = 0 := by linarith
  have hgaugeZero : coefficient 6 = 0 := by linarith
  have hgaugeOne : coefficient 7 = 0 := by linarith
  have hgaugeTwo : coefficient 8 = 0 := by linarith
  intro directionIndex
  fin_cases directionIndex <;> assumption

/-- **BUNDLE RIGIDITY.**  A direction that leaves all twenty rainbow tie forms stationary
moves the two copies of a split tetrahedron direction TOGETHER.  No admissibility is
needed: the twenty tie equations alone force it.

The mechanism is a difference of two rainbow triples that agree except on which copy they
take.  For the pair `(0,4)` the triples `T_0 = (0,1,2)` and `T_4 = (4,1,2)` (missing
direction `3`), `T_12 = (0,2,3)` and `T_14 = (4,2,3)` (missing `1`), and `T_16 = (0,1,3)`
and `T_18 = (4,1,3)` (missing `2`) give three differences, so the displacement
`dg_0 − dg_4` is orthogonal to `v_1, v_2, v_3` — a basis — hence zero.  Nine of the
twenty-one atom coordinates are killed outright, which is the structural half of the
upper bound `dim ≤ 9`. -/
theorem rainbowSeven_bundleRigid_of_velocity_zero {atomVelocity : Fin 7 → Fin 3 → ℝ}
    (hstationary : ∀ tripleIndex : Fin 20,
      rainbowSevenVelocityFamily atomVelocity tripleIndex = 0) :
    atomVelocity 0 = atomVelocity 4 ∧ atomVelocity 1 = atomVelocity 5
      ∧ atomVelocity 2 = atomVelocity 6 := by
  have hpairing : ∀ tripleIndex : Fin 20,
      atomVelocity (rainbowSevenFirst tripleIndex)
          ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex)
        + atomVelocity (rainbowSevenSecond tripleIndex)
          ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex)
        + atomVelocity (rainbowSevenThird tripleIndex)
          ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex) = 0 := by
    intro tripleIndex
    have hvanishes := hstationary tripleIndex
    rw [rainbowSevenVelocityFamily_eq] at hvanishes
    linarith
  have hzero := hpairing 0
  have hone := hpairing 1
  have htwo := hpairing 2
  have hfour := hpairing 4
  have height := hpairing 8
  have hnine := hpairing 9
  have hten := hpairing 10
  have htwelve := hpairing 12
  have hthirteen := hpairing 13
  have hfourteen := hpairing 14
  have hsixteen := hpairing 16
  have hseventeen := hpairing 17
  have heighteen := hpairing 18
  simp [rainbowSevenFirst, rainbowSevenSecond, rainbowSevenThird,
    rainbowSevenMissedDirection, dotProduct, Fin.sum_univ_three,
    tetraAtom] at hzero hone htwo hfour height
  simp [rainbowSevenFirst, rainbowSevenSecond, rainbowSevenThird,
    rainbowSevenMissedDirection, dotProduct, Fin.sum_univ_three,
    tetraAtom] at hnine hten htwelve hthirteen
  simp [rainbowSevenFirst, rainbowSevenSecond, rainbowSevenThird,
    rainbowSevenMissedDirection, dotProduct, Fin.sum_univ_three,
    tetraAtom] at hfourteen hsixteen hseventeen heighteen
  have hfirstZero : atomVelocity 0 0 = atomVelocity 4 0 := by linarith
  have hfirstOne : atomVelocity 0 1 = atomVelocity 4 1 := by linarith
  have hfirstTwo : atomVelocity 0 2 = atomVelocity 4 2 := by linarith
  have hsecondZero : atomVelocity 1 0 = atomVelocity 5 0 := by linarith
  have hsecondOne : atomVelocity 1 1 = atomVelocity 5 1 := by linarith
  have hsecondTwo : atomVelocity 1 2 = atomVelocity 5 2 := by linarith
  have hthirdZero : atomVelocity 2 0 = atomVelocity 6 0 := by linarith
  have hthirdOne : atomVelocity 2 1 = atomVelocity 6 1 := by linarith
  have hthirdTwo : atomVelocity 2 2 = atomVelocity 6 2 := by linarith
  refine ⟨funext fun coord => ?_, funext fun coord => ?_, funext fun coord => ?_⟩ <;>
    fin_cases coord <;> assumption

/-- Seven-term expansion, so the mass constraint reads on numeral indices. -/
private theorem sum_over_seven (summand : Fin 7 → ℝ) :
    ∑ index, summand index
      = summand 0 + summand 1 + summand 2 + summand 3 + summand 4 + summand 5
        + summand 6 := by
  simp [Fin.sum_univ_succ]
  ring


/-! ## The matching upper bound: the nine directions SPAN

The nine directions are independent, so the flat space has dimension at least nine.  This
section closes the other half by exhibiting the inverse readout: nine explicit linear
functionals of a flat direction that reproduce it as a combination of the nine.  Together
with `stratumFlatDirection_independent` this pins `dim = 9`; the rank statement that
follows from it is the next section.

The elimination runs on a REDUCED system, and that it suffices is itself part of the
content.  `rainbowSeven_bundleRigid_of_velocity_zero` supplies nine rows; four rainbow
triples supply one row per missed tetrahedron direction (`T_0, T_8, T_12, T_16`, which
between them use only the atoms `0,1,2,3`); the six Parseval entries and the mass supply
seven more.  Twenty rows of rank nineteen.

Counted at the level of the proofs rather than of the summary: the rigidity theorem
instantiates the tie hypothesis at the thirteen indices `0,1,2,4,8,9,10,12,13,14,16,17,18`
and the four spanning rows are among those thirteen, so THIRTEEN tie rows are used and
SEVEN — `T_3, T_5, T_6, T_7, T_11, T_15, T_19` — are never touched. -/

/-- **THE INVERSE READOUT.**  Nine explicit linear functionals of a direction, which on a
FLAT direction are its coordinates in the nine.  The formulas are the inverse of the
`9 × 9` readout block of `stratumFlatDirection_independent`, so they are forced. -/
noncomputable def stratumFlatCoefficient (atomVelocity : Fin 7 → Fin 3 → ℝ)
    (weightVelocity : Fin 7 → ℝ) : Fin 9 → ℝ :=
  ![3/32 * atomVelocity 0 0 + 3/32 * atomVelocity 0 1 + 3/32 * atomVelocity 0 2
      + weightVelocity 0,
    9/32 * atomVelocity 0 0 - 3/32 * atomVelocity 0 1 - 3/32 * atomVelocity 0 2
      + 3/8 * atomVelocity 1 0 + weightVelocity 1,
    -(3/8) * atomVelocity 0 0 + 3/16 * atomVelocity 0 2 - 3/8 * atomVelocity 1 0
      - 3/16 * atomVelocity 1 1 - 3/16 * atomVelocity 2 0 + weightVelocity 2,
    -(1/32) * atomVelocity 0 0 - 1/32 * atomVelocity 0 1 - 1/32 * atomVelocity 0 2,
    -(3/32) * atomVelocity 0 0 + 1/32 * atomVelocity 0 1 + 1/32 * atomVelocity 0 2
      - 1/8 * atomVelocity 1 0,
    1/8 * atomVelocity 0 0 - 1/16 * atomVelocity 0 2 + 1/8 * atomVelocity 1 0
      + 1/16 * atomVelocity 1 1 + 1/16 * atomVelocity 2 0,
    3/4 * atomVelocity 0 0 - 1/2 * atomVelocity 0 1 + 3/4 * atomVelocity 1 0
      + 1/2 * atomVelocity 1 1,
    17/16 * atomVelocity 0 0 - 3/16 * atomVelocity 0 1 - 9/16 * atomVelocity 0 2
      + 3/4 * atomVelocity 1 0 + 3/8 * atomVelocity 1 1 - 1/8 * atomVelocity 2 0,
    3/16 * atomVelocity 0 0 + 3/16 * atomVelocity 0 1 - 3/16 * atomVelocity 0 2
      + 1/2 * atomVelocity 1 0 + 3/8 * atomVelocity 1 1 - 1/8 * atomVelocity 2 0]

/-- **THE NINE DIRECTIONS SPAN THE FLAT SPACE.**  Every admissible direction on which all
twenty rainbow tie forms are stationary is the combination of the nine with coefficients
`stratumFlatCoefficient`. -/
theorem stratumFlat_eq_combination {atomVelocity : Fin 7 → Fin 3 → ℝ}
    {weightVelocity : Fin 7 → ℝ} (hflat : IsSplitSevenFlat atomVelocity weightVelocity) :
    (∀ (atomIndex : Fin 7) (coord : Fin 3), atomVelocity atomIndex coord
        = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
            * stratumFlatDirectionAtom directionIndex atomIndex coord)
      ∧ (∀ atomIndex : Fin 7, weightVelocity atomIndex
        = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
            * stratumFlatDirectionWeight directionIndex atomIndex) := by
  obtain ⟨⟨hmass, hparsevalMatrix⟩, hstationary⟩ := hflat
  obtain ⟨hfirstPair, hsecondPair, hthirdPair⟩ :=
    rainbowSeven_bundleRigid_of_velocity_zero hstationary
  have hpairing : ∀ tripleIndex : Fin 20,
      atomVelocity (rainbowSevenFirst tripleIndex)
          ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex)
        + atomVelocity (rainbowSevenSecond tripleIndex)
          ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex)
        + atomVelocity (rainbowSevenThird tripleIndex)
          ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex) = 0 := by
    intro tripleIndex
    have hvanishes := hstationary tripleIndex
    rw [rainbowSevenVelocityFamily_eq] at hvanishes
    linarith
  have hparseval : ∀ rowIndex colIndex : Fin 3,
      ∑ atomIndex, (weightVelocity atomIndex
            * (splitSevenDesign.atom atomIndex rowIndex
              * splitSevenDesign.atom atomIndex colIndex)
          + splitSevenDesign.weight atomIndex
            * (atomVelocity atomIndex rowIndex * splitSevenDesign.atom atomIndex colIndex
              + splitSevenDesign.atom atomIndex rowIndex
                * atomVelocity atomIndex colIndex)) = 0 := by
    intro rowIndex colIndex
    rw [← parsevalMatrixVelocity_apply, hparsevalMatrix]
    rfl
  have htieThree := hpairing 0
  have htieZero := hpairing 8
  have htieOne := hpairing 12
  have htieTwo := hpairing 16
  simp [rainbowSevenFirst, rainbowSevenSecond, rainbowSevenThird,
    rainbowSevenMissedDirection, dotProduct, Fin.sum_univ_three,
    tetraAtom] at htieThree htieZero htieOne htieTwo
  have hparsevalZeroZero := hparseval 0 0
  have hparsevalZeroOne := hparseval 0 1
  have hparsevalZeroTwo := hparseval 0 2
  have hparsevalOneOne := hparseval 1 1
  have hparsevalOneTwo := hparseval 1 2
  have hparsevalTwoTwo := hparseval 2 2
  simp [Fin.sum_univ_succ, splitSevenDesign, splitSevenAtom, splitSevenDirection,
    tetraAtom] at hparsevalZeroZero hparsevalZeroOne hparsevalZeroTwo
  simp [Fin.sum_univ_succ, splitSevenDesign, splitSevenAtom, splitSevenDirection,
    tetraAtom] at hparsevalOneOne hparsevalOneTwo hparsevalTwoTwo
  rw [sum_over_seven] at hmass
  have hrigidZeroZero := congrFun hfirstPair 0
  have hrigidZeroOne := congrFun hfirstPair 1
  have hrigidZeroTwo := congrFun hfirstPair 2
  have hrigidOneZero := congrFun hsecondPair 0
  have hrigidOneOne := congrFun hsecondPair 1
  have hrigidOneTwo := congrFun hsecondPair 2
  have hrigidTwoZero := congrFun hthirdPair 0
  have hrigidTwoOne := congrFun hthirdPair 1
  have hrigidTwoTwo := congrFun hthirdPair 2
  have hatomZeroZero : atomVelocity 0 0
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 0 0 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomZeroOne : atomVelocity 0 1
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 0 1 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomZeroTwo : atomVelocity 0 2
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 0 2 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomOneZero : atomVelocity 1 0
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 1 0 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomOneOne : atomVelocity 1 1
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 1 1 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomOneTwo : atomVelocity 1 2
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 1 2 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomTwoZero : atomVelocity 2 0
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 2 0 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomTwoOne : atomVelocity 2 1
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 2 1 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomTwoTwo : atomVelocity 2 2
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 2 2 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomThreeZero : atomVelocity 3 0
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 3 0 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomThreeOne : atomVelocity 3 1
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 3 1 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomThreeTwo : atomVelocity 3 2
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 3 2 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomFourZero : atomVelocity 4 0
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 4 0 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomFourOne : atomVelocity 4 1
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 4 1 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomFourTwo : atomVelocity 4 2
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 4 2 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomFiveZero : atomVelocity 5 0
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 5 0 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomFiveOne : atomVelocity 5 1
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 5 1 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomFiveTwo : atomVelocity 5 2
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 5 2 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomSixZero : atomVelocity 6 0
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 6 0 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomSixOne : atomVelocity 6 1
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 6 1 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hatomSixTwo : atomVelocity 6 2
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionAtom directionIndex 6 2 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionAtom, bundleTotalAtomVelocity,
      gaugeRotationAtomVelocity]
    linarith
  have hweightZero : weightVelocity 0
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionWeight directionIndex 0 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionWeight, weightSplitWeightVelocity,
      bundleTotalWeightVelocity]
    linarith
  have hweightOne : weightVelocity 1
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionWeight directionIndex 1 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionWeight, weightSplitWeightVelocity,
      bundleTotalWeightVelocity]
    linarith
  have hweightTwo : weightVelocity 2
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionWeight directionIndex 2 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionWeight, weightSplitWeightVelocity,
      bundleTotalWeightVelocity]
    linarith
  have hweightThree : weightVelocity 3
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionWeight directionIndex 3 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionWeight, weightSplitWeightVelocity,
      bundleTotalWeightVelocity]
    linarith
  have hweightFour : weightVelocity 4
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionWeight directionIndex 4 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionWeight, weightSplitWeightVelocity,
      bundleTotalWeightVelocity]
    linarith
  have hweightFive : weightVelocity 5
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionWeight directionIndex 5 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionWeight, weightSplitWeightVelocity,
      bundleTotalWeightVelocity]
    linarith
  have hweightSix : weightVelocity 6
      = ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity directionIndex
          * stratumFlatDirectionWeight directionIndex 6 := by
    rw [sum_over_nine]
    simp [stratumFlatCoefficient, stratumFlatDirectionWeight, weightSplitWeightVelocity,
      bundleTotalWeightVelocity]
    linarith
  refine ⟨fun atomIndex coord => ?_, fun atomIndex => ?_⟩
  · fin_cases atomIndex <;> fin_cases coord <;> assumption
  · fin_cases atomIndex <;> assumption

/-- **DIMENSION EXACTLY NINE.**  Put beside `stratumFlatDirection_isFlat` and
`stratumFlatDirection_independent`, the spanning theorem above pins the flat space: nine
flat directions, linearly independent, and every flat direction a combination of them.

[The `Module.finrank` form of the same statement is `stratumStackedJacobian_finrank_ker`
below, and the rank of the stacked Jacobian follows from it by rank–nullity in
`stratumStackedJacobian_finrank_range`.] -/
theorem stratumFlat_coefficient_unique {atomVelocity : Fin 7 → Fin 3 → ℝ}
    {weightVelocity : Fin 7 → ℝ} (hflat : IsSplitSevenFlat atomVelocity weightVelocity)
    (coefficient : Fin 9 → ℝ)
    (hatom : ∀ (atomIndex : Fin 7) (coord : Fin 3), atomVelocity atomIndex coord
        = ∑ directionIndex, coefficient directionIndex
            * stratumFlatDirectionAtom directionIndex atomIndex coord)
    (hweight : ∀ atomIndex : Fin 7, weightVelocity atomIndex
        = ∑ directionIndex, coefficient directionIndex
            * stratumFlatDirectionWeight directionIndex atomIndex) :
    coefficient = stratumFlatCoefficient atomVelocity weightVelocity := by
  obtain ⟨hcanonicalAtom, hcanonicalWeight⟩ := stratumFlat_eq_combination hflat
  have hdifference : ∀ directionIndex : Fin 9,
      coefficient directionIndex - stratumFlatCoefficient atomVelocity weightVelocity
        directionIndex = 0 := by
    refine stratumFlatDirection_independent _ (fun atomIndex coord => ?_)
      (fun atomIndex => ?_)
    · have hexpand : (∑ directionIndex, (coefficient directionIndex
              - stratumFlatCoefficient atomVelocity weightVelocity directionIndex)
              * stratumFlatDirectionAtom directionIndex atomIndex coord)
            + ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity
                directionIndex * stratumFlatDirectionAtom directionIndex atomIndex coord
            = ∑ directionIndex, coefficient directionIndex
                * stratumFlatDirectionAtom directionIndex atomIndex coord := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun directionIndex _ => by ring
      rw [← hcanonicalAtom atomIndex coord, ← hatom atomIndex coord] at hexpand
      linarith
    · have hexpand : (∑ directionIndex, (coefficient directionIndex
              - stratumFlatCoefficient atomVelocity weightVelocity directionIndex)
              * stratumFlatDirectionWeight directionIndex atomIndex)
            + ∑ directionIndex, stratumFlatCoefficient atomVelocity weightVelocity
                directionIndex * stratumFlatDirectionWeight directionIndex atomIndex
            = ∑ directionIndex, coefficient directionIndex
                * stratumFlatDirectionWeight directionIndex atomIndex := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun directionIndex _ => by ring
      rw [← hcanonicalWeight atomIndex, ← hweight atomIndex] at hexpand
      linarith
  funext directionIndex
  linarith [hdifference directionIndex]

/-! ## The rank of the stacked Jacobian

The three theorems above pin the flat space to dimension nine.  This section turns that
into the RANK statement: the stacked Jacobian is exhibited as an honest linear map, its
kernel is shown to be exactly the flat space, the nine directions are assembled into a
basis of that kernel, and rank–nullity finishes.

The codomain is deliberately UNREDUCED — the Parseval component is the whole `3 x 3`
matrix rather than its six independent entries, and no attempt is made to say that only
`27` of the coordinates are independent.  That costs nothing: the rank of a linear map is
`dim(domain) − dim(ker)`, so padding the codomain cannot change it, and the domain and the
kernel are exactly what the previous section computed. -/

/-- The Parseval velocity is additive in the direction. -/
theorem parsevalMatrixVelocity_add (design : WeightedDesign m k)
    (firstAtomVelocity secondAtomVelocity : Fin m → Fin k → ℝ)
    (firstWeightVelocity secondWeightVelocity : Fin m → ℝ) :
    parsevalMatrixVelocity design (firstAtomVelocity + secondAtomVelocity)
        (firstWeightVelocity + secondWeightVelocity)
      = parsevalMatrixVelocity design firstAtomVelocity firstWeightVelocity
        + parsevalMatrixVelocity design secondAtomVelocity secondWeightVelocity := by
  ext rowIndex colIndex
  simp only [parsevalMatrixVelocity_apply, Matrix.add_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun atomIndex _ => by ring

/-- The Parseval velocity is homogeneous in the direction. -/
theorem parsevalMatrixVelocity_smul (design : WeightedDesign m k) (scalar : ℝ)
    (atomVelocity : Fin m → Fin k → ℝ) (weightVelocity : Fin m → ℝ) :
    parsevalMatrixVelocity design (scalar • atomVelocity) (scalar • weightVelocity)
      = scalar • parsevalMatrixVelocity design atomVelocity weightVelocity := by
  ext rowIndex colIndex
  simp only [parsevalMatrixVelocity_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun atomIndex _ => by ring

/-- Every tie-form velocity is additive in the atom direction. -/
theorem rainbowSevenVelocityFamily_add
    (firstAtomVelocity secondAtomVelocity : Fin 7 → Fin 3 → ℝ) (tripleIndex : Fin 20) :
    rainbowSevenVelocityFamily (firstAtomVelocity + secondAtomVelocity) tripleIndex
      = rainbowSevenVelocityFamily firstAtomVelocity tripleIndex
        + rainbowSevenVelocityFamily secondAtomVelocity tripleIndex := by
  rw [rainbowSevenVelocityFamily_eq, rainbowSevenVelocityFamily_eq,
    rainbowSevenVelocityFamily_eq]
  simp only [Pi.add_apply, add_dotProduct]
  ring

/-- Every tie-form velocity is homogeneous in the atom direction. -/
theorem rainbowSevenVelocityFamily_smul (scalar : ℝ) (atomVelocity : Fin 7 → Fin 3 → ℝ)
    (tripleIndex : Fin 20) :
    rainbowSevenVelocityFamily (scalar • atomVelocity) tripleIndex
      = scalar * rainbowSevenVelocityFamily atomVelocity tripleIndex := by
  rw [rainbowSevenVelocityFamily_eq, rainbowSevenVelocityFamily_eq]
  simp only [Pi.smul_apply, smul_dotProduct, smul_eq_mul]
  ring

/-- **THE STACKED JACOBIAN, AS A LINEAR MAP.**  Twenty rainbow tie-form velocities, the
matrix Parseval velocity, and the mass velocity, on the `21 + 7 = 28`-dimensional space of
`(atom velocity, weight velocity)` pairs. -/
noncomputable def stratumStackedJacobian :
    ((Fin 7 → Fin 3 → ℝ) × (Fin 7 → ℝ)) →ₗ[ℝ]
      ((Fin 20 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ × ℝ) where
  toFun direction :=
    (fun tripleIndex => rainbowSevenVelocityFamily direction.1 tripleIndex,
      parsevalMatrixVelocity splitSevenDesign direction.1 direction.2,
      ∑ atomIndex, direction.2 atomIndex)
  map_add' firstDirection secondDirection := by
    refine Prod.ext (funext fun tripleIndex => ?_) (Prod.ext ?_ ?_)
    · simpa using rainbowSevenVelocityFamily_add firstDirection.1 secondDirection.1 tripleIndex
    · simpa using parsevalMatrixVelocity_add splitSevenDesign firstDirection.1 secondDirection.1
        firstDirection.2 secondDirection.2
    · simpa using Finset.sum_add_distrib (f := firstDirection.2) (g := secondDirection.2)
  map_smul' scalar direction := by
    refine Prod.ext (funext fun tripleIndex => ?_) (Prod.ext ?_ ?_)
    · simpa using rainbowSevenVelocityFamily_smul scalar direction.1 tripleIndex
    · simpa using parsevalMatrixVelocity_smul splitSevenDesign scalar direction.1 direction.2
    · simpa using (Finset.mul_sum Finset.univ direction.2 scalar).symm

@[simp] theorem stratumStackedJacobian_apply
    (direction : (Fin 7 → Fin 3 → ℝ) × (Fin 7 → ℝ)) :
    stratumStackedJacobian direction
      = (fun tripleIndex => rainbowSevenVelocityFamily direction.1 tripleIndex,
          parsevalMatrixVelocity splitSevenDesign direction.1 direction.2,
          ∑ atomIndex, direction.2 atomIndex) := rfl

/-- **THE KERNEL IS THE FLAT SPACE.**  By construction, but stated so that the dimension
theorems above become dimension theorems about this map's kernel. -/
theorem mem_ker_stratumStackedJacobian_iff
    (direction : (Fin 7 → Fin 3 → ℝ) × (Fin 7 → ℝ)) :
    direction ∈ LinearMap.ker stratumStackedJacobian
      ↔ IsSplitSevenFlat direction.1 direction.2 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hzero
    refine ⟨⟨?_, ?_⟩, fun tripleIndex => ?_⟩
    · simpa using congrArg (fun value => value.2.2) hzero
    · simpa using congrArg (fun value => value.2.1) hzero
    · simpa using congrArg (fun value => value.1 tripleIndex) hzero
  · rintro ⟨⟨hmass, hparseval⟩, hties⟩
    refine Prod.ext (funext fun tripleIndex => ?_) (Prod.ext ?_ ?_)
    · simpa using hties tripleIndex
    · simpa using hparseval
    · simpa using hmass

/-- The nine flat directions as points of the direction space. -/
noncomputable def stratumFlatDirectionPair : Fin 9 → ((Fin 7 → Fin 3 → ℝ) × (Fin 7 → ℝ)) :=
  fun directionIndex =>
    (stratumFlatDirectionAtom directionIndex, stratumFlatDirectionWeight directionIndex)

theorem stratumFlatDirectionPair_mem_ker (directionIndex : Fin 9) :
    stratumFlatDirectionPair directionIndex ∈ LinearMap.ker stratumStackedJacobian :=
  (mem_ker_stratumStackedJacobian_iff _).mpr (stratumFlatDirection_isFlat directionIndex)

/-- The nine flat directions, as a family inside the kernel. -/
noncomputable def stratumFlatKernelFamily :
    Fin 9 → (LinearMap.ker stratumStackedJacobian) :=
  fun directionIndex =>
    ⟨stratumFlatDirectionPair directionIndex, stratumFlatDirectionPair_mem_ker directionIndex⟩

/-- Coordinate readout of a combination of the nine, on the atom side. -/
private theorem sum_smul_stratumFlatDirectionPair_atom (coefficient : Fin 9 → ℝ)
    (atomIndex : Fin 7) (coord : Fin 3) :
    (∑ directionIndex, coefficient directionIndex • stratumFlatDirectionPair directionIndex).1
        atomIndex coord
      = ∑ directionIndex, coefficient directionIndex
          * stratumFlatDirectionAtom directionIndex atomIndex coord := by
  simp [stratumFlatDirectionPair, Prod.fst_sum, Finset.sum_apply]

/-- Coordinate readout of a combination of the nine, on the weight side. -/
private theorem sum_smul_stratumFlatDirectionPair_weight (coefficient : Fin 9 → ℝ)
    (atomIndex : Fin 7) :
    (∑ directionIndex, coefficient directionIndex • stratumFlatDirectionPair directionIndex).2
        atomIndex
      = ∑ directionIndex, coefficient directionIndex
          * stratumFlatDirectionWeight directionIndex atomIndex := by
  simp [stratumFlatDirectionPair, Prod.snd_sum, Finset.sum_apply]

theorem stratumFlatKernelFamily_linearIndependent :
    LinearIndependent ℝ stratumFlatKernelFamily := by
  rw [Fintype.linearIndependent_iff]
  intro coefficient hsum
  have hambient : (∑ directionIndex,
      coefficient directionIndex • stratumFlatDirectionPair directionIndex) = 0 := by
    have hcoe := congrArg Subtype.val hsum
    simpa [stratumFlatKernelFamily, Submodule.coe_sum] using hcoe
  refine stratumFlatDirection_independent coefficient (fun atomIndex coord => ?_)
    (fun atomIndex => ?_)
  · rw [← sum_smul_stratumFlatDirectionPair_atom, hambient]; rfl
  · rw [← sum_smul_stratumFlatDirectionPair_weight, hambient]; rfl

theorem stratumFlatKernelFamily_span :
    ⊤ ≤ Submodule.span ℝ (Set.range stratumFlatKernelFamily) := by
  rintro ⟨direction, hmem⟩ -
  rw [Submodule.mem_span_range_iff_exists_fun]
  obtain ⟨hatom, hweight⟩ :=
    stratumFlat_eq_combination ((mem_ker_stratumStackedJacobian_iff direction).mp hmem)
  refine ⟨stratumFlatCoefficient direction.1 direction.2, Subtype.ext ?_⟩
  have hcoe : ((∑ directionIndex, stratumFlatCoefficient direction.1 direction.2 directionIndex
        • stratumFlatKernelFamily directionIndex : LinearMap.ker stratumStackedJacobian) :
          (Fin 7 → Fin 3 → ℝ) × (Fin 7 → ℝ))
      = ∑ directionIndex, stratumFlatCoefficient direction.1 direction.2 directionIndex
          • stratumFlatDirectionPair directionIndex := by
    simp [stratumFlatKernelFamily]
  rw [hcoe]
  refine Prod.ext (funext fun atomIndex => funext fun coord => ?_) (funext fun atomIndex => ?_)
  · rw [sum_smul_stratumFlatDirectionPair_atom]; exact (hatom atomIndex coord).symm
  · rw [sum_smul_stratumFlatDirectionPair_weight]; exact (hweight atomIndex).symm

/-- **THE NINE ARE A BASIS OF THE KERNEL.** -/
noncomputable def stratumFlatKernelBasis :
    Module.Basis (Fin 9) ℝ (LinearMap.ker stratumStackedJacobian) :=
  Module.Basis.mk stratumFlatKernelFamily_linearIndependent stratumFlatKernelFamily_span

/-- **THE FLAT SPACE HAS DIMENSION EXACTLY NINE**, now as a `finrank`. -/
theorem stratumStackedJacobian_finrank_ker :
    Module.finrank ℝ (LinearMap.ker stratumStackedJacobian) = 9 := by
  rw [Module.finrank_eq_card_basis stratumFlatKernelBasis, Fintype.card_fin]

/-- The direction space is `21 + 7 = 28`-dimensional. -/
theorem stratumDirectionSpace_finrank :
    Module.finrank ℝ ((Fin 7 → Fin 3 → ℝ) × (Fin 7 → ℝ)) = 28 := by
  simp [Module.finrank_prod, Module.finrank_pi_fintype]

/-- **THE STACKED JACOBIAN HAS RANK EXACTLY NINETEEN.**  Rank–nullity on
`stratumStackedJacobian`: the domain is `28`-dimensional, the kernel is the flat space and
is `9`-dimensional, so the range is `19`-dimensional.  This is the number the campaign
measured by exact rational elimination; it is now a theorem. -/
theorem stratumStackedJacobian_finrank_range :
    Module.finrank ℝ (LinearMap.range stratumStackedJacobian) = 19 := by
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker stratumStackedJacobian
  rw [stratumStackedJacobian_finrank_ker, stratumDirectionSpace_finrank] at hrankNullity
  omega

/-! ## Covering on the whole tie class through the split tetrahedron

The flat directions above are the tangent to a genuine surface, and the surface is
covered.  `Gtz.splitClassDesign` puts the corank-one atom of each class on the atoms
carrying it, evaluated at the CLASS TOTALS, so the class through the split tetrahedron is
a section over the whole open weight simplex.  All of it ties, and all of it has a
dominating triple. -/

/-- **The tie class through the split tetrahedron**, at an arbitrary weight vector: the
`(2,2,2,1)` branch of `Gtz.splitClassDesign` on the atom-to-direction map of
`splitSevenDesign` itself. -/
noncomputable def splitSevenClassDesign (weight : Fin 7 → ℝ)
    (hpos : ∀ atomIndex, 0 < weight atomIndex)
    (hsum : ∑ atomIndex, weight atomIndex = 1) : WeightedDesign 7 3 :=
  splitClassDesign splitSevenDirection weight (by norm_num) (by decide) hpos hsum

@[simp] theorem splitSevenClassDesign_weight (weight : Fin 7 → ℝ)
    (hpos : ∀ atomIndex, 0 < weight atomIndex) (hsum : ∑ atomIndex, weight atomIndex = 1) :
    (splitSevenClassDesign weight hpos hsum).weight = weight := rfl

/-- Every point of the class is an exact tie. -/
theorem splitSevenClassDesign_isTie (weight : Fin 7 → ℝ)
    (hpos : ∀ atomIndex, 0 < weight atomIndex) (hsum : ∑ atomIndex, weight atomIndex = 1) :
    IsTie (splitSevenClassDesign weight hpos hsum) :=
  splitClassDesign_isTie splitSevenDirection weight (by norm_num) (by decide) hpos hsum

/-- **THE CLASS IS COVERED.**  Every design on the tie class through the split
tetrahedron — a six-parameter section over the open weight simplex, not one point — has a
dominating triple.  This is the leg a near-tie design is handed to once a merge or a dust
drop has put it back on the class. -/
theorem splitSevenClassDesign_exists_dominatingTriple (weight : Fin 7 → ℝ)
    (hpos : ∀ atomIndex, 0 < weight atomIndex) (hsum : ∑ atomIndex, weight atomIndex = 1) :
    ∃ selected : Finset (Fin 7), selected.card = 3
      ∧ Dominates (splitSevenClassDesign weight hpos hsum) selected :=
  (splitSevenClassDesign_isTie weight hpos hsum).1

/-! ### The class really does pass through the split tetrahedron

The section above is named "the class through the split tetrahedron", and the name is a
theorem: evaluated at `splitSevenDesign.weight` the section returns `splitSevenDesign`
itself.  That is not formal — the class atoms come from the Householder construction
`Gtz.simplexTieAtom` at the class totals, not from `Gtz.tetraAtom` — so it is proved
here, through the exact value of the reflector at uniform class weight `1/4`. -/

/-- The four class totals of the split tetrahedron are all `1/4`: direction `3` carries
the single weight-`1/4` atom, and each other direction carries two weight-`1/8` copies. -/
theorem splitSevenClassTotalWeight_eq_quarter (label : Fin 4) :
    classTotalWeight splitSevenDirection splitSevenDesign.weight label = 1/4 := by
  rw [classTotalWeight, Finset.sum_filter]
  fin_cases label <;>
    simp [Fin.sum_univ_seven, splitSevenDirection, splitSevenDesign_weight_apply] <;>
    norm_num

/-- At uniform weight the tie defect is `1/2`: `sqrt((1 − 1/4)/3) = sqrt(1/4)`. -/
theorem tieDefect_uniformQuarter (label : Fin 4) :
    tieDefect (k := 3) (fun _ => (1/4 : ℝ)) label = 1/2 := by
  have hvalue : ((1 : ℝ) - (fun _ : Fin 4 => (1/4 : ℝ)) label) / ((3 : ℕ) : ℝ)
      = (1/2 : ℝ) ^ 2 := by norm_num
  rw [tieDefect, hvalue, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1/2)]

/-- Hence the reflector is `(−1/2, 1/2, 1/2, 1/2)`, of unit length. -/
theorem tieReflector_uniformQuarter (label : Fin 4) :
    tieReflector (k := 3) (fun _ => (1/4 : ℝ)) label
      = 1/2 - (if label = 0 then (1 : ℝ) else 0) := by
  rw [tieReflector, tieDefect_uniformQuarter]

/-- **THE SPLIT TETRAHEDRON IS THE CLASS SECTION'S VALUE AT ITS OWN WEIGHT.**  At uniform
class weight `1/4` the corank-one Householder atom is exactly the tetrahedron direction,
coordinate by coordinate. -/
theorem simplexTieAtom_uniformQuarter_eq_tetraAtom (direction : Fin 4) (coord : Fin 3) :
    simplexTieAtom (k := 3) (fun _ => (1/4 : ℝ)) direction coord = tetraAtom direction coord := by
  have hsqrt : Real.sqrt ((fun _ : Fin 4 => (1/4 : ℝ)) direction) = 1/2 := by
    have hvalue : (fun _ : Fin 4 => (1/4 : ℝ)) direction = (1/2 : ℝ) ^ 2 := by norm_num
    rw [hvalue, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [simplexTieAtom, hsqrt, tieHouseholder_apply, tieReflector_uniformQuarter,
    tieReflector_uniformQuarter, tieDefect_uniformQuarter]
  fin_cases direction <;> fin_cases coord <;>
    norm_num +decide [tetraAtom, Fin.succ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]

/-- **THE CLASS PASSES THROUGH THE SPLIT TETRAHEDRON.**  The six-parameter section
evaluated at the split tetrahedron's own weight vector IS the split tetrahedron, so every
theorem of the class section applies at the point the rest of this file studies. -/
theorem splitSevenClassDesign_eq_splitSevenDesign :
    splitSevenClassDesign splitSevenDesign.weight splitSevenDesign.weight_pos
        splitSevenDesign.weight_sum_one = splitSevenDesign := by
  refine WeightedDesign.ext (funext fun atomIndex => funext fun coord => ?_) rfl
  have hatom : (splitSevenClassDesign splitSevenDesign.weight splitSevenDesign.weight_pos
        splitSevenDesign.weight_sum_one).atom atomIndex coord
      = simplexTieAtom (classTotalWeight splitSevenDirection splitSevenDesign.weight)
          (splitSevenDirection atomIndex) coord := rfl
  rw [hatom, funext splitSevenClassTotalWeight_eq_quarter,
    simplexTieAtom_uniformQuarter_eq_tetraAtom, splitSevenDesign_atom]

/-- **THE GRAPHIC REALIZATION IS COVERED, AT EVERY RANK, WITH A NAMED WITNESS.**  The
bundled cycle with graph-induced conductance is dominated by an explicit spanning tree —
one edge out of each arc but one.  `Gtz.bundledCycle_isTie` gives the same subset
existentially; this states which subset it is, which is what a covering argument needs.

[The five `(6,3)` and `(7,3)` instances an earlier draft of this file also shipped were
literally the first components of `Gtz.bundlingSixThreeHeavy_isTie` and its four
companions, which already ship and are already audited upstream.  They are gone; use the
upstream tie theorems, or this one with the bundling of interest.] -/
theorem bundledCycle_exists_dominatingSubset {edgeCount vertexRank : ℕ}
    (bundling : CycleBundling edgeCount vertexRank) (hrank : 1 ≤ vertexRank) :
    Dominates (bundledCycleDesign bundling hrank) (bundledCycleTree bundling 0)
      ∧ (bundledCycleTree bundling 0).card = vertexRank :=
  ⟨bundledCycleTree_dominates bundling hrank 0, bundledCycleTree_card bundling 0⟩

/-! ## The tube: covering reduced to one determinant sign -/

/-- Every coordinate of every tetrahedron direction is `±1`. -/
theorem tetraAtom_abs_eq_one (direction : Fin 4) (coord : Fin 3) :
    |tetraAtom direction coord| = 1 := by
  fin_cases direction <;> fin_cases coord <;> simp [tetraAtom]

/-- Hence every coordinate squares to one. -/
theorem tetraAtom_mul_self_eq_one (direction : Fin 4) (coord : Fin 3) :
    tetraAtom direction coord * tetraAtom direction coord = 1 := by
  rw [← abs_mul_abs_self, tetraAtom_abs_eq_one, one_mul]

/-- Every coordinate of every atom of the split tetrahedron is `±1`. -/
theorem splitSevenDesign_atom_abs_eq_one (atomIndex : Fin 7) (coord : Fin 3) :
    |splitSevenDesign.atom atomIndex coord| = 1 := by
  rw [splitSevenDesign_atom, tetraAtom_abs_eq_one]

/-- **The tie gap of a rainbow triple, entry by entry**: `3·I − v vᵀ` at the missed
direction, so the diagonal is `2` and every off-diagonal entry is `±1`. -/
theorem rainbowSevenTriple_gapEntry (tripleIndex : Fin 20) (rowIndex colIndex : Fin 3) :
    (subsetSum splitSevenDesign (rainbowSevenTriple tripleIndex) - 1) rowIndex colIndex
      = 3 * (if rowIndex = colIndex then (1 : ℝ) else 0)
        - tetraAtom (rainbowSevenMissedDirection tripleIndex) rowIndex
          * tetraAtom (rainbowSevenMissedDirection tripleIndex) colIndex := by
  rw [splitSevenDesign_subsetSum_rainbow]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The tie gap's diagonal is exactly `2`. -/
theorem rainbowSevenTriple_gapEntry_diagonal (tripleIndex : Fin 20) (coord : Fin 3) :
    (subsetSum splitSevenDesign (rainbowSevenTriple tripleIndex) - 1) coord coord = 2 := by
  rw [rainbowSevenTriple_gapEntry, if_pos rfl, tetraAtom_mul_self_eq_one]
  norm_num

/-- Off the diagonal the tie gap entry is exactly `±1`. -/
theorem rainbowSevenTriple_gapEntry_abs_offDiagonal (tripleIndex : Fin 20)
    {rowIndex colIndex : Fin 3} (hne : rowIndex ≠ colIndex) :
    |(subsetSum splitSevenDesign (rainbowSevenTriple tripleIndex) - 1) rowIndex colIndex|
      = 1 := by
  rw [rainbowSevenTriple_gapEntry, if_neg hne, mul_zero, zero_sub, abs_neg, abs_mul,
    tetraAtom_abs_eq_one, tetraAtom_abs_eq_one, one_mul]

/-- A product of two coordinates moves by at most `radius · (2 + radius)` when each
coordinate moves by at most `radius` from a base of absolute value one.  This is the
sum-of-absolute-coefficients bound in its smallest instance. -/
private theorem abs_product_dist_le {leftBase leftMoved rightBase rightMoved radius : ℝ}
    (hradius : 0 ≤ radius) (hleftBase : |leftBase| = 1) (hrightBase : |rightBase| = 1)
    (hleft : |leftMoved - leftBase| ≤ radius) (hright : |rightMoved - rightBase| ≤ radius) :
    |leftMoved * rightMoved - leftBase * rightBase| ≤ radius * (2 + radius) := by
  have hrightSplit : rightMoved = (rightMoved - rightBase) + rightBase := by ring
  have hrightMovedAbs : |rightMoved| ≤ 1 + radius := by
    calc |rightMoved| = |(rightMoved - rightBase) + rightBase| := by rw [← hrightSplit]
      _ ≤ |rightMoved - rightBase| + |rightBase| := abs_add_le _ _
      _ ≤ radius + 1 := by rw [hrightBase]; linarith
      _ = 1 + radius := by ring
  have hkey : leftMoved * rightMoved - leftBase * rightBase
      = (leftMoved - leftBase) * rightMoved + leftBase * (rightMoved - rightBase) := by ring
  rw [hkey]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, hleftBase, one_mul]
  have hfirst : |leftMoved - leftBase| * |rightMoved| ≤ radius * (1 + radius) :=
    mul_le_mul hleft hrightMovedAbs (abs_nonneg _) hradius
  nlinarith [hright]

/-- **THE ENTRYWISE TUBE BOUND.**  In a sup-norm tube of radius `radius` around the split
tetrahedron, every entry of every rainbow gap sits within `3 · radius · (2 + radius)` of
its value at the tie.  Three atoms, one product each: the sum of absolute coefficients is
`3`, and the bound is linear in the radius with an explicit quadratic correction. -/
theorem rainbowSeven_gapEntry_dist_le (design : WeightedDesign 7 3) (tripleIndex : Fin 20)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (htube : ∀ (atomIndex : Fin 7) (coord : Fin 3),
        |design.atom atomIndex coord - splitSevenDesign.atom atomIndex coord| ≤ radius)
    (rowIndex colIndex : Fin 3) :
    |(subsetSum design (rainbowSevenTriple tripleIndex) - 1) rowIndex colIndex
        - (subsetSum splitSevenDesign (rainbowSevenTriple tripleIndex) - 1) rowIndex colIndex|
      ≤ 3 * (radius * (2 + radius)) := by
  have hentry : ∀ candidate : WeightedDesign 7 3,
      (subsetSum candidate (rainbowSevenTriple tripleIndex) - 1) rowIndex colIndex
        = (∑ atomIndex ∈ rainbowSevenTriple tripleIndex,
            candidate.atom atomIndex rowIndex * candidate.atom atomIndex colIndex)
          - (if rowIndex = colIndex then (1 : ℝ) else 0) := by
    intro candidate
    simp [subsetSum, Matrix.sub_apply, Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply,
      Matrix.one_apply]
  have hperAtom : ∀ atomIndex : Fin 7,
      |design.atom atomIndex rowIndex * design.atom atomIndex colIndex
          - splitSevenDesign.atom atomIndex rowIndex * splitSevenDesign.atom atomIndex colIndex|
        ≤ radius * (2 + radius) := fun atomIndex =>
    abs_product_dist_le hradius (splitSevenDesign_atom_abs_eq_one atomIndex rowIndex)
      (splitSevenDesign_atom_abs_eq_one atomIndex colIndex) (htube atomIndex rowIndex)
      (htube atomIndex colIndex)
  rw [hentry, hentry]
  have hcollapse : ((∑ atomIndex ∈ rainbowSevenTriple tripleIndex,
          design.atom atomIndex rowIndex * design.atom atomIndex colIndex)
        - (if rowIndex = colIndex then (1 : ℝ) else 0))
      - ((∑ atomIndex ∈ rainbowSevenTriple tripleIndex,
          splitSevenDesign.atom atomIndex rowIndex * splitSevenDesign.atom atomIndex colIndex)
        - (if rowIndex = colIndex then (1 : ℝ) else 0))
      = (design.atom (rainbowSevenFirst tripleIndex) rowIndex
            * design.atom (rainbowSevenFirst tripleIndex) colIndex
          - splitSevenDesign.atom (rainbowSevenFirst tripleIndex) rowIndex
            * splitSevenDesign.atom (rainbowSevenFirst tripleIndex) colIndex)
        + (design.atom (rainbowSevenSecond tripleIndex) rowIndex
            * design.atom (rainbowSevenSecond tripleIndex) colIndex
          - splitSevenDesign.atom (rainbowSevenSecond tripleIndex) rowIndex
            * splitSevenDesign.atom (rainbowSevenSecond tripleIndex) colIndex)
        + (design.atom (rainbowSevenThird tripleIndex) rowIndex
            * design.atom (rainbowSevenThird tripleIndex) colIndex
          - splitSevenDesign.atom (rainbowSevenThird tripleIndex) rowIndex
            * splitSevenDesign.atom (rainbowSevenThird tripleIndex) colIndex) := by
    rw [sum_rainbowSevenTriple, sum_rainbowSevenTriple]
    ring
  rw [hcollapse]
  refine (abs_add_three _ _ _).trans ?_
  have hfirst := hperAtom (rainbowSevenFirst tripleIndex)
  have hsecond := hperAtom (rainbowSevenSecond tripleIndex)
  have hthird := hperAtom (rainbowSevenThird tripleIndex)
  linarith

/-- Two diagonal entries near `2` beat one off-diagonal entry near `1`: the two-by-two
principal minor is nonnegative whenever the entrywise deviation stays at or below `1/2`,
which is exactly where `(2 − deviation)^2 ≥ (1 + deviation)^2` still holds. -/
private theorem minor_nonneg_of_entryBounds {diagLeft diagRight offDiag deviation : ℝ}
    (hdeviationSmall : deviation ≤ 1 / 2)
    (hleft : 2 - deviation ≤ diagLeft) (hright : 2 - deviation ≤ diagRight)
    (hoff : |offDiag| ≤ 1 + deviation) :
    0 ≤ diagLeft * diagRight - offDiag ^ 2 := by
  have hbase : (0 : ℝ) < 2 - deviation := by linarith
  have hproduct : (2 - deviation) * (2 - deviation) ≤ diagLeft * diagRight :=
    mul_le_mul hleft hright (by linarith) (by linarith)
  have hbounds := abs_le.mp hoff
  nlinarith [hbounds.1, hbounds.2]

/-- **THE TUBE REDUCTION.**  At radius at most `1/16` around the split tetrahedron, a
rainbow triple DOMINATES as soon as its gap determinant is nonnegative.

Everything Sylvester's all-principal-minors criterion needs beyond the determinant is
proved from the radius: the entrywise deviation is at most `99/256`, so the diagonal is at
least `413/256` and every off-diagonal entry at most `355/256`, and `413 > 355` closes the
three two-by-two minors.  `Gtz.posSemidef_three_of_principalMinors` is the criterion, with
no strictness anywhere — which is what a boundary problem needs. -/
theorem rainbowSeven_dominates_of_tube_of_determinant (design : WeightedDesign 7 3)
    (tripleIndex : Fin 20) (radius : ℝ) (hradiusNonneg : 0 ≤ radius)
    (hradiusSmall : radius ≤ 1 / 16)
    (htube : ∀ (atomIndex : Fin 7) (coord : Fin 3),
        |design.atom atomIndex coord - splitSevenDesign.atom atomIndex coord| ≤ radius)
    (hdeterminant : 0 ≤ (subsetSum design (rainbowSevenTriple tripleIndex) - 1).det) :
    Dominates design (rainbowSevenTriple tripleIndex) := by
  have hdeviation : ∀ rowIndex colIndex : Fin 3,
      |(subsetSum design (rainbowSevenTriple tripleIndex) - 1) rowIndex colIndex
        - (subsetSum splitSevenDesign (rainbowSevenTriple tripleIndex) - 1) rowIndex colIndex|
        ≤ 99 / 256 := by
    intro rowIndex colIndex
    refine (rainbowSeven_gapEntry_dist_le design tripleIndex radius hradiusNonneg htube
      rowIndex colIndex).trans ?_
    nlinarith
  have hdiagonal : ∀ coord : Fin 3,
      2 - 99 / 256
        ≤ (subsetSum design (rainbowSevenTriple tripleIndex) - 1) coord coord := by
    intro coord
    have hbounds := abs_le.mp (hdeviation coord coord)
    rw [rainbowSevenTriple_gapEntry_diagonal] at hbounds
    linarith [hbounds.1]
  have hoffDiagonal : ∀ rowIndex colIndex : Fin 3, rowIndex ≠ colIndex →
      |(subsetSum design (rainbowSevenTriple tripleIndex) - 1) rowIndex colIndex|
        ≤ 1 + 99 / 256 := by
    intro rowIndex colIndex hdistinct
    have hbounds := abs_le.mp (hdeviation rowIndex colIndex)
    have htie := abs_le.mp
      (le_of_eq (rainbowSevenTriple_gapEntry_abs_offDiagonal tripleIndex hdistinct))
    rw [abs_le]
    constructor <;> linarith [hbounds.1, hbounds.2, htie.1, htie.2]
  refine posSemidef_three_of_principalMinors (subsetSum_sub_one_transpose design _)
    (by linarith [hdiagonal 0]) (by linarith [hdiagonal 1]) (by linarith [hdiagonal 2])
    ?_ ?_ ?_ hdeterminant
  · exact minor_nonneg_of_entryBounds (by norm_num) (hdiagonal 0) (hdiagonal 1)
      (hoffDiagonal 0 1 (by decide))
  · exact minor_nonneg_of_entryBounds (by norm_num) (hdiagonal 0) (hdiagonal 2)
      (hoffDiagonal 0 2 (by decide))
  · exact minor_nonneg_of_entryBounds (by norm_num) (hdiagonal 1) (hdiagonal 2)
      (hoffDiagonal 1 2 (by decide))

/-- **THE ONE NAMED HYPOTHESIS.**  Every design in the tube has a rainbow triple whose gap
determinant is nonnegative.  This is a single scalar polynomial sign per design, and the
neighbourhood residual FOLLOWS FROM it.

[Only that direction is proved.  The converse — that covering in the tube forces this
witness — needs "no direction-repeating triple dominates in the tube", which is MEASURED
(their `lambda_min` stays near `−0.99` throughout) and is not a theorem here.  The tube's
weight condition is load-bearing: with radius at most `1/16` it pins `t_min > 1/16`, and
the tie locus's slack constant degenerates like `Theta(t_min)`.] -/
def SplitSevenTubeDeterminantWitness (radius : ℝ) : Prop :=
  ∀ design : WeightedDesign 7 3,
    (∀ (atomIndex : Fin 7) (coord : Fin 3), |design.atom atomIndex coord
        - splitSevenDesign.atom atomIndex coord| < radius) →
    (∀ atomIndex : Fin 7, |design.weight atomIndex
        - splitSevenDesign.weight atomIndex| < radius) →
    ∃ tripleIndex : Fin 20,
      0 ≤ (subsetSum design (rainbowSevenTriple tripleIndex) - 1).det

/-- **THE RESIDUAL, REDUCED.**  `SplitSevenNeighbourhoodCovering` follows from the
determinant witness at any radius up to `1/16`. -/
theorem splitSevenNeighbourhoodCovering_of_determinantWitness (radius : ℝ)
    (hradiusPos : 0 < radius) (hradiusSmall : radius ≤ 1 / 16)
    (hwitness : SplitSevenTubeDeterminantWitness radius) :
    SplitSevenNeighbourhoodCovering := by
  refine ⟨radius, hradiusPos, fun design hatoms hweights => ?_⟩
  obtain ⟨tripleIndex, hdeterminant⟩ := hwitness design hatoms hweights
  exact ⟨rainbowSevenTriple tripleIndex, rainbowSevenTriple_card tripleIndex,
    rainbowSeven_dominates_of_tube_of_determinant design tripleIndex radius hradiusPos.le
      hradiusSmall (fun atomIndex coord => (hatoms atomIndex coord).le) hdeterminant⟩

/-- **THE REMAINDER IS AN IDENTITY, NOT AN ESTIMATE.**  At a nearby design the tie form of
a rainbow triple at its own frozen probe equals the tie-form VELOCITY of the displacement
plus an exact sum of squares.  There is nothing to bound: the quadratic term is present
with the right sign, and the expansion terminates.  The identity holds at an arbitrary
design; no tube is needed.

[What it does NOT give is a covering criterion.  This is ONE probe, `v_miss`, while
domination is an all-probe property, so a positive frozen form does not imply a
nonnegative determinant.  MEASURED counterexample inside the shipped tube: at sup-norm
distance `0.0481` a rainbow triple carries linear term `+2.1e-3` and frozen form `+3.9e-3`
with gap determinant `−3.2e-3`, and does not dominate.  The sign of the linear term is
therefore not what stands between the certificate and covering; see the module header.] -/
theorem rainbowSeven_displacement_frozenForm (design : WeightedDesign 7 3)
    (tripleIndex : Fin 20) :
    tetraAtom (rainbowSevenMissedDirection tripleIndex)
        ⬝ᵥ ((subsetSum design (rainbowSevenTriple tripleIndex) - 1)
              *ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex))
      = rainbowSevenVelocityFamily
            (fun atomIndex coord => design.atom atomIndex coord
              - splitSevenDesign.atom atomIndex coord) tripleIndex
        + ∑ atomIndex ∈ rainbowSevenTriple tripleIndex,
            ((fun coord => design.atom atomIndex coord - splitSevenDesign.atom atomIndex coord)
              ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex)) ^ 2 := by
  have hray : rayAtomSum splitSevenDesign
      (fun atomIndex coord => design.atom atomIndex coord - splitSevenDesign.atom atomIndex coord)
      (rainbowSevenTriple tripleIndex) 1
      = subsetSum design (rainbowSevenTriple tripleIndex) := by
    rw [rayAtomSum, subsetSum]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    congr 1
    funext coord
    simp
  rw [← hray, rainbowSevenTriple_rayGapForm_missedDirection, rainbowSevenVelocityFamily]
  ring

end Gtz
