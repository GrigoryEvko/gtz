/-
# The rank-two hinge in mass coordinates, and the circuit bound

`RankTwoFourDirectionHinge` — four pairwise non-parallel atoms of a rank-two design
force a strictly dominating pair — is the object branch (iii) of the `(6,3)` stress
trichotomy reduces to.  The previous attack walled at "the missing ingredient is
`rank C <= 3`, and a rank constraint cannot be fed into an entrywise-nonnegativity
argument".  This file removes that wall by changing coordinates: in the coordinates
below the rank constraint is not an extra hypothesis at all, it is the ONLY thing
left, and it enters as a linear DEPENDENCY between atom projectors rather than as a
spectral statement.

## The dictionary

For an atom write `l_c` for its leverage, `t_c` for its weight and put

    atomMass       T_c = t_c * l_c
    atomHeaviness  p_c = max 0 (1 - 1 / l_c)
    unitPairGram   B_cd = <g_c, g_d>^2 / (l_c l_d)

Three identities carry everything, and none of them needs a coordinate frame:

* `sum_atomMass`                       `sum_c T_c = k`      (trace of Parseval)
* `sum_atomMass_mul_atomHeaviness_ge`  `sum_c T_c p_c >= k - 1`
* `sum_atomMass_mul_unitPairGram_eq_one`
      **`sum_c T_c B_jc = 1` at every atom `j`** -- Parseval at the probe `g_j`,
      divided by `l_j`.  This is the identity the whole argument turns on, and it is
      the exact statement that the "corner" heaviness vector `p = B_{j.}` sits on the
      boundary `sum_c T_c p_c = 1`.

`posDef_pair_iff_heaviness_gt_unitPairGram` says the pair `{c,d}` dominates STRICTLY
exactly when `p_c p_d > B_cd` with both atoms heavy, so at rank two a tie is exactly
`p_c p_d <= B_cd` at every pair together with `sum_c T_c p_c = k - 1 = 1`.

## The circuit bound

`sum_mass_mul_heaviness_le_one_of_support_card_le_three` is the engine, and it is
elementary, index-type-generic and design-free.  For ANY nonnegative mass vector whose
support has at most three labels, whose total is two and which reproduces the probe
identity `sum_c mass_c B_jc = 1` on its support,

    sum_c mass_c p_c <= 1.

The proof is two lines of bookkeeping: the probe identity at a pivot, with the pair cap
substituted on the off-diagonal, gives `mass_j (1 - p_j^2) <= 1 - p_j * total`, hence
`mass_j (1 + p_j) <= 1` as soon as `total > 1`; summing THAT over a support of at most
three labels gives `2 + total <= 3`.  The count three is the rank plus one, and it is
where `rank C <= 3` finally acts.

CALIBRATION, so that nobody reads this as a re-proof of a shipped lemma.  Instantiate the
pivot step at the design's OWN mass vector: it returns `t_j (2 l_j - 1) <= 1`, which is
literally `Gtz.weightedLeverage_le_nesterenkoBound_of_isTie`, and the count then returns
only `m >= 3`.  The engine IS the Nesterenko bound.  THE NEW CONTENT IS THAT THE SAME
BOUND APPLIES TO A SECOND ADMISSIBLE MASS VECTOR -- one supported on three atoms -- where
the count returns `2 + total <= 3` instead.

THE CEILING OF THE OLD ROUTE, exactly.  The row-identity plus Cauchy-Schwarz family
proves `sum_c T_c p_c <= sqrt 2` and provably nothing sharper: aggregating the pair caps
against ANY nonnegative weight vector `w` gives only `(sum_c w_c p_c)^2 <= w B w`, and at
`w = T` that reads `total^2 <= 2`.  That is the previous lane's `V <= sqrt 2` on the
nose.  The circuit bound is what reaches `1`, and it reaches it by NOT aggregating.

## What is left, named

A design's own mass vector has full support, and there the count returns only `m >= 3`
-- the circuit bound instantiated at the design itself IS the shipped Nesterenko law and
nothing more.  The bound bites only on a SECOND admissible mass vector supported on at
most three labels, and `RankTwoCircuitReduction` is exactly the statement that one
exists without losing heaviness: a sub-collection of at most three atoms that is itself
a design and is at least as heavy as the whole.  That is Caratheodory for the cone
`{coefficient >= 0 : sum_c coefficient_c g_c g_c^T = I}` in the three-dimensional space
of symmetric two by two matrices, made monotone by writing the design's own coefficient
vector as a CONVEX combination of such subfamilies (every one of them has total mass two,
so the combining weights sum to one) and taking a summand above the average.  Four atom
projectors in a three-dimensional space always carry a linear dependency; that dependency
is the `rank <= 3` input, entering as a Caratheodory reduction rather than as a spectral
hypothesis -- which is why the entrywise-nonnegativity obstruction does not apply to it.

`not_isTie_of_circuitReduction_of_equalityStratum` closes the hinge from that residual
plus one strictness input, `RankTwoEqualityStratum`, which says the equality locus
`sum_c mass_c p_c = 1` of the circuit bound carries no four distinct directions.  Both
residuals are finite and elementary; neither is a rank obstruction.

MEASURED, at exact-rational and eighty-digit precision, outside Lean.  Maximising the
worst pair slack over four-direction designs returns ZERO at every non-parallelism floor
from `0.3` down to `0.001`, and the maximiser always runs into `p_j -> 1`, i.e. into
`t_j -> 0`.  CORRECTION TO A MEASURED CLAIM: the sibling rank-two lane recorded a
floor-proportional optimum (`-0.061` at floor `0.1`, ratio near `-0.65` across three
decades).  That is not reproducible here.  The true supremum is `0` at every floor,
approached at the ZERO-WEIGHT boundary rather than at the parallel one, and never
attained.  On the equality locus itself -- where the heaviness vector must be
`p_c = (1 + nu cos Theta_c)/2` for a single symmetric trace-one matrix -- the optimum at
three directions is INTERIOR (`nu = 0.8236`, `p = (0.9118, 0.3542, 0.3542)`, all three
pairs exactly tight: the corank-one tie family), while at four and five directions the
optimum is pinned to `nu = 1` with `max p_c = 1` exactly.  So the four-direction equality
stratum touches feasibility ONLY at zero weight.  That is a structural explanation of the
sibling lane's "exact tie with third weight `5e-82`": that near-miss is not a numerical
curiosity, it is the equality stratum being pinned to the excluded boundary `t_j = 0`.

THE `nu = 1` HALF IS NOW CLOSED, unconditionally and at every size, by
`not_cornerHeaviness_of_pairCap` in Part 5.  What remains of the equality residual is the
band `nu != 1`, and the same measurement quantifies it.  Imposing `p_c <= 1 - eps` at
every atom -- every design weight held a distance `eps` off the excluded value zero --
and maximising the worst constraint margin over the whole equality stratum returns a
STRICTLY NEGATIVE optimum at every `eps` tested:

    four directions   eps = 0.2, 0.1, 0.05, 0.02, 0.01, 0.004
                      margin = -5.5e-3, -3.7e-3, -2.2e-3, -1.0e-3, -5.2e-4, -2.2e-4
    five directions   margin = -8.6e-3, -6.3e-3, -4.2e-3, -2.2e-3, -1.6e-3, -6.5e-4

so the four-direction equality stratum is infeasible for every positive `eps`, and the
margin vanishes only as `eps -> 0`.  It vanishes SUBLINEARLY, like `eps^0.82` at four
directions and `eps^0.66` at five -- recorded as measured, not as a claimed rate.  The
stratum therefore meets feasibility at exactly one place, the zero-weight boundary, which
is the excluded one.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.TwoByTwo
import Gtz.Design.LeverageBound
import Gtz.Quantitative.ChartHadamard
import Gtz.Quantitative.VolumeSelectionFailure
import Gtz.Reduction.RealVolumeFloor
import Gtz.Certificates.ResidueDissolution
import Gtz.Design.FrameConservation
import Gtz.Quantitative.FlooredSpreadRegion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1: the circuit bound, design-free

The engine.  No design, no rank, no matrices: a nonnegative mass vector on any finite
index type, a symmetric cap matrix with unit diagonal, and a heaviness vector in the
unit interval whose pairwise products are capped.  Support at most three forces the
mass-weighted heaviness under one. -/

/-- **THE CIRCUIT BOUND.**  A nonnegative mass vector of total two, supported on at most
three labels and satisfying the probe identity `sum_c mass_c * cap j c = 1` at each of
its support labels, cannot give the heaviness vector a mass-weighted total above one.

The count three is the only place the size of the ambient space enters, and it enters
through `support.card`, not through any spectral hypothesis. -/
theorem sum_mass_mul_heaviness_le_one_of_support_card_le_three
    {label : Type*} [Fintype label] [DecidableEq label]
    (mass heaviness : label → ℝ) (cap : label → label → ℝ) (support : Finset label)
    (hmassNonneg : ∀ index, 0 ≤ mass index)
    (hmassVanishesOffSupport : ∀ index, index ∉ support → mass index = 0)
    (hmassTotal : ∑ index, mass index = 2)
    (hprobe : ∀ pivot ∈ support, ∑ index, mass index * cap pivot index = 1)
    (hcapDiagonal : ∀ pivot ∈ support, cap pivot pivot = 1)
    (hheavinessNonneg : ∀ index, 0 ≤ heaviness index)
    (hheavinessLeOne : ∀ index, heaviness index ≤ 1)
    (hpairCap : ∀ pivot index, pivot ≠ index →
      heaviness pivot * heaviness index ≤ cap pivot index)
    (hsupportSmall : (support.card : ℝ) ≤ 3) :
    ∑ index, mass index * heaviness index ≤ 1 := by
  classical
  by_contra hexceeds
  push Not at hexceeds
  set total := ∑ index, mass index * heaviness index with htotalDef
  -- The pivot step: the probe identity with the pair cap substituted off the diagonal.
  have hpivotBound : ∀ pivot ∈ support, mass pivot * (1 + heaviness pivot) ≤ 1 := by
    intro pivot hpivotMem
    have hcapSplit : mass pivot * cap pivot pivot
        + ∑ index ∈ Finset.univ.erase pivot, mass index * cap pivot index = 1 := by
      rw [Finset.add_sum_erase _ (fun index => mass index * cap pivot index)
        (Finset.mem_univ pivot)]
      exact hprobe pivot hpivotMem
    rw [hcapDiagonal pivot hpivotMem] at hcapSplit
    have hoffDiagonal : ∑ index ∈ Finset.univ.erase pivot,
          mass index * (heaviness pivot * heaviness index)
        ≤ ∑ index ∈ Finset.univ.erase pivot, mass index * cap pivot index := by
      refine Finset.sum_le_sum fun index hindexMem => ?_
      have hdistinct : pivot ≠ index := fun heq =>
        (Finset.mem_erase.mp hindexMem).1 heq.symm
      exact mul_le_mul_of_nonneg_left (hpairCap pivot index hdistinct) (hmassNonneg index)
    have hsplitTotal : mass pivot * heaviness pivot
        + ∑ index ∈ Finset.univ.erase pivot, mass index * heaviness index
        = ∑ index, mass index * heaviness index :=
      Finset.add_sum_erase _ (fun index => mass index * heaviness index)
        (Finset.mem_univ pivot)
    rw [← htotalDef] at hsplitTotal
    have hpull : ∑ index ∈ Finset.univ.erase pivot,
          mass index * (heaviness pivot * heaviness index)
        = heaviness pivot * ∑ index ∈ Finset.univ.erase pivot,
            mass index * heaviness index := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun index _ => by ring
    rw [hpull] at hoffDiagonal
    have hkey : mass pivot
        + heaviness pivot * (total - mass pivot * heaviness pivot) ≤ 1 := by
      have hrewriteTail : ∑ index ∈ Finset.univ.erase pivot, mass index * heaviness index
          = total - mass pivot * heaviness pivot := by linarith [hsplitTotal]
      rw [hrewriteTail] at hoffDiagonal
      linarith [hoffDiagonal, hcapSplit]
    rcases eq_or_lt_of_le (hheavinessLeOne pivot) with hunit | hbelowOne
    · exfalso
      rw [hunit] at hkey
      linarith [hkey, hexceeds]
    · have hgapPos : 0 < 1 - heaviness pivot := by linarith
      have hfactor : (1 - heaviness pivot) * (mass pivot * (1 + heaviness pivot) - 1) ≤ 0 := by
        nlinarith [hkey, hexceeds, hheavinessNonneg pivot]
      by_contra hbad
      push Not at hbad
      nlinarith [hfactor, hgapPos, hbad]
  -- Summing the pivot step over the support: total mass two plus the heaviness total.
  have hsupportMass : ∑ pivot ∈ support, mass pivot = 2 := by
    rw [Finset.sum_subset (Finset.subset_univ support)
      fun index _ hindexOut => hmassVanishesOffSupport index hindexOut]
    exact hmassTotal
  have hsupportHeavy : ∑ pivot ∈ support, mass pivot * heaviness pivot = total := by
    rw [Finset.sum_subset (Finset.subset_univ support) fun index _ hindexOut => by
      rw [hmassVanishesOffSupport index hindexOut, zero_mul]]
  have hcombined : ∑ pivot ∈ support, mass pivot * (1 + heaviness pivot) = 2 + total := by
    have hregroup : ∀ pivot : label, mass pivot * (1 + heaviness pivot)
        = mass pivot + mass pivot * heaviness pivot := fun pivot => by ring
    rw [Finset.sum_congr rfl fun pivot _ => hregroup pivot, Finset.sum_add_distrib,
      hsupportMass, hsupportHeavy]
  have hcardBound : ∑ pivot ∈ support, mass pivot * (1 + heaviness pivot)
      ≤ (support.card : ℝ) := by
    calc ∑ pivot ∈ support, mass pivot * (1 + heaviness pivot)
        ≤ ∑ _pivot ∈ support, (1 : ℝ) := Finset.sum_le_sum hpivotBound
      _ = (support.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcombined] at hcardBound
  linarith [hcardBound, hsupportSmall, hexceeds]

/-! ## Part 2: the mass coordinates of a design -/

/-- The **mass** of an atom: its weight times its leverage.  The masses total the rank
(`sum_atomMass`), so at rank two they total two. -/
def atomMass (D : WeightedDesign m k) (label : Fin m) : ℝ :=
  D.weight label * leverageOf (D.atom label)

/-- The **heaviness** of an atom: `1 - 1 / l`, clipped below at zero.  It lies in `[0,1)`
for every atom of positive leverage, and it is zero exactly on the atoms that are not
strictly heavy. -/
noncomputable def atomHeaviness (D : WeightedDesign m k) (label : Fin m) : ℝ :=
  if leverageOf (D.atom label) ≤ 1 then 0 else 1 - (leverageOf (D.atom label))⁻¹

/-- The **unit pair Gram**: the squared pairing of two atoms, normalised by both
leverages.  At rank two it is `cos^2` of the angle between the two atom directions, so
it vanishes exactly on orthogonal pairs and equals one exactly on parallel ones. -/
noncomputable def unitPairGram (D : WeightedDesign m k) (pivotLabel partnerLabel : Fin m) : ℝ :=
  (D.atom pivotLabel ⬝ᵥ D.atom partnerLabel) ^ 2
    / (leverageOf (D.atom pivotLabel) * leverageOf (D.atom partnerLabel))

theorem atomMass_nonneg (D : WeightedDesign m k) (label : Fin m) : 0 ≤ atomMass D label :=
  mul_nonneg (D.weight_pos label).le (leverageOf_nonneg _)

theorem atomHeaviness_nonneg (D : WeightedDesign m k) (label : Fin m) :
    0 ≤ atomHeaviness D label := by
  rw [atomHeaviness]
  split
  · exact le_refl 0
  · rename_i hheavy
    push Not at hheavy
    have hpos : (0 : ℝ) < leverageOf (D.atom label) := lt_trans zero_lt_one hheavy
    have hinvLt : (leverageOf (D.atom label))⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      exact Or.inr hheavy
    linarith

theorem atomHeaviness_le_one (D : WeightedDesign m k) (label : Fin m) :
    atomHeaviness D label ≤ 1 := by
  rw [atomHeaviness]
  split
  · norm_num
  · rename_i hheavy
    push Not at hheavy
    have hpos : (0 : ℝ) < leverageOf (D.atom label) := lt_trans zero_lt_one hheavy
    have hinvNonneg : (0 : ℝ) ≤ (leverageOf (D.atom label))⁻¹ := (inv_pos.mpr hpos).le
    linarith

/-- The heaviness of an atom is STRICTLY below one: the reciprocal leverage is positive
whenever the atom is heavy.  This is exactly the statement that the atom's weight is
positive, and it is the hypothesis the circuit bound's equality analysis consumes. -/
theorem atomHeaviness_lt_one (D : WeightedDesign m k) (label : Fin m) :
    atomHeaviness D label < 1 := by
  rw [atomHeaviness]
  split
  · norm_num
  · rename_i hheavy
    push Not at hheavy
    have hpos : (0 : ℝ) < leverageOf (D.atom label) := lt_trans zero_lt_one hheavy
    have hinvPos : (0 : ℝ) < (leverageOf (D.atom label))⁻¹ := inv_pos.mpr hpos
    linarith

/-- **The masses total the rank.**  This is the trace of Parseval. -/
theorem sum_atomMass (D : WeightedDesign m k) : ∑ label, atomMass D label = (k : ℝ) :=
  sum_weighted_leverage D

/-- **The mass-weighted heaviness is at least `k - 1`.**  Clipping the heaviness below at
zero only raises the total, and unclipped the total is exactly the excess budget. -/
theorem sum_atomMass_mul_atomHeaviness_ge (D : WeightedDesign m k) :
    (k : ℝ) - 1 ≤ ∑ label, atomMass D label * atomHeaviness D label := by
  have htermwise : ∀ label : Fin m,
      D.weight label * (leverageOf (D.atom label) - 1)
        ≤ atomMass D label * atomHeaviness D label := by
    intro label
    rw [atomMass, atomHeaviness]
    split
    · rename_i hlight
      have hweightPos := D.weight_pos label
      nlinarith [hlight, hweightPos]
    · rename_i hheavy
      push Not at hheavy
      have hpos : (0 : ℝ) < leverageOf (D.atom label) := lt_trans zero_lt_one hheavy
      have hcancel : D.weight label * leverageOf (D.atom label)
            * (1 - (leverageOf (D.atom label))⁻¹)
          = D.weight label * (leverageOf (D.atom label) - 1) := by
        field_simp
      linarith [hcancel]
  calc (k : ℝ) - 1 = ∑ label, D.weight label * (leverageOf (D.atom label) - 1) :=
        (sum_weight_mul_leverage_sub_one D).symm
    _ ≤ ∑ label, atomMass D label * atomHeaviness D label :=
        Finset.sum_le_sum fun label _ => htermwise label

/-- The unit pair Gram is nonnegative. -/
theorem unitPairGram_nonneg (D : WeightedDesign m k) (pivotLabel partnerLabel : Fin m) :
    0 ≤ unitPairGram D pivotLabel partnerLabel :=
  div_nonneg (sq_nonneg _) (mul_nonneg (leverageOf_nonneg _) (leverageOf_nonneg _))

/-- The unit pair Gram is one on the diagonal at every nonzero atom. -/
theorem unitPairGram_self (D : WeightedDesign m k) {pivotLabel : Fin m}
    (hnonzero : D.atom pivotLabel ≠ 0) : unitPairGram D pivotLabel pivotLabel = 1 := by
  have hleveragePos : 0 < leverageOf (D.atom pivotLabel) :=
    lt_of_le_of_ne (leverageOf_nonneg _) fun heq =>
      hnonzero (eq_zero_of_leverageOf_eq_zero heq.symm)
  rw [unitPairGram, ← leverageOf_eq_dotProduct]
  field_simp

/-- **THE PROBE IDENTITY -- the identity the whole reduction turns on.**  The masses
average the unit pair Gram against any fixed nonzero atom to exactly one, at every rank
and every size.  It is Parseval at the probe `g_j` divided by that atom's leverage, and
it says the "corner" heaviness vector `p = B_{j.}` sits exactly on the boundary
`sum_c T_c p_c = 1` that a rank-two tie has to occupy. -/
theorem sum_atomMass_mul_unitPairGram_eq_one (D : WeightedDesign m k) {pivotLabel : Fin m}
    (hnonzero : D.atom pivotLabel ≠ 0) :
    ∑ partnerLabel, atomMass D partnerLabel * unitPairGram D pivotLabel partnerLabel = 1 := by
  have hleveragePos : 0 < leverageOf (D.atom pivotLabel) :=
    lt_of_le_of_ne (leverageOf_nonneg _) fun heq =>
      hnonzero (eq_zero_of_leverageOf_eq_zero heq.symm)
  have htermwise : ∀ partnerLabel : Fin m,
      atomMass D partnerLabel * unitPairGram D pivotLabel partnerLabel
        = D.weight partnerLabel * (D.atom partnerLabel ⬝ᵥ D.atom pivotLabel) ^ 2
            / leverageOf (D.atom pivotLabel) := by
    intro partnerLabel
    rcases eq_or_lt_of_le (leverageOf_nonneg (D.atom partnerLabel)) with hzero | hpartnerPos
    · have hatomZero : D.atom partnerLabel = 0 := eq_zero_of_leverageOf_eq_zero hzero.symm
      have hleverageZero : leverageOf (D.atom partnerLabel) = 0 := hzero.symm
      rw [atomMass, unitPairGram, hleverageZero, hatomZero]
      simp
    · rw [atomMass, unitPairGram,
        dotProduct_comm (D.atom partnerLabel) (D.atom pivotLabel)]
      field_simp
  rw [Finset.sum_congr rfl fun partnerLabel _ => htermwise partnerLabel,
    ← Finset.sum_div, ← dotProduct_self_eq_sum_weight_mul_sq D (D.atom pivotLabel),
    ← leverageOf_eq_dotProduct]
  exact div_self (ne_of_gt hleveragePos)

/-! ### The same identities for a SUB-DESIGN

The circuit bound consumes a second admissible mass vector, and the only thing that
makes a coefficient vector admissible is that it reproduces Parseval.  Both identities
above therefore hold verbatim for any such vector, in particular for one supported on
three atoms -- which is what the Caratheodory residual produces. -/

/-- Parseval as a quadratic form, for an arbitrary reproducing coefficient vector.
The design's own weights are the case `coefficient = D.weight`. -/
theorem dotProduct_self_eq_sum_coefficient_mul_sq (D : WeightedDesign m k)
    (coefficient : Fin m → ℝ)
    (hreproduces : ∑ label, coefficient label • atomMatrix (D.atom label) = 1)
    (probe : Fin k → ℝ) :
    probe ⬝ᵥ probe = ∑ label, coefficient label * (D.atom label ⬝ᵥ probe) ^ 2 := by
  have hidentity : probe ⬝ᵥ ((1 : Matrix (Fin k) (Fin k) ℝ) *ᵥ probe) = probe ⬝ᵥ probe := by
    rw [Matrix.one_mulVec]
  rw [← hidentity, ← hreproduces, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]

/-- The masses of a reproducing coefficient vector total the rank. -/
theorem sum_coefficient_mul_leverage (D : WeightedDesign m k) (coefficient : Fin m → ℝ)
    (hreproduces : ∑ label, coefficient label • atomMatrix (D.atom label) = 1) :
    ∑ label, coefficient label * leverageOf (D.atom label) = (k : ℝ) := by
  have htrace := congrArg Matrix.trace hreproduces
  rw [Matrix.trace_sum, Matrix.trace_one, Fintype.card_fin] at htrace
  rw [← htrace]
  exact Finset.sum_congr rfl fun label _ => by
    rw [Matrix.trace_smul, trace_atomMatrix, smul_eq_mul]

/-- **The probe identity for a sub-design.**  Any reproducing coefficient vector averages
the unit pair Gram against a fixed nonzero atom to exactly one -- the atom need not carry
any of that coefficient vector's own mass. -/
theorem sum_coefficientMass_mul_unitPairGram_eq_one (D : WeightedDesign m k)
    (coefficient : Fin m → ℝ)
    (hreproduces : ∑ label, coefficient label • atomMatrix (D.atom label) = 1)
    {pivotLabel : Fin m} (hnonzero : D.atom pivotLabel ≠ 0) :
    ∑ partnerLabel, (coefficient partnerLabel * leverageOf (D.atom partnerLabel))
      * unitPairGram D pivotLabel partnerLabel = 1 := by
  have hleveragePos : 0 < leverageOf (D.atom pivotLabel) :=
    lt_of_le_of_ne (leverageOf_nonneg _) fun heq =>
      hnonzero (eq_zero_of_leverageOf_eq_zero heq.symm)
  have htermwise : ∀ partnerLabel : Fin m,
      (coefficient partnerLabel * leverageOf (D.atom partnerLabel))
          * unitPairGram D pivotLabel partnerLabel
        = coefficient partnerLabel * (D.atom partnerLabel ⬝ᵥ D.atom pivotLabel) ^ 2
            / leverageOf (D.atom pivotLabel) := by
    intro partnerLabel
    rcases eq_or_lt_of_le (leverageOf_nonneg (D.atom partnerLabel)) with hzero | hpartnerPos
    · have hatomZero : D.atom partnerLabel = 0 := eq_zero_of_leverageOf_eq_zero hzero.symm
      have hleverageZero : leverageOf (D.atom partnerLabel) = 0 := hzero.symm
      rw [unitPairGram, hleverageZero, hatomZero]
      simp
    · rw [unitPairGram, dotProduct_comm (D.atom partnerLabel) (D.atom pivotLabel)]
      field_simp
  rw [Finset.sum_congr rfl fun partnerLabel _ => htermwise partnerLabel,
    ← Finset.sum_div,
    ← dotProduct_self_eq_sum_coefficient_mul_sq D coefficient hreproduces (D.atom pivotLabel),
    ← leverageOf_eq_dotProduct]
  exact div_self (ne_of_gt hleveragePos)

/-! ## Part 3: the rank-two domination criterion in mass coordinates -/

/-- The gap matrix of a pair is symmetric.  Restated here (the sibling rank-two lane
proves the same statement under the name `transpose_pairGap`) so that nothing in this
file depends on an unlanded module. -/
theorem pairGap_transpose_eq (D : WeightedDesign m k) (pivotLabel partnerLabel : Fin m) :
    (subsetSum D {pivotLabel, partnerLabel} - 1)ᵀ
      = subsetSum D {pivotLabel, partnerLabel} - 1 := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum, Matrix.transpose_sum]
  refine congrArg (fun summed => summed - (1 : Matrix (Fin k) (Fin k) ℝ)) ?_
  refine Finset.sum_congr rfl fun label _ => ?_
  ext rowIndex colIndex
  simp [atomMatrix, Matrix.vecMulVec_apply, mul_comm]

/-- **A heavy pair whose leverage excesses beat their squared pairing dominates
strictly.**  Trace positivity comes from heaviness, determinant positivity is the
hypothesis, and at rank two those two are the whole positive-definiteness test. -/
theorem posDef_pairGap_of_excessProduct_gt (D : WeightedDesign m 2)
    {pivotLabel partnerLabel : Fin m} (hdistinct : pivotLabel ≠ partnerLabel)
    (hpivotHeavy : 1 < leverageOf (D.atom pivotLabel))
    (hpartnerHeavy : 1 < leverageOf (D.atom partnerLabel))
    (hexcess : (D.atom pivotLabel ⬝ᵥ D.atom partnerLabel) ^ 2
      < (leverageOf (D.atom pivotLabel) - 1) * (leverageOf (D.atom partnerLabel) - 1)) :
    (subsetSum D {pivotLabel, partnerLabel} - 1).PosDef := by
  have hsymmetric := pairGap_transpose_eq D pivotLabel partnerLabel
  have hentries : (subsetSum D {pivotLabel, partnerLabel} - 1) 0 0
        = leverageOf (D.atom pivotLabel) + leverageOf (D.atom partnerLabel)
          - (D.atom pivotLabel 1 ^ 2 + D.atom partnerLabel 1 ^ 2) - 1
      ∧ (subsetSum D {pivotLabel, partnerLabel} - 1) 1 1
        = D.atom pivotLabel 1 ^ 2 + D.atom partnerLabel 1 ^ 2 - 1 := by
    rw [subsetSum_pair D hdistinct]
    constructor
    · simp only [Matrix.sub_apply, Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply,
        leverageOf, Fin.sum_univ_two, Matrix.one_apply, Fin.isValue]
      norm_num
      ring
    · simp only [Matrix.sub_apply, Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply,
        Matrix.one_apply, Fin.isValue]
      norm_num
      ring
  have htracePos : 0 < (subsetSum D {pivotLabel, partnerLabel} - 1) 0 0
      + (subsetSum D {pivotLabel, partnerLabel} - 1) 1 1 := by
    rw [hentries.1, hentries.2]; linarith
  have hdetValue : (subsetSum D {pivotLabel, partnerLabel} - 1).det
      = (leverageOf (D.atom pivotLabel) - 1) * (leverageOf (D.atom partnerLabel) - 1)
        - (D.atom pivotLabel ⬝ᵥ D.atom partnerLabel) ^ 2 := by
    rw [subsetSum_pair D hdistinct, Matrix.det_fin_two]
    simp only [Matrix.sub_apply, Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply,
      leverageOf, dotProduct, Fin.sum_univ_two, Matrix.one_apply, Fin.isValue]
    norm_num
    ring
  have hoffDiagonal : (subsetSum D {pivotLabel, partnerLabel} - 1) 1 0
      = (subsetSum D {pivotLabel, partnerLabel} - 1) 0 1 := by
    have hentry := congrFun (congrFun hsymmetric 0) 1
    simpa [Matrix.transpose_apply] using hentry
  have hminorEq : (subsetSum D {pivotLabel, partnerLabel} - 1) 0 0
        * (subsetSum D {pivotLabel, partnerLabel} - 1) 1 1
      - (subsetSum D {pivotLabel, partnerLabel} - 1) 0 1 ^ 2
      = (subsetSum D {pivotLabel, partnerLabel} - 1).det := by
    rw [Matrix.det_fin_two, hoffDiagonal]; ring
  have hposSemidef : (subsetSum D {pivotLabel, partnerLabel} - 1).PosSemidef :=
    (posSemidef_two_iff_of_trace_pos hsymmetric htracePos).mpr (by
      rw [hminorEq, hdetValue]; linarith)
  exact hposSemidef.posDef_iff_det_ne_zero.mpr (by rw [hdetValue]; linarith)

/-- **A rank-two tie caps every pair of heavinesses by the unit pair Gram.**  On a pair
where either atom fails to be strictly heavy the cap is free, because the heaviness is
clipped to zero there; on a heavy pair it is the contrapositive of
`posDef_pairGap_of_excessProduct_gt`, divided by the two leverages. -/
theorem atomHeaviness_mul_le_unitPairGram_of_isTie (D : WeightedDesign m 2) (htie : IsTie D)
    (pivotLabel partnerLabel : Fin m) (hdistinct : pivotLabel ≠ partnerLabel) :
    atomHeaviness D pivotLabel * atomHeaviness D partnerLabel
      ≤ unitPairGram D pivotLabel partnerLabel := by
  by_cases hpivotLight : leverageOf (D.atom pivotLabel) ≤ 1
  · simp only [atomHeaviness, if_pos hpivotLight, zero_mul]
    exact unitPairGram_nonneg D pivotLabel partnerLabel
  by_cases hpartnerLight : leverageOf (D.atom partnerLabel) ≤ 1
  · have hzeroFactor : atomHeaviness D partnerLabel = 0 := by
      simp only [atomHeaviness, if_pos hpartnerLight]
    rw [hzeroFactor, mul_zero]
    exact unitPairGram_nonneg D pivotLabel partnerLabel
  push Not at hpivotLight hpartnerLight
  have hpivotPos : (0 : ℝ) < leverageOf (D.atom pivotLabel) := lt_trans zero_lt_one hpivotLight
  have hpartnerPos : (0 : ℝ) < leverageOf (D.atom partnerLabel) :=
    lt_trans zero_lt_one hpartnerLight
  have hnotStrict : ¬ (subsetSum D {pivotLabel, partnerLabel} - 1).PosDef :=
    htie.2 {pivotLabel, partnerLabel} (Finset.card_pair hdistinct)
  have hexcessCap : (leverageOf (D.atom pivotLabel) - 1)
      * (leverageOf (D.atom partnerLabel) - 1)
      ≤ (D.atom pivotLabel ⬝ᵥ D.atom partnerLabel) ^ 2 := by
    by_contra hviolated
    push Not at hviolated
    exact hnotStrict
      (posDef_pairGap_of_excessProduct_gt D hdistinct hpivotLight hpartnerLight hviolated)
  have hdenomPos : 0 < leverageOf (D.atom pivotLabel) * leverageOf (D.atom partnerLabel) :=
    mul_pos hpivotPos hpartnerPos
  have hgapForm : unitPairGram D pivotLabel partnerLabel
        - (1 - (leverageOf (D.atom pivotLabel))⁻¹)
          * (1 - (leverageOf (D.atom partnerLabel))⁻¹)
      = ((D.atom pivotLabel ⬝ᵥ D.atom partnerLabel) ^ 2
          - (leverageOf (D.atom pivotLabel) - 1)
            * (leverageOf (D.atom partnerLabel) - 1))
        / (leverageOf (D.atom pivotLabel) * leverageOf (D.atom partnerLabel)) := by
    rw [unitPairGram]
    field_simp
  have hquotientNonneg : 0 ≤ ((D.atom pivotLabel ⬝ᵥ D.atom partnerLabel) ^ 2
      - (leverageOf (D.atom pivotLabel) - 1) * (leverageOf (D.atom partnerLabel) - 1))
      / (leverageOf (D.atom pivotLabel) * leverageOf (D.atom partnerLabel)) :=
    div_nonneg (by linarith [hexcessCap]) hdenomPos.le
  simp only [atomHeaviness, if_neg (not_le.mpr hpivotLight), if_neg (not_le.mpr hpartnerLight)]
  linarith [hgapForm, hquotientNonneg]

/-! ## Part 5: the equality stratum at a CORNER -- closed, unconditionally

The circuit bound's equality locus forces the heaviness vector to be orthogonal to every
projector dependency, hence to be `p_c = g_c R g_c / l_c` for a single symmetric
trace-one matrix `R`.  Writing `R`'s eigenvalues as `(1 + nu)/2` and `(1 - nu)/2`, the
extreme case `nu = 1` is `R = f f^T` for a unit direction `f` -- the CORNER heaviness
vector `p_c = <g_c, f>^2 / l_c`, which is exactly the vector the probe identity
`sum_atomMass_mul_unitPairGram_eq_one` places on the boundary, and exactly the case the
numerics pin the four-direction equality stratum to.

`not_cornerHeaviness_of_pairCap` kills it outright: NO rank-two design carries a corner
heaviness vector together with the pair cap, at any size and any number of directions.

THE MECHANISM, and it is a moment argument, not a rank argument.  Put
`X_c = sqrt(t_c) <g_c, f>` and `Y_c = sqrt(t_c) <g_c, f-perp>`.  Parseval at `f`, at
`f-perp`, and between them says exactly

    sum_c X_c^2 = 1,    sum_c Y_c^2 = 1,    sum_c X_c Y_c = 0

-- the design contributes nothing else.  The corner condition makes `p_c < 1` equivalent
to `Y_c != 0`, and turns the pair cap into `Y_c Y_d (Y_c Y_d + 2 X_c X_d) >= 0`.  Split
the labels by the sign of `X_c Y_c`; with `a`, `b` the along-masses and `p`, `q` the
across-masses of the two sides and `mu` their shared cross moment, the cap gives
`mu^2 >= 2 a b` while Cauchy-Schwarz gives `mu^2 <= a p` and `mu^2 <= b q`.  Hence
`2 b <= p` and `2 a <= q`, so `p + q >= 2 (a + b) = 2`, against `p + q <= 1`.

Everything below is phrased in squared moments, so no square root ever appears. -/

/-- The atom matrix's quadratic form, polarised. -/
theorem dotProduct_atomMatrix_mulVec_pair {rank : ℕ}
    (vector probeLeft probeRight : Fin rank → ℝ) :
    probeLeft ⬝ᵥ (atomMatrix vector *ᵥ probeRight)
      = (vector ⬝ᵥ probeLeft) * (vector ⬝ᵥ probeRight) := by
  have hrow : ∀ index : Fin rank, (atomMatrix vector *ᵥ probeRight) index
      = vector index * (vector ⬝ᵥ probeRight) := by
    intro index
    simp only [atomMatrix, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun other _ => by ring
  simp only [dotProduct, hrow]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun index _ => by ring

/-- **Parseval, polarised.**  The pairing of two probes is the weighted average of the
product of their atom projections; the diagonal case is the shipped
`Gtz.dotProduct_self_eq_sum_weight_mul_sq`. -/
theorem dotProduct_eq_sum_weight_mul_atomPair (D : WeightedDesign m k)
    (probeLeft probeRight : Fin k → ℝ) :
    probeLeft ⬝ᵥ probeRight
      = ∑ label, D.weight label
          * ((D.atom label ⬝ᵥ probeLeft) * (D.atom label ⬝ᵥ probeRight)) := by
  have hidentity : probeLeft ⬝ᵥ ((1 : Matrix (Fin k) (Fin k) ℝ) *ᵥ probeRight)
      = probeLeft ⬝ᵥ probeRight := by rw [Matrix.one_mulVec]
  rw [← hidentity, ← D.isParseval, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec_pair]

/-- **THE MOMENT CONTRADICTION, design-free.**  Three moment sequences on any finite index
type -- two nonnegative with unit totals, and one whose square is their product and whose
total vanishes -- cannot satisfy the cross cap once the vanishing locus of the cross
moment carries no along-mass.

`hcrossCap` is the pair cap after the sign split; `hzeroCross` is what the corner
condition supplies.  No rank, no matrices, no square roots. -/
theorem not_forall_crossCap_of_unitMoments
    {label : Type*} [Fintype label] [DecidableEq label]
    (alongSq acrossSq crossMoment : label → ℝ)
    (halongNonneg : ∀ index, 0 ≤ alongSq index)
    (hacrossNonneg : ∀ index, 0 ≤ acrossSq index)
    (hgeometricMean : ∀ index, crossMoment index ^ 2 = alongSq index * acrossSq index)
    (halongTotal : ∑ index, alongSq index = 1)
    (hacrossTotal : ∑ index, acrossSq index = 1)
    (hcrossTotal : ∑ index, crossMoment index = 0)
    (hzeroCross : ∀ index, crossMoment index = 0 → alongSq index = 0)
    (hcrossCap : ∀ first second : label, 0 < crossMoment first → crossMoment second < 0 →
      2 * (alongSq first * alongSq second)
        ≤ crossMoment first * (- crossMoment second)) :
    False := by
  classical
  set positivePart := Finset.univ.filter (fun index => 0 < crossMoment index) with hpositiveDef
  set negativePart := Finset.univ.filter (fun index => crossMoment index < 0) with hnegativeDef
  have hdisjoint : Disjoint positivePart negativePart := by
    rw [Finset.disjoint_left]
    intro index hinPositive hinNegative
    simp only [hpositiveDef, hnegativeDef, Finset.mem_filter] at hinPositive hinNegative
    linarith [hinPositive.2, hinNegative.2]
  have hzeroOutside : ∀ index : label, index ∉ positivePart ∪ negativePart →
      crossMoment index = 0 := by
    intro index hout
    simp only [hpositiveDef, hnegativeDef, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, not_or, not_lt] at hout
    exact le_antisymm hout.1 hout.2
  have halongSplit : (∑ index ∈ positivePart, alongSq index)
      + ∑ index ∈ negativePart, alongSq index = 1 := by
    rw [← Finset.sum_union hdisjoint,
      Finset.sum_subset (Finset.subset_univ (positivePart ∪ negativePart))
        (fun index _ hout => hzeroCross index (hzeroOutside index hout)), halongTotal]
  have hcrossSplit : (∑ index ∈ positivePart, crossMoment index)
      + ∑ index ∈ negativePart, crossMoment index = 0 := by
    rw [← Finset.sum_union hdisjoint,
      Finset.sum_subset (Finset.subset_univ (positivePart ∪ negativePart))
        (fun index _ hout => hzeroOutside index hout), hcrossTotal]
  have hacrossBound : (∑ index ∈ positivePart, acrossSq index)
      + ∑ index ∈ negativePart, acrossSq index ≤ 1 := by
    rw [← Finset.sum_union hdisjoint, ← hacrossTotal]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun index _ _ => hacrossNonneg index
  have hcauchyPositive : (∑ index ∈ positivePart, crossMoment index) ^ 2
      ≤ (∑ index ∈ positivePart, alongSq index) * ∑ index ∈ positivePart, acrossSq index :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul positivePart
      (fun index _ => halongNonneg index) (fun index _ => hacrossNonneg index)
      (fun index _ => le_of_eq (hgeometricMean index))
  have hcauchyNegative : (∑ index ∈ negativePart, crossMoment index) ^ 2
      ≤ (∑ index ∈ negativePart, alongSq index) * ∑ index ∈ negativePart, acrossSq index :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul negativePart
      (fun index _ => halongNonneg index) (fun index _ => hacrossNonneg index)
      (fun index _ => le_of_eq (hgeometricMean index))
  -- the cap, aggregated over the two sides
  have hproductBound :
      2 * ((∑ index ∈ positivePart, alongSq index) * ∑ index ∈ negativePart, alongSq index)
        ≤ - ((∑ index ∈ positivePart, crossMoment index)
              * ∑ index ∈ negativePart, crossMoment index) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun first hfirst => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun second hsecond => ?_
    simp only [hpositiveDef, hnegativeDef, Finset.mem_filter] at hfirst hsecond
    have hcap := hcrossCap first second hfirst.2 hsecond.2
    linarith [hcap]
  -- the two sides carry the same cross moment up to sign
  have hcrossMirror : (∑ index ∈ negativePart, crossMoment index)
      = - ∑ index ∈ positivePart, crossMoment index := by linarith [hcrossSplit]
  have hkeyLower :
      2 * ((∑ index ∈ positivePart, alongSq index) * ∑ index ∈ negativePart, alongSq index)
        ≤ (∑ index ∈ positivePart, crossMoment index) ^ 2 := by
    rw [hcrossMirror] at hproductBound
    nlinarith [hproductBound]
  have hkeyLowerMirror :
      2 * ((∑ index ∈ positivePart, alongSq index) * ∑ index ∈ negativePart, alongSq index)
        ≤ (∑ index ∈ negativePart, crossMoment index) ^ 2 := by
    rw [hcrossMirror]
    nlinarith [hkeyLower]
  have halongPositiveNonneg : 0 ≤ ∑ index ∈ positivePart, alongSq index :=
    Finset.sum_nonneg fun index _ => halongNonneg index
  have halongNegativeNonneg : 0 ≤ ∑ index ∈ negativePart, alongSq index :=
    Finset.sum_nonneg fun index _ => halongNonneg index
  have hpositiveNegSigns : ∀ index ∈ negativePart, crossMoment index < 0 := by
    intro index hmem
    simp only [hnegativeDef, Finset.mem_filter] at hmem
    exact hmem.2
  have hnegativePosSigns : ∀ index ∈ positivePart, 0 < crossMoment index := by
    intro index hmem
    simp only [hpositiveDef, Finset.mem_filter] at hmem
    exact hmem.2
  -- a vanishing along-mass on one side collapses the other, against the unit total
  have halongPositivePos : 0 < ∑ index ∈ positivePart, alongSq index := by
    rcases lt_or_eq_of_le halongPositiveNonneg with hpos | hzero
    · exact hpos
    · exfalso
      have hcrossSq : (∑ index ∈ positivePart, crossMoment index) ^ 2 ≤ 0 := by
        rw [← hzero, zero_mul] at hcauchyPositive
        exact hcauchyPositive
      have hcrossPositiveZero : (∑ index ∈ positivePart, crossMoment index) = 0 :=
        (pow_eq_zero_iff (n := 2) (by norm_num)).mp (le_antisymm hcrossSq (sq_nonneg _))
      have hcrossNegativeZero : (∑ index ∈ negativePart, crossMoment index) = 0 := by
        linarith [hcrossSplit, hcrossPositiveZero]
      have hallZero := (Finset.sum_eq_zero_iff_of_nonpos
        (fun index hmem => (hpositiveNegSigns index hmem).le)).mp hcrossNegativeZero
      have hnegativeAlongZero : (∑ index ∈ negativePart, alongSq index) = 0 :=
        Finset.sum_eq_zero fun index hmem =>
          absurd (hallZero index hmem) (ne_of_lt (hpositiveNegSigns index hmem))
      linarith [halongSplit, hnegativeAlongZero, hzero]
  have halongNegativePos : 0 < ∑ index ∈ negativePart, alongSq index := by
    rcases lt_or_eq_of_le halongNegativeNonneg with hpos | hzero
    · exact hpos
    · exfalso
      have hcrossSq : (∑ index ∈ negativePart, crossMoment index) ^ 2 ≤ 0 := by
        rw [← hzero, zero_mul] at hcauchyNegative
        exact hcauchyNegative
      have hcrossNegativeZero : (∑ index ∈ negativePart, crossMoment index) = 0 :=
        (pow_eq_zero_iff (n := 2) (by norm_num)).mp (le_antisymm hcrossSq (sq_nonneg _))
      have hcrossPositiveZero : (∑ index ∈ positivePart, crossMoment index) = 0 := by
        linarith [hcrossSplit, hcrossNegativeZero]
      have hallZero := (Finset.sum_eq_zero_iff_of_nonneg
        (fun index hmem => (hnegativePosSigns index hmem).le)).mp hcrossPositiveZero
      have hpositiveAlongZero : (∑ index ∈ positivePart, alongSq index) = 0 :=
        Finset.sum_eq_zero fun index hmem =>
          absurd (hallZero index hmem).symm (ne_of_lt (hnegativePosSigns index hmem))
      linarith [halongSplit, hpositiveAlongZero, hzero]
  -- the two halves of the count
  have hacrossPositiveLower : 2 * (∑ index ∈ negativePart, alongSq index)
      ≤ ∑ index ∈ positivePart, acrossSq index := by
    nlinarith [hkeyLower, hcauchyPositive, halongPositivePos]
  have hacrossNegativeLower : 2 * (∑ index ∈ positivePart, alongSq index)
      ≤ ∑ index ∈ negativePart, acrossSq index := by
    nlinarith [hkeyLowerMirror, hcauchyNegative, halongNegativePos]
  linarith [hacrossBound, hacrossPositiveLower, hacrossNegativeLower, halongSplit]

/-- **THE CORNER EQUALITY STRATUM IS EMPTY.**  No rank-two design carries a CORNER
heaviness vector -- `p_c * l_c = <g_c, f>^2` for a fixed unit direction `f` -- together
with the pair cap that a tie imposes.  Unconditional: no hypothesis on the size, on the
number of distinct directions, or on which pairs are tight.

This closes the `nu = 1` half of `RankTwoEqualityStratum`, which is the half the
numerics pin the four-direction equality stratum to. -/
theorem not_cornerHeaviness_of_pairCap (D : WeightedDesign m 2)
    (alongProbe : Fin 2 → ℝ) (hunitProbe : alongProbe ⬝ᵥ alongProbe = 1)
    (hcorner : ∀ label, atomHeaviness D label * leverageOf (D.atom label)
      = (D.atom label ⬝ᵥ alongProbe) ^ 2)
    (hpairCap : ∀ pivot partner : Fin m, pivot ≠ partner →
      (D.atom pivot ⬝ᵥ alongProbe) ^ 2 * (D.atom partner ⬝ᵥ alongProbe) ^ 2
        ≤ (D.atom pivot ⬝ᵥ D.atom partner) ^ 2) :
    False := by
  classical
  set acrossProbe : Fin 2 → ℝ := ![-(alongProbe 1), alongProbe 0] with hacrossProbeDef
  have hcoordUnit : alongProbe 0 ^ 2 + alongProbe 1 ^ 2 = 1 := by
    have hraw := hunitProbe
    simp only [dotProduct, Fin.sum_univ_two] at hraw
    linear_combination hraw
  have hframeSplit : ∀ leftVector rightVector : Fin 2 → ℝ,
      leftVector ⬝ᵥ rightVector
        = (leftVector ⬝ᵥ alongProbe) * (rightVector ⬝ᵥ alongProbe)
          + (leftVector ⬝ᵥ acrossProbe) * (rightVector ⬝ᵥ acrossProbe) := by
    intro leftVector rightVector
    simp only [hacrossProbeDef, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linear_combination (- (leftVector 0 * rightVector 0 + leftVector 1 * rightVector 1))
      * hcoordUnit
  have hacrossUnit : acrossProbe ⬝ᵥ acrossProbe = 1 := by
    simp only [hacrossProbeDef, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linear_combination hcoordUnit
  have hprobesOrthogonal : alongProbe ⬝ᵥ acrossProbe = 0 := by
    simp only [hacrossProbeDef, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  have hleverageSplit : ∀ label : Fin m, leverageOf (D.atom label)
      = (D.atom label ⬝ᵥ alongProbe) ^ 2 + (D.atom label ⬝ᵥ acrossProbe) ^ 2 := by
    intro label
    rw [leverageOf_eq_dotProduct, hframeSplit (D.atom label) (D.atom label)]
    ring
  -- the across projection never vanishes: that is exactly `atomHeaviness < 1`
  have hacrossNonzero : ∀ label : Fin m, D.atom label ⬝ᵥ acrossProbe = 0 →
      D.atom label ⬝ᵥ alongProbe = 0 := by
    intro label hzeroAcross
    have hlev := hleverageSplit label
    rw [hzeroAcross] at hlev
    have hcornerLabel := hcorner label
    rw [hlev] at hcornerLabel
    have hproduct : (D.atom label ⬝ᵥ alongProbe) ^ 2 * (1 - atomHeaviness D label) = 0 := by
      linear_combination - hcornerLabel
    rcases mul_eq_zero.mp hproduct with hsquareZero | hunitHeaviness
    · exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hsquareZero
    · exact absurd (by linarith [hunitHeaviness] : atomHeaviness D label = 1)
        (ne_of_lt (atomHeaviness_lt_one D label))
  refine not_forall_crossCap_of_unitMoments
    (fun label => D.weight label * (D.atom label ⬝ᵥ alongProbe) ^ 2)
    (fun label => D.weight label * (D.atom label ⬝ᵥ acrossProbe) ^ 2)
    (fun label => D.weight label
      * ((D.atom label ⬝ᵥ alongProbe) * (D.atom label ⬝ᵥ acrossProbe)))
    (fun label => mul_nonneg (D.weight_pos label).le (sq_nonneg _))
    (fun label => mul_nonneg (D.weight_pos label).le (sq_nonneg _))
    (fun label => by ring) ?_ ?_ ?_ ?_ ?_
  · have hparseval := dotProduct_self_eq_sum_weight_mul_sq D alongProbe
    rw [hunitProbe] at hparseval
    exact hparseval.symm
  · have hparseval := dotProduct_self_eq_sum_weight_mul_sq D acrossProbe
    rw [hacrossUnit] at hparseval
    exact hparseval.symm
  · have hparseval := dotProduct_eq_sum_weight_mul_atomPair D alongProbe acrossProbe
    rw [hprobesOrthogonal] at hparseval
    exact hparseval.symm
  · intro label hzeroCross
    have hweightPos := D.weight_pos label
    have hfactorZero : (D.atom label ⬝ᵥ alongProbe) * (D.atom label ⬝ᵥ acrossProbe) = 0 := by
      rcases mul_eq_zero.mp hzeroCross with hweightZero | hfactor
      · exact absurd hweightZero (ne_of_gt hweightPos)
      · exact hfactor
    rcases mul_eq_zero.mp hfactorZero with halongZero | hacrossZero
    · rw [halongZero]; ring
    · rw [hacrossNonzero label hacrossZero]; ring
  · intro firstLabel secondLabel hfirstPos hsecondNeg
    have hweightFirst := D.weight_pos firstLabel
    have hweightSecond := D.weight_pos secondLabel
    have hdistinct : firstLabel ≠ secondLabel := by
      intro heq
      rw [heq] at hfirstPos
      linarith [hfirstPos, hsecondNeg]
    have hcap := hpairCap firstLabel secondLabel hdistinct
    rw [hframeSplit (D.atom firstLabel) (D.atom secondLabel)] at hcap
    -- abbreviations for the two frame products
    have hcapExpanded : 0 ≤ 2 * ((D.atom firstLabel ⬝ᵥ alongProbe)
          * (D.atom secondLabel ⬝ᵥ alongProbe)
          * ((D.atom firstLabel ⬝ᵥ acrossProbe) * (D.atom secondLabel ⬝ᵥ acrossProbe)))
        + ((D.atom firstLabel ⬝ᵥ acrossProbe) * (D.atom secondLabel ⬝ᵥ acrossProbe)) ^ 2 := by
      nlinarith [hcap]
    have hfirstFrameProduct : 0 < (D.atom firstLabel ⬝ᵥ alongProbe)
        * (D.atom firstLabel ⬝ᵥ acrossProbe) := by
      by_contra hnonpos
      push Not at hnonpos
      nlinarith [hfirstPos, mul_nonneg hweightFirst.le (neg_nonneg.mpr hnonpos)]
    have hsecondFrameProduct : (D.atom secondLabel ⬝ᵥ alongProbe)
        * (D.atom secondLabel ⬝ᵥ acrossProbe) < 0 := by
      by_contra hnonneg
      push Not at hnonneg
      nlinarith [hsecondNeg, mul_nonneg hweightSecond.le hnonneg]
    have hcrossNegative : (D.atom firstLabel ⬝ᵥ alongProbe)
          * (D.atom secondLabel ⬝ᵥ alongProbe)
          * ((D.atom firstLabel ⬝ᵥ acrossProbe) * (D.atom secondLabel ⬝ᵥ acrossProbe)) < 0 := by
      nlinarith [mul_neg_of_pos_of_neg hfirstFrameProduct hsecondFrameProduct]
    have halongProduct : 2 * (((D.atom firstLabel ⬝ᵥ alongProbe)
          * (D.atom secondLabel ⬝ᵥ alongProbe)) ^ 2)
        ≤ - ((D.atom firstLabel ⬝ᵥ alongProbe) * (D.atom secondLabel ⬝ᵥ alongProbe)
            * ((D.atom firstLabel ⬝ᵥ acrossProbe) * (D.atom secondLabel ⬝ᵥ acrossProbe))) := by
      nlinarith [hcapExpanded, hcrossNegative,
        mul_nonneg (sq_nonneg ((D.atom firstLabel ⬝ᵥ alongProbe)
          * (D.atom secondLabel ⬝ᵥ alongProbe))) hcapExpanded]
    nlinarith [halongProduct, hweightFirst, hweightSecond,
      mul_pos hweightFirst hweightSecond]

/-! ## Part 4: the composite, and the two named residuals -/

/-- **THE CARATHEODORY RESIDUAL.**  A rank-two design contains a sub-collection of at
most THREE atoms which is itself a design (`hreproduces`) and which is at least as heavy
as the whole (`hmonotone`).

This is Caratheodory for the cone `{coefficient >= 0 : sum_c coefficient_c g_c g_c^T = I}`
inside the three-dimensional space of symmetric two by two matrices, made monotone.  The
plain existence half is classical -- the design's own coefficient vector realises `I` in
the conic hull of the atom projectors, so some at-most-three-element subfamily already
does; the monotone half comes from writing the design's coefficient vector as a CONVEX
combination of such subfamilies (each has total mass `2`, so the combination's weights
sum to one) and picking a summand at least as heavy as the average.

Four projectors in a three-dimensional space always carry a linear dependency; that
dependency is precisely the `rank <= 3` input the previous attack could not feed into an
entrywise-nonnegativity argument, and here it enters as the Caratheodory reduction rather
than as a spectral hypothesis. -/
def RankTwoCircuitReduction : Prop :=
  ∀ (size : ℕ) (D : WeightedDesign size 2) (heaviness : Fin size → ℝ),
    ∃ (subWeight : Fin size → ℝ) (support : Finset (Fin size)),
      (∀ label, 0 ≤ subWeight label)
      ∧ (∀ label, label ∉ support → subWeight label = 0)
      ∧ support.card ≤ 3
      ∧ (∑ label, subWeight label • atomMatrix (D.atom label) = 1)
      ∧ (∑ label, atomMass D label * heaviness label)
          ≤ ∑ label, (subWeight label * leverageOf (D.atom label)) * heaviness label

/-- **THE EQUALITY RESIDUAL.**  The circuit bound is TIGHT: the equilateral rank-two tie
attains `sum_c mass_c p_c = 1` exactly, so the bound alone cannot exclude a tie -- only a
tie with FOUR pairwise non-parallel atoms.  Sliding forces the heaviness vector to be
orthogonal to every projector dependency at equality, i.e. `p_c = (1 + nu cos Theta_c)/2`
for a single symmetric trace-one matrix; this residual says no such vector supports four
distinct directions with every heaviness strictly below one.

THE `nu = 1` HALF IS CLOSED.  `not_cornerHeaviness_of_pairCap` (Part 5) rules out the
corner heaviness vector `p_c l_c = <g_c, f>^2` unconditionally -- at every size, every
number of directions, and with no hypothesis on which pairs are tight.  That is exactly
the half the numerics pin the four-direction stratum to, so what is left of this residual
is the band `nu != 1`, measured strictly infeasible at four or more directions. -/
def RankTwoEqualityStratum : Prop :=
  ∀ (size : ℕ) (D : WeightedDesign size 2) (firstLabel secondLabel thirdLabel
      fourthLabel : Fin size),
    firstLabel ≠ secondLabel → firstLabel ≠ thirdLabel → firstLabel ≠ fourthLabel →
    secondLabel ≠ thirdLabel → secondLabel ≠ fourthLabel → thirdLabel ≠ fourthLabel →
    unitPairGram D firstLabel secondLabel ≠ 1 → unitPairGram D firstLabel thirdLabel ≠ 1 →
    unitPairGram D firstLabel fourthLabel ≠ 1 → unitPairGram D secondLabel thirdLabel ≠ 1 →
    unitPairGram D secondLabel fourthLabel ≠ 1 → unitPairGram D thirdLabel fourthLabel ≠ 1 →
    (∀ pivot partner : Fin size, pivot ≠ partner →
      atomHeaviness D pivot * atomHeaviness D partner ≤ unitPairGram D pivot partner) →
    ∑ label, atomMass D label * atomHeaviness D label ≠ 1

/-- **THE COMPOSITE.**  A rank-two tie whose mass admits a three-label reduction has
mass-weighted heaviness exactly one, and four pairwise non-parallel atoms then contradict
the equality residual.  Both inputs are finite and elementary; neither is a rank
obstruction, and the rank enters only as the count three in the circuit bound. -/
theorem not_isTie_of_circuitReduction_of_equalityStratum
    (hreduction : RankTwoCircuitReduction) (hequality : RankTwoEqualityStratum)
    (D : WeightedDesign m 2)
    (firstLabel secondLabel thirdLabel fourthLabel : Fin m)
    (hone : firstLabel ≠ secondLabel) (htwo : firstLabel ≠ thirdLabel)
    (hthree : firstLabel ≠ fourthLabel) (hfour : secondLabel ≠ thirdLabel)
    (hfive : secondLabel ≠ fourthLabel) (hsix : thirdLabel ≠ fourthLabel)
    (hgramOne : unitPairGram D firstLabel secondLabel ≠ 1)
    (hgramTwo : unitPairGram D firstLabel thirdLabel ≠ 1)
    (hgramThree : unitPairGram D firstLabel fourthLabel ≠ 1)
    (hgramFour : unitPairGram D secondLabel thirdLabel ≠ 1)
    (hgramFive : unitPairGram D secondLabel fourthLabel ≠ 1)
    (hgramSix : unitPairGram D thirdLabel fourthLabel ≠ 1) :
    ¬ IsTie D := by
  intro htie
  have hpairCap : ∀ pivot partner : Fin m, pivot ≠ partner →
      atomHeaviness D pivot * atomHeaviness D partner ≤ unitPairGram D pivot partner :=
    fun pivot partner hdistinct =>
      atomHeaviness_mul_le_unitPairGram_of_isTie D htie pivot partner hdistinct
  obtain ⟨subWeight, support, hsubNonneg, hsubOff, hcard, hreproduces, hmonotone⟩ :=
    hreduction m D (atomHeaviness D)
  classical
  set reducedMass := fun label => subWeight label * leverageOf (D.atom label) with hreducedDef
  -- Drop any zero atom from the support: it carries no mass and has no unit Gram.
  set liveSupport := support.filter (fun label => D.atom label ≠ 0) with hliveDef
  have hmassNonneg : ∀ label, 0 ≤ reducedMass label := fun label =>
    mul_nonneg (hsubNonneg label) (leverageOf_nonneg _)
  have hmassOff : ∀ label, label ∉ liveSupport → reducedMass label = 0 := by
    intro label hout
    rw [hliveDef, Finset.mem_filter] at hout
    push Not at hout
    rw [hreducedDef]
    by_cases hinSupport : label ∈ support
    · have hatomZero : D.atom label = 0 := by
        by_contra hnonzero
        exact hnonzero (hout hinSupport)
      simp [hatomZero, leverageOf]
    · simp [hsubOff label hinSupport]
  have hmassTotal : ∑ label, reducedMass label = 2 := by
    have hrank := sum_coefficient_mul_leverage D subWeight hreproduces
    norm_num at hrank
    exact hrank
  have hliveNonzero : ∀ pivot ∈ liveSupport, D.atom pivot ≠ 0 := by
    intro pivot hpivotMem
    rw [hliveDef, Finset.mem_filter] at hpivotMem
    exact hpivotMem.2
  have hprobe : ∀ pivot ∈ liveSupport,
      ∑ label, reducedMass label * unitPairGram D pivot label = 1 := fun pivot hpivotMem =>
    sum_coefficientMass_mul_unitPairGram_eq_one D subWeight hreproduces
      (hliveNonzero pivot hpivotMem)
  have hcapDiagonal : ∀ pivot ∈ liveSupport, unitPairGram D pivot pivot = 1 :=
    fun pivot hpivotMem => unitPairGram_self D (hliveNonzero pivot hpivotMem)
  have hliveCard : (liveSupport.card : ℝ) ≤ 3 := by
    have hsubset : liveSupport.card ≤ support.card :=
      Finset.card_le_card (by rw [hliveDef]; exact Finset.filter_subset _ _)
    exact_mod_cast le_trans hsubset hcard
  have hdesignTotal : (1 : ℝ) ≤ ∑ label, atomMass D label * atomHeaviness D label := by
    have hexcess := sum_atomMass_mul_atomHeaviness_ge D
    norm_num at hexcess
    exact hexcess
  have hbound : ∑ label, reducedMass label * atomHeaviness D label ≤ 1 :=
    sum_mass_mul_heaviness_le_one_of_support_card_le_three
      reducedMass (atomHeaviness D) (unitPairGram D) liveSupport hmassNonneg hmassOff
      hmassTotal hprobe hcapDiagonal (atomHeaviness_nonneg D) (atomHeaviness_le_one D)
      hpairCap hliveCard
  have hexactlyOne : ∑ label, atomMass D label * atomHeaviness D label = 1 :=
    le_antisymm (le_trans hmonotone hbound) hdesignTotal
  exact hequality m D firstLabel secondLabel thirdLabel fourthLabel hone htwo hthree hfour
    hfive hsix hgramOne hgramTwo hgramThree hgramFour hgramFive hgramSix hpairCap hexactlyOne

end Gtz

