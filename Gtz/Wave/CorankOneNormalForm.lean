/-
# The free-mass split, the null-direction budget, and the corank-one normal form

A tie owns a triple `C0` whose gap `S_{C0} - 1` is positive semidefinite and
singular.  `Gtz/Wave/CorankDecomposition.lean` closes corank three.  Corank one
carries every known tie: exact computation puts the gap corank at `1` at every
weakly dominating triple of `Gtz.tetraDesign`, `Gtz.diamondDesign`,
`Gtz.nonUniformLeverageTieDesign` and `Gtz.sixSplitDiamondDesign`.  This module
lands the algebra of that cell.

## The master identity

Parseval splits the identity across a subset and its complement.  Subtract that
split from the unweighted atom sum of the subset and one matrix identity falls
out, at every size, every rank and every subset:

  `freeMassMatrix D C = (subsetSum D C - 1) + complementMassMatrix D C`

with `freeMassMatrix D C = sum over c in C of (1 - t_c) * g_c g_c^T` and
`complementMassMatrix D C = sum over c off C of t_c * g_c g_c^T`.  The left side
is the free mass of `C`, the exact matrix the tree's free-mass certificate
inverts (`Gtz.HasStrictCertificate`, `Gtz.Design.StressFreeStratum`).  The
middle term is the gap.  The right term is the complement mass.

`Gtz.freeMassMatrix_eq_gap_add_complementMassMatrix` is that identity.  Four
readings follow.

* **The null-direction budget.**  At a direction where the gap form vanishes,
  the free mass and the complement mass agree:
  `sum over c in C of (1 - t_c) (g_c . v)^2 = sum over c off C of t_c (g_c . v)^2`.
  This is `Gtz.nullDirection_budget_identity`.
* **The free mass is positive definite at every weakly dominating subset**
  (`Gtz.freeMassMatrix_posDef_of_dominates`).  The tree carries that clause as a
  HYPOTHESIS inside `Gtz.HasStrictCertificate` and inside `Gtz.NoStressResidual`.
  It is free.
* **The spend identity.**  The certificate spend equals the rank minus the trace
  of the gap in the free-mass metric:
  `budgetSpend D C + trace (freeMass^{-1} * gap) = k`
  (`Gtz.budgetSpend_add_trace_freeMassInv_gap`).  A sum over the complement
  becomes a trace of the gap.  At a `(6,3)` tie the landed
  `Gtz.not_hasStrictCertificate_of_isTie` then reads
  `trace (freeMass^{-1} * gap) <= 2` at every weakly dominating triple.
* **The corank-one normal form.**  When the gap form vanishes exactly on one
  line, the complement mass form is at most the free mass form everywhere, with
  equality exactly on that line.  `Gtz.corankOne_normalForm` packages it.

## The corank-two residue

Two results, both new.

* **Nine of the eighteen mixed triples are free.**  If the gap of `C0` is
  `lam * gapDir gapDir^T` at rank three, then for every `drop` in `C0` and every
  `add` off `C0` the swapped triple `C0 - drop + add` FAILS to dominate
  strictly (`Gtz.not_posDef_swap_of_rankOneGap`).  A direction orthogonal to
  `gapDir` and to `g_add` sees the swapped gap form as `-(g_drop . x)^2`.  So at
  corank two the tie condition on those nine triples carries no information, and
  the corank-two content is the complement triple plus the nine triples that
  share ONE label.  Measured: 40000 sampled corank-two configurations, 360000
  two-shared triples, ZERO strict dominators.
* **The exact threshold.**  If `inner * (1 + lam) < 1 - outer`, the complement
  triple dominates strictly (`Gtz.posDef_compl_of_rankOneGap_of_threshold`).  So
  a corank-two `(6,3)` tie needs `1 - outer <= inner * (1 + lam)`, that is
  `1 - inner - outer <= inner * lam` (`Gtz.rankOneGap_threshold_of_isTie`).  In
  leverage vocabulary `lam = sum over c in C0 of l_c - 3`, and the floor reads
  `1 - outer <= inner * (sum over c in C0 of l_c - 2)`.  That is sharper by
  `2 * inner` than the landed `Gtz.sum_leverage_floor_of_isTie_sixThree`.

**Corank two did NOT fall.**  Measured on 60000 sampled corank-two
configurations, the landed threshold discharges 32 percent of them.  Two sharper
criteria, both unlanded, discharge 63 and 71 percent: the first replaces
`inner * (1 + lam)` by `inner + sum over c in C0 of t_c (l_c - 1)`, the second
compares the smallest eigenvalue of the complement mass with `outer` directly.
Neither reaches 100 percent.  Every survivor of the sharpest of the three loses a
ONE-shared triple, and this module carries no lever on those nine triples.  The
band that survives the second criterion is
`1 - inner - outer <= sum over c in C0 of t_c (l_c - 1) <= 1 - min weight on C0`,
and that interval is nonempty at every weight profile.

## Why the corank-two lever cannot run at `(5,3)`

`Gtz.diamondDesign` is a PRIMITIVE `(5,3)` tie, so no argument may exclude it.
The lever above is `Gtz.posDef_subsetSum_of_outside_share_lt` applied to the
COMPLEMENT of the dominating triple.  Its hypothesis asks the inside share to
stay below `1 - outer` in every direction.

`Gtz.full_inside_share_of_commonOrthogonal` shows that hypothesis fails at once
whenever the complement atoms share an orthogonal direction: Parseval then puts
the whole unit mass on the inside.  At `(5,3)` the complement of a triple has
TWO atoms, and `Gtz.exists_orthogonal_to_pair` produces a common orthogonal
direction for any two vectors of `R^3`.  So
`Gtz.not_insideShareCriterion_fiveThree` refutes the lever at EVERY triple of
EVERY `(5,3)` design, with no hypothesis at all.

At `(6,3)` the complement is a triple, and a triple with a common orthogonal
direction never dominates (`Gtz.not_dominates_of_commonOrthogonal`).  One
hypothesis, `card of the complement = rank`, carries the whole difference.

## The `(5,3)` calibration, measured

Exact rational data at `Gtz.diamondDesign`, all eight weakly dominating triples:
gap corank `1`, gap spectrum `(0, 3/2, 4)` on the four spanning triples through
the spine and `(0, 11/4, 4)` on the four others.  Both sides of the null-direction
budget read `4/5`.  The free mass is positive definite at all eight, with
spectrum `(4/5, 2, 4)` and `(4/5, 3, 4)`.  The spend reads `5/4` and `13/12`, and
the identity `spend = 3 - trace (freeMass^{-1} * gap)` holds at each.  So every
identity of this module holds at the `(5,3)` diamond.  Only the corank-two lever
of section 6 fails there, and section 7 proves it fails.

## The vacuity guard

`Gtz.OnPathRegistryCollapse.elim_primitive_isTie_of_hinge` makes every Prop of
shape `forall D, IsPrimitiveDesign D -> IsTie D -> _` equal to the frontier.  No
statement here has that shape.  Every antecedent below is inhabited:
`Gtz.budget_identity_nonUniformLeverageTieDesign` and
`Gtz.gapNullLine_nonUniformLeverageTieDesign` inhabit the corank-one arm at a
landed `(6,3)` tie, and `Gtz.rankOneGapWitnessDesign` inhabits the corank-two
arm with rational entries.
-/
import Mathlib
import Gtz.Wave.CorankDecomposition
import Gtz.Design.FreeMassBudgetDischarge
import Gtz.Design.ComplementEngine
import Gtz.Design.MarginTransfer
import Gtz.Design.NearPencilTransport
import Gtz.Reduction.MassGapDescent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. The free mass, the complement mass, and the split

The two matrices below are the two halves of the certificate vocabulary.  The
first is verbatim the matrix that `Gtz.HasStrictCertificate` inverts.  The
second is the weighted mass carried by the labels outside the subset. -/

/-- **The free mass of a subset.**  Each selected atom enters with the mass that
its own weight leaves free.  This is the matrix inverted by the second arm of
`Gtz.HasStrictCertificate`. -/
def freeMassMatrix (D : WeightedDesign m k) (C : Finset (Fin m)) :
    Matrix (Fin k) (Fin k) ℝ :=
  ∑ c ∈ C, (1 - D.weight c) • atomMatrix (D.atom c)

/-- **The complement mass of a subset.**  The weighted atom sum of the labels
outside the subset. -/
def complementMassMatrix (D : WeightedDesign m k) (C : Finset (Fin m)) :
    Matrix (Fin k) (Fin k) ℝ :=
  ∑ c ∈ Cᶜ, D.weight c • atomMatrix (D.atom c)

theorem freeMassMatrix_def (D : WeightedDesign m k) (C : Finset (Fin m)) :
    freeMassMatrix D C = ∑ c ∈ C, (1 - D.weight c) • atomMatrix (D.atom c) := rfl

theorem complementMassMatrix_def (D : WeightedDesign m k) (C : Finset (Fin m)) :
    complementMassMatrix D C = ∑ c ∈ Cᶜ, D.weight c • atomMatrix (D.atom c) := rfl

/-- Parseval, split along a subset and its complement. -/
theorem weightedMass_add_complementMassMatrix (D : WeightedDesign m k) (C : Finset (Fin m)) :
    (∑ c ∈ C, D.weight c • atomMatrix (D.atom c)) + complementMassMatrix D C = 1 := by
  classical
  rw [complementMassMatrix, Finset.sum_add_sum_compl, D.isParseval]

/-- **THE MASTER IDENTITY.**  The free mass of a subset is its gap plus the
complement mass.  No hypothesis: every size, every rank, every subset.

Read it three ways.  The free mass exceeds the gap by exactly the complement
mass.  The gap is the amount by which the free mass beats the complement mass.
And a direction that kills the gap form makes the two masses agree. -/
theorem freeMassMatrix_eq_gap_add_complementMassMatrix (D : WeightedDesign m k)
    (C : Finset (Fin m)) :
    freeMassMatrix D C = (subsetSum D C - 1) + complementMassMatrix D C := by
  classical
  have hsplit := weightedMass_add_complementMassMatrix D C
  have hexpand : freeMassMatrix D C
      = subsetSum D C - ∑ c ∈ C, D.weight c • atomMatrix (D.atom c) := by
    rw [freeMassMatrix, subsetSum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by rw [sub_smul, one_smul]
  rw [hexpand, ← hsplit]
  abel

/-- The gap is the free mass minus the complement mass. -/
theorem gap_eq_freeMassMatrix_sub_complementMassMatrix (D : WeightedDesign m k)
    (C : Finset (Fin m)) :
    subsetSum D C - 1 = freeMassMatrix D C - complementMassMatrix D C := by
  rw [freeMassMatrix_eq_gap_add_complementMassMatrix]
  abel

/-! ### The two masses as quadratic forms -/

theorem freeMassMatrix_form (D : WeightedDesign m k) (C : Finset (Fin m)) (probe : Fin k → ℝ) :
    probe ⬝ᵥ (freeMassMatrix D C *ᵥ probe)
      = ∑ c ∈ C, (1 - D.weight c) * (D.atom c ⬝ᵥ probe) ^ 2 := by
  rw [freeMassMatrix, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun c _ => by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]

theorem complementMassMatrix_form (D : WeightedDesign m k) (C : Finset (Fin m))
    (probe : Fin k → ℝ) :
    probe ⬝ᵥ (complementMassMatrix D C *ᵥ probe)
      = ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 := by
  rw [complementMassMatrix, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun c _ => by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]

/-- **The split as a scalar identity**, at an arbitrary direction. -/
theorem freeMassForm_eq_gapForm_add_complementMassForm (D : WeightedDesign m k)
    (C : Finset (Fin m)) (probe : Fin k → ℝ) :
    ∑ c ∈ C, (1 - D.weight c) * (D.atom c ⬝ᵥ probe) ^ 2
      = probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe)
        + ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 := by
  have hmatrix := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => probe ⬝ᵥ (M *ᵥ probe))
    (freeMassMatrix_eq_gap_add_complementMassMatrix D C)
  simp only [Matrix.add_mulVec, dotProduct_add] at hmatrix
  rw [freeMassMatrix_form, complementMassMatrix_form] at hmatrix
  exact hmatrix

/-! ## 2. The null-direction budget

A direction where the gap form vanishes is a TIGHT direction of the subset:
`sum over c in C of (g_c . v)^2 = |v|^2`.  Every tie owns one, by
`Gtz.isTie_yields_tightDirection`. -/

/-- Tightness in the two vocabularies. -/
theorem gapForm_eq_zero_iff_sum_sq (D : WeightedDesign m k) (C : Finset (Fin m))
    (probe : Fin k → ℝ) :
    probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe) = 0
      ↔ ∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2 = probe ⬝ᵥ probe := by
  rw [dominationGap_form, sub_eq_zero]

/-- **THE NULL-DIRECTION BUDGET IDENTITY.**  In a direction where the gap form
vanishes, the free mass of the subset and the mass of its complement are EQUAL.

The left side is the free mass that the certificate of
`Gtz.HasStrictCertificate` inverts.  The right side is the complement spend that
the same certificate asks to be small.  At equality the certificate has no
room, which is the exact reason `Gtz.not_hasStrictCertificate_of_isTie` holds.

No hypothesis on the corank, on the rank, on the size or on domination. -/
theorem nullDirection_budget_identity (D : WeightedDesign m k) (C : Finset (Fin m))
    {nullDir : Fin k → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0) :
    ∑ c ∈ C, (1 - D.weight c) * (D.atom c ⬝ᵥ nullDir) ^ 2
      = ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ nullDir) ^ 2 := by
  have hsplit := freeMassForm_eq_gapForm_add_complementMassForm D C nullDir
  rw [hnull, zero_add] at hsplit
  exact hsplit

/-- The same identity read from the tight-direction hypothesis. -/
theorem nullDirection_budget_identity_of_tight (D : WeightedDesign m k) (C : Finset (Fin m))
    {nullDir : Fin k → ℝ}
    (htight : ∑ c ∈ C, (D.atom c ⬝ᵥ nullDir) ^ 2 = nullDir ⬝ᵥ nullDir) :
    ∑ c ∈ C, (1 - D.weight c) * (D.atom c ⬝ᵥ nullDir) ^ 2
      = ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ nullDir) ^ 2 :=
  nullDirection_budget_identity D C ((gapForm_eq_zero_iff_sum_sq D C nullDir).mpr htight)

/-! ### The complement cannot be blind to a null direction -/

/-- **A NULL DIRECTION ALWAYS TOUCHES THE COMPLEMENT.**  At a design of size at
least two, no nonzero direction that kills the gap form of `C` is orthogonal to
every atom outside `C`.

The budget identity forces the free mass to vanish too, and every coefficient
`1 - t_c` is positive, so every selected atom is orthogonal to the direction.
Tightness then reads `|v|^2 = 0`. -/
theorem exists_compl_dotProduct_ne_zero_of_nullDirection (D : WeightedDesign m k)
    (hsize : 2 ≤ m) (C : Finset (Fin m)) {nullDir : Fin k → ℝ} (hne : nullDir ≠ 0)
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0) :
    ∃ c ∈ Cᶜ, D.atom c ⬝ᵥ nullDir ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hright : ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ nullDir) ^ 2 = 0 :=
    Finset.sum_eq_zero fun c hc => by rw [hcon c hc]; ring
  have hleft := nullDirection_budget_identity D C hnull
  rw [hright] at hleft
  have hterms : ∀ c ∈ C, (1 - D.weight c) * (D.atom c ⬝ᵥ nullDir) ^ 2 = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hleft
    exact fun c _ => mul_nonneg (by linarith [weight_lt_one D hsize c]) (sq_nonneg _)
  have hvanish : ∀ c ∈ C, (D.atom c ⬝ᵥ nullDir) ^ 2 = 0 := by
    intro c hc
    have hpos : 0 < 1 - D.weight c := by linarith [weight_lt_one D hsize c]
    have := hterms c hc
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (ne_of_gt hpos)
    · exact h
  have htight := (gapForm_eq_zero_iff_sum_sq D C nullDir).mp hnull
  rw [Finset.sum_congr rfl hvanish, Finset.sum_const_zero] at htight
  exact absurd htight.symm (ne_of_gt (dotProduct_self_pos hne))

/-- **The complement mass is strictly positive in every null direction.**  The
right side of the budget identity never vanishes, so the left side never does
either. -/
theorem complementMassForm_pos_of_nullDirection (D : WeightedDesign m k) (hsize : 2 ≤ m)
    (C : Finset (Fin m)) {nullDir : Fin k → ℝ} (hne : nullDir ≠ 0)
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0) :
    0 < ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ nullDir) ^ 2 := by
  classical
  obtain ⟨c, hc, hdot⟩ := exists_compl_dotProduct_ne_zero_of_nullDirection D hsize C hne hnull
  refine Finset.sum_pos' (fun d _ => mul_nonneg (D.weight_pos d).le (sq_nonneg _)) ⟨c, hc, ?_⟩
  exact mul_pos (D.weight_pos c) (lt_of_le_of_ne (sq_nonneg _)
    (fun h => hdot (sq_eq_zero_iff.mp h.symm)))

/-! ## 3. The free mass is positive definite at a weakly dominating subset

The tree carries `(free mass).PosDef` as a HYPOTHESIS inside
`Gtz.HasStrictCertificate`, inside `Gtz.FreeMassBudgetCertificate` and inside
`Gtz.NoStressResidual`.  At a weakly dominating subset it is free. -/

theorem transpose_freeMassMatrix (D : WeightedDesign m k) (C : Finset (Fin m)) :
    (freeMassMatrix D C)ᵀ = freeMassMatrix D C := by
  ext rowIndex colIndex
  simp only [freeMassMatrix, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
    atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem freeMassMatrix_posSemidef (D : WeightedDesign m k) (hsize : 2 ≤ m)
    (C : Finset (Fin m)) : (freeMassMatrix D C).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_freeMassMatrix D C), fun probe => ?_⟩
  rw [star_trivial, freeMassMatrix_form]
  exact Finset.sum_nonneg fun c _ =>
    mul_nonneg (by linarith [weight_lt_one D hsize c]) (sq_nonneg _)

/-- **THE FREE MASS OF A WEAKLY DOMINATING SUBSET IS POSITIVE DEFINITE.**
Unconditional at every size at least two and every rank.

The proof is the master identity plus section 2.  Off the tight cone the gap
form is strictly positive, and on the tight cone the complement mass form is
strictly positive.  Either way the free mass form is strictly positive. -/
theorem freeMassMatrix_posDef_of_dominates (D : WeightedDesign m k) (hsize : 2 ≤ m)
    (C : Finset (Fin m)) (hdominates : Dominates D C) : (freeMassMatrix D C).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_freeMassMatrix D C), fun probe hprobe => ?_⟩
  rw [star_trivial, freeMassMatrix_form,
    freeMassForm_eq_gapForm_add_complementMassForm D C probe]
  have hgap : 0 ≤ probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe) := by
    have hstep := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probe
    simpa only [star_trivial] using hstep
  have hcompl : 0 ≤ ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 :=
    Finset.sum_nonneg fun c _ => mul_nonneg (D.weight_pos c).le (sq_nonneg _)
  rcases eq_or_lt_of_le hgap with heq | hlt
  · have hpos := complementMassForm_pos_of_nullDirection D hsize C hprobe heq.symm
    linarith
  · linarith

/-- The determinant of the free mass of a weakly dominating subset is a unit,
so the inverse used by the certificate is a genuine inverse. -/
theorem isUnit_det_freeMassMatrix_of_dominates (D : WeightedDesign m k) (hsize : 2 ≤ m)
    (C : Finset (Fin m)) (hdominates : Dominates D C) :
    IsUnit (freeMassMatrix D C).det :=
  isUnit_iff_ne_zero.mpr (ne_of_gt (freeMassMatrix_posDef_of_dominates D hsize C
    hdominates).det_pos)

/-! ## 4. The spend identity

`Gtz.HasStrictCertificate` asks the complement to spend less than one unit of
free mass.  That spend is a sum over the complement.  The master identity turns
it into a trace of the GAP, and the sum disappears. -/

/-- **The certificate spend**, verbatim the second clause of the free-mass arm
of `Gtz.HasStrictCertificate`. -/
noncomputable def budgetSpend (D : WeightedDesign m k) (C : Finset (Fin m)) : ℝ :=
  ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ ((freeMassMatrix D C)⁻¹ *ᵥ D.atom c))

/-- The spend is the trace of the complement mass in the free-mass metric. -/
theorem budgetSpend_eq_trace (D : WeightedDesign m k) (C : Finset (Fin m)) :
    budgetSpend D C
      = Matrix.trace ((freeMassMatrix D C)⁻¹ * complementMassMatrix D C) := by
  rw [budgetSpend, complementMassMatrix, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_mul_atomMatrix_massGap]

/-- **THE SPEND IDENTITY.**  The certificate spend and the trace of the gap in
the free-mass metric add up to the rank.  A sum over the complement labels
becomes a trace of one matrix.

At rank three the certificate's second arm fires exactly when
`trace (freeMass^{-1} * gap) > 2`. -/
theorem budgetSpend_add_trace_freeMassInv_gap (D : WeightedDesign m k) (C : Finset (Fin m))
    (hunit : IsUnit (freeMassMatrix D C).det) :
    budgetSpend D C + Matrix.trace ((freeMassMatrix D C)⁻¹ * (subsetSum D C - 1))
      = (k : ℝ) := by
  rw [budgetSpend_eq_trace, ← Matrix.trace_add, ← Matrix.mul_add,
    add_comm (complementMassMatrix D C) (subsetSum D C - 1),
    ← freeMassMatrix_eq_gap_add_complementMassMatrix, Matrix.nonsing_inv_mul _ hunit,
    Matrix.trace_one]
  simp

/-- The spend, solved for. -/
theorem budgetSpend_eq_rank_sub_trace (D : WeightedDesign m k) (C : Finset (Fin m))
    (hunit : IsUnit (freeMassMatrix D C).det) :
    budgetSpend D C
      = (k : ℝ) - Matrix.trace ((freeMassMatrix D C)⁻¹ * (subsetSum D C - 1)) := by
  have := budgetSpend_add_trace_freeMassInv_gap D C hunit
  linarith

/-- **THE CERTIFICATE ARM, AS ONE TRACE INEQUALITY.**  At a weakly dominating
subset the free-mass arm of `Gtz.HasStrictCertificate` holds exactly when the
gap fills more than `k - 1` of the free-mass directions. -/
theorem freeMassArm_iff_trace_gt (D : WeightedDesign m 3) (hsize : 2 ≤ m)
    (C : Finset (Fin m)) (hdominates : Dominates D C) :
    ((freeMassMatrix D C).PosDef ∧ budgetSpend D C < 1)
      ↔ 2 < Matrix.trace ((freeMassMatrix D C)⁻¹ * (subsetSum D C - 1)) := by
  have hunit := isUnit_det_freeMassMatrix_of_dominates D hsize C hdominates
  have hspend := budgetSpend_eq_rank_sub_trace D C hunit
  constructor
  · rintro ⟨_, hlt⟩
    rw [hspend] at hlt
    norm_num at hlt
    linarith
  · intro htrace
    refine ⟨freeMassMatrix_posDef_of_dominates D hsize C hdominates, ?_⟩
    rw [hspend]
    norm_num
    linarith

/-- **THE TIE READS AS A TRACE CEILING.**  Every weakly dominating triple of a
`(6,3)` tie satisfies `trace (freeMass^{-1} * gap) <= 2`.  The free mass is
positive definite by section 3, so the landed
`Gtz.not_hasStrictCertificate_of_isTie` bites on the spend alone. -/
theorem trace_freeMassInv_gap_le_two_of_isTie (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) (hdominates : Dominates D C) :
    Matrix.trace ((freeMassMatrix D C)⁻¹ * (subsetSum D C - 1)) ≤ 2 := by
  by_contra hcon
  push Not at hcon
  exact not_hasStrictCertificate_of_isTie D htie C hcard
    (Or.inr ((freeMassArm_iff_trace_gt D (by omega) C hdominates).mpr hcon))

/-! ## 5. The corank-one normal form

Corank one means the gap form vanishes exactly on one line.  The master identity
then says the complement mass form sits UNDER the free mass form everywhere,
and TOUCHES it exactly on that line. -/

/-- **The gap of `C` has a null LINE at `nullDir`.**  The gap form vanishes at
`nullDir`, and every direction where it vanishes is a multiple of `nullDir`.
Together with weak domination this is exactly gap corank one. -/
def GapNullLine (D : WeightedDesign m k) (C : Finset (Fin m)) (nullDir : Fin k → ℝ) : Prop :=
  nullDir ≠ 0 ∧ nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0 ∧
    ∀ probe : Fin k → ℝ, probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe) = 0 →
      ∃ scale : ℝ, probe = scale • nullDir

/-- **The complement mass never beats the free mass at a weakly dominating
subset.**  The difference of the two forms IS the gap form. -/
theorem complementMassForm_le_freeMassForm_of_dominates (D : WeightedDesign m k)
    (C : Finset (Fin m)) (hdominates : Dominates D C) (probe : Fin k → ℝ) :
    ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2
      ≤ ∑ c ∈ C, (1 - D.weight c) * (D.atom c ⬝ᵥ probe) ^ 2 := by
  have hgap : 0 ≤ probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe) := by
    have hstep := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probe
    simpa only [star_trivial] using hstep
  have hsplit := freeMassForm_eq_gapForm_add_complementMassForm D C probe
  linarith

/-- **Off the null line the gap form is strictly positive.** -/
theorem gapForm_pos_of_gapNullLine (D : WeightedDesign m k) (C : Finset (Fin m))
    {nullDir : Fin k → ℝ} (hline : GapNullLine D C nullDir)
    (hdominates : Dominates D C) {probe : Fin k → ℝ}
    (hoff : ∀ scale : ℝ, probe ≠ scale • nullDir) :
    0 < probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe) := by
  have hgap : 0 ≤ probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe) := by
    have hstep := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probe
    simpa only [star_trivial] using hstep
  rcases eq_or_lt_of_le hgap with heq | hlt
  · obtain ⟨scale, hscale⟩ := hline.2.2 probe heq.symm
    exact absurd hscale (hoff scale)
  · exact hlt

/-- **THE CORANK-ONE NORMAL FORM.**  At a weakly dominating subset whose gap has
a null line, the complement mass form equals the free mass form along the line
and stays STRICTLY below it in every other direction.

This is the exact shape of the certificate-free locus.  The tree's free-mass
certificate asks the complement spend to stay below the free mass after
inversion.  At corank one the two forms touch, in exactly one direction. -/
theorem corankOne_normalForm (D : WeightedDesign m k) (hsize : 2 ≤ m) (C : Finset (Fin m))
    {nullDir : Fin k → ℝ} (hline : GapNullLine D C nullDir) (hdominates : Dominates D C) :
    (∑ c ∈ C, (1 - D.weight c) * (D.atom c ⬝ᵥ nullDir) ^ 2
        = ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ nullDir) ^ 2)
      ∧ (0 < ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ nullDir) ^ 2)
      ∧ (∀ probe : Fin k → ℝ, (∀ scale : ℝ, probe ≠ scale • nullDir) →
          ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2
            < ∑ c ∈ C, (1 - D.weight c) * (D.atom c ⬝ᵥ probe) ^ 2)
      ∧ (freeMassMatrix D C).PosDef := by
  refine ⟨nullDirection_budget_identity D C hline.2.1,
    complementMassForm_pos_of_nullDirection D hsize C hline.1 hline.2.1, fun probe hoff => ?_,
    freeMassMatrix_posDef_of_dominates D hsize C hdominates⟩
  have hpos := gapForm_pos_of_gapNullLine D C hline hdominates hoff
  have hsplit := freeMassForm_eq_gapForm_add_complementMassForm D C probe
  linarith

/-- **The null line is the unique touching direction.**  Equality of the two mass
forms at a nonzero direction forces that direction onto the null line. -/
theorem mem_nullLine_of_freeMassForm_eq_complementMassForm (D : WeightedDesign m k)
    (C : Finset (Fin m)) {nullDir : Fin k → ℝ} (hline : GapNullLine D C nullDir)
    {probe : Fin k → ℝ}
    (hequal : ∑ c ∈ C, (1 - D.weight c) * (D.atom c ⬝ᵥ probe) ^ 2
      = ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2) :
    ∃ scale : ℝ, probe = scale • nullDir := by
  have hsplit := freeMassForm_eq_gapForm_add_complementMassForm D C probe
  exact hline.2.2 probe (by linarith)

/-! ## 6. The corank-two residue at rank three

Corank two says the gap is a positive multiple of a single rank-one atom.  Two
consequences, both unconditional at rank three. -/

/-- **Two vectors of `R^3` always have a common orthogonal direction.**  Put them
in the first two rows of a three by three matrix and leave the third row zero.
The determinant dies and the kernel vector is the direction. -/
theorem exists_orthogonal_to_pair (first second : Fin 3 → ℝ) :
    ∃ direction : Fin 3 → ℝ, direction ≠ 0 ∧ first ⬝ᵥ direction = 0
      ∧ second ⬝ᵥ direction = 0 := by
  classical
  set rowMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of ![first, second, (0 : Fin 3 → ℝ)] with hrow
  have hdet : rowMatrix.det = 0 := by
    refine Matrix.det_eq_zero_of_row_eq_zero 2 fun colIndex => ?_
    simp [hrow]
  obtain ⟨direction, hne, hkernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨direction, hne, ?_, ?_⟩
  · have hzero := congrFun hkernel 0
    simpa [hrow, Matrix.mulVec, dotProduct] using hzero
  · have hzero := congrFun hkernel 1
    simpa [hrow, Matrix.mulVec, dotProduct] using hzero

/-- The gap form of a rank-one gap, at an arbitrary direction. -/
theorem gapForm_of_rankOneGap (D : WeightedDesign m k) (C : Finset (Fin m)) {lam : ℝ}
    {gapDir : Fin k → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix gapDir)
    (probe : Fin k → ℝ) :
    probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe) = lam * (gapDir ⬝ᵥ probe) ^ 2 := by
  rw [hgap, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]

/-- **NINE OF THE EIGHTEEN MIXED TRIPLES ARE FREE AT CORANK TWO.**  If the gap of
`C` is a multiple of one rank-one atom, then no triple obtained from `C` by one
swap dominates strictly, whatever the dropped and the added label are.

The witness is a direction orthogonal both to `gapDir` and to the added atom.
Rank three grants one: two linear conditions leave a line.  On that direction the
swapped gap form reads `-(dropped atom . direction)^2`, which is not positive.

The consequence for the campaign is a NEGATIVE one.  At a corank-two `(6,3)` tie
the tie condition on the nine triples that share TWO labels with `C` carries no
information at all, so the corank-two content is the complement triple and the
nine triples that share ONE label. -/
theorem not_posDef_swap_of_rankOneGap (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {gapDir : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix gapDir)
    {dropped added : Fin m} (hdropped : dropped ∈ C) (hadded : added ∉ C) :
    ¬ (subsetSum D (insert added (C.erase dropped)) - 1).PosDef := by
  classical
  obtain ⟨direction, hne, hgapDir, hadd⟩ := exists_orthogonal_to_pair gapDir (D.atom added)
  intro hposDef
  have hnotMem : added ∉ C.erase dropped := fun hmem => hadded (Finset.mem_of_mem_erase hmem)
  have hsumSwap : ∑ c ∈ insert added (C.erase dropped), (D.atom c ⬝ᵥ direction) ^ 2
      = (D.atom added ⬝ᵥ direction) ^ 2
        + ((∑ c ∈ C, (D.atom c ⬝ᵥ direction) ^ 2) - (D.atom dropped ⬝ᵥ direction) ^ 2) := by
    rw [Finset.sum_insert hnotMem, Finset.sum_erase_eq_sub hdropped]
  have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hne
  rw [star_trivial, dominationGap_form, hsumSwap, hadd] at hform
  have hgapZero : ∑ c ∈ C, (D.atom c ⬝ᵥ direction) ^ 2 - direction ⬝ᵥ direction = 0 := by
    have hrankOne := gapForm_of_rankOneGap D C hgap direction
    rw [dominationGap_form, hgapDir] at hrankOne
    simpa using hrankOne
  nlinarith [hform, hgapZero, sq_nonneg (D.atom dropped ⬝ᵥ direction)]

/-- The swapped triple really is a triple. -/
theorem card_swap_eq_three (C : Finset (Fin 6)) (hcard : C.card = 3) {dropped added : Fin 6}
    (hdropped : dropped ∈ C) (hadded : added ∉ C) :
    (insert added (C.erase dropped)).card = 3 := by
  classical
  have hnotMem : added ∉ C.erase dropped := fun hmem => hadded (Finset.mem_of_mem_erase hmem)
  rw [Finset.card_insert_of_notMem hnotMem, Finset.card_erase_of_mem hdropped, hcard]

/-- **The nine two-shared triples of a corank-two `(6,3)` tie, all free.** -/
theorem twoShared_not_posDef_of_rankOneGap_sixThree (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} {gapDir : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix gapDir)
    {dropped added : Fin 6} (hdropped : dropped ∈ C) (hadded : added ∉ C) :
    (insert added (C.erase dropped)).card = 3
      ∧ ¬ (subsetSum D (insert added (C.erase dropped)) - 1).PosDef :=
  ⟨card_swap_eq_three C hcard hdropped hadded,
    not_posDef_swap_of_rankOneGap D C hgap hdropped hadded⟩

/-! ### The complement kill, and the exact threshold -/

/-- **THE COMPLEMENT KILL AT A RANK-ONE GAP.**  If the weights inside `C` are
capped by `inner`, the weights outside by `outer`, and `inner * (1 + lam)` stays
below `1 - outer`, then the COMPLEMENT of `C` dominates strictly.

The inside share of any direction is at most `inner` times the atom-sum form,
which a rank-one gap prices as `1 + lam` times the squared norm.  The landed
`Gtz.posDef_subsetSum_of_outside_share_lt` then closes the complement. -/
theorem posDef_compl_of_rankOneGap_of_threshold (D : WeightedDesign m k)
    (C : Finset (Fin m)) (inner outer lam : ℝ) (houterPos : 0 < outer)
    (hinnerNonneg : 0 ≤ inner) (hlamNonneg : 0 ≤ lam)
    {gapDir : Fin k → ℝ} (hunit : gapDir ⬝ᵥ gapDir = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix gapDir)
    (hin : ∀ c ∈ C, D.weight c ≤ inner) (hout : ∀ c ∈ Cᶜ, D.weight c ≤ outer)
    (hthreshold : inner * (1 + lam) < 1 - outer) :
    (subsetSum D Cᶜ - 1).PosDef := by
  classical
  refine posDef_subsetSum_of_outside_share_lt D Cᶜ outer houterPos hout ?_
  intro probe hne
  rw [compl_compl]
  have hprobePos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hne
  have hcauchy : (gapDir ⬝ᵥ probe) ^ 2 ≤ probe ⬝ᵥ probe := by
    have := dotProduct_sq_le_mul gapDir probe
    rw [hunit, one_mul] at this
    exact this
  have hsum : ∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2
      = probe ⬝ᵥ probe + lam * (gapDir ⬝ᵥ probe) ^ 2 := by
    have hform := gapForm_of_rankOneGap D C hgap probe
    rw [dominationGap_form] at hform
    linarith
  have hinside : ∑ c ∈ C, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2
      ≤ inner * ∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun c hc =>
      mul_le_mul_of_nonneg_right (hin c hc) (sq_nonneg _)
  rw [hsum] at hinside
  nlinarith [hinside, mul_nonneg (mul_nonneg hinnerNonneg hlamNonneg)
      (sub_nonneg.mpr hcauchy),
    mul_lt_mul_of_pos_right hthreshold hprobePos]

/-- **THE CORANK-TWO THRESHOLD AT `(6,3)`.**  A tie whose gap at a triple is a
multiple of one rank-one atom must satisfy `1 - outer <= inner * (1 + lam)`.  The
complement of a triple is a triple, so the tie must refuse it. -/
theorem rankOneGap_threshold_of_isTie (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) (inner outer lam : ℝ) (houterPos : 0 < outer)
    (hinnerNonneg : 0 ≤ inner) (hlamNonneg : 0 ≤ lam)
    {gapDir : Fin 3 → ℝ} (hunit : gapDir ⬝ᵥ gapDir = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix gapDir)
    (hin : ∀ c ∈ C, D.weight c ≤ inner) (hout : ∀ c ∈ Cᶜ, D.weight c ≤ outer) :
    1 - outer ≤ inner * (1 + lam) := by
  by_contra hcon
  push Not at hcon
  exact htie.2 Cᶜ (card_compl_eq_three_of_card_eq_three C hcard)
    (posDef_compl_of_rankOneGap_of_threshold D C inner outer lam houterPos hinnerNonneg
      hlamNonneg hunit hgap hin hout hcon)

/-- **THE THRESHOLD WITH THE MAXIMAL CAPS.**  The split caps of
`Gtz.exists_splitWeightCaps_add_lt_one` obey `inner + outer < 1` at every design,
so the threshold turns into a strictly positive floor on `lam`:

  `0 < 1 - inner - outer <= inner * lam`.

A corank-two `(6,3)` tie carries a gap eigenvalue at least
`(1 - inner - outer) / inner`. -/
theorem lam_floor_of_rankOneGap_isTie_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) (lam : ℝ) (hlamNonneg : 0 ≤ lam)
    {gapDir : Fin 3 → ℝ} (hunit : gapDir ⬝ᵥ gapDir = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix gapDir) :
    ∃ inner outer : ℝ, 0 < inner ∧ 0 < outer ∧ inner + outer < 1
      ∧ 1 - inner - outer ≤ inner * lam ∧ 0 < lam := by
  classical
  have hcomplNe : Cᶜ.Nonempty :=
    Finset.card_pos.mp (by rw [card_compl_eq_three_of_card_eq_three C hcard]; omega)
  obtain ⟨inner, outer, hinnerPos, houterPos, hcaps, hin, hout⟩ :=
    exists_splitWeightCaps_add_lt_one D C (by omega) hcomplNe
  have hthreshold := rankOneGap_threshold_of_isTie D htie C hcard inner outer lam houterPos
    hinnerPos.le hlamNonneg hunit hgap hin hout
  refine ⟨inner, outer, hinnerPos, houterPos, hcaps, by nlinarith [hthreshold], ?_⟩
  rcases eq_or_lt_of_le hlamNonneg with heq | hlt
  · exfalso
    rw [← heq] at hthreshold
    nlinarith [hthreshold, hcaps]
  · exact hlt

/-! ### The threshold in leverage vocabulary

The eigenvalue `lam` of a rank-one gap is its trace, so it is the leverage sum
of the triple minus the rank. -/

theorem trace_gap_eq_sum_leverage_sub (D : WeightedDesign m k) (C : Finset (Fin m)) :
    Matrix.trace (subsetSum D C - 1) = (∑ c ∈ C, leverageOf (D.atom c)) - (k : ℝ) := by
  rw [subsetSum, Matrix.trace_sub, Matrix.trace_sum, Matrix.trace_one]
  simp [trace_atomMatrix]

theorem lam_eq_sum_leverage_sub_of_rankOneGap (D : WeightedDesign m k) (C : Finset (Fin m))
    {lam : ℝ} {gapDir : Fin k → ℝ} (hunit : gapDir ⬝ᵥ gapDir = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix gapDir) :
    lam = (∑ c ∈ C, leverageOf (D.atom c)) - (k : ℝ) := by
  have hleft : Matrix.trace (subsetSum D C - 1) = lam := by
    rw [hgap, Matrix.trace_smul, trace_atomMatrix, smul_eq_mul,
      ← leverageOf_eq_dotProduct_self] at *
    rw [hunit] at *
    ring
  rw [← hleft, trace_gap_eq_sum_leverage_sub]

/-- **THE SHARPENED LEVERAGE FLOOR AT A CORANK-TWO `(6,3)` TIE.**  The landed
`Gtz.sum_leverage_floor_of_isTie_sixThree` reads
`1 - outer <= inner * (sum of leverages)`.  At a rank-one gap the identity
`lam = sum of leverages - 3` sharpens it by `2 * inner`:

  `1 - outer <= inner * (sum over c in C of l_c - 2)`. -/
theorem sum_leverage_floor_sharp_of_rankOneGap_isTie (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) (lam : ℝ) (hlamNonneg : 0 ≤ lam)
    {gapDir : Fin 3 → ℝ} (hunit : gapDir ⬝ᵥ gapDir = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix gapDir) :
    ∃ inner outer : ℝ, 0 < inner ∧ 0 < outer ∧ inner + outer < 1
      ∧ 1 - outer ≤ inner * ((∑ c ∈ C, leverageOf (D.atom c)) - 2) := by
  classical
  have hcomplNe : Cᶜ.Nonempty :=
    Finset.card_pos.mp (by rw [card_compl_eq_three_of_card_eq_three C hcard]; omega)
  obtain ⟨inner, outer, hinnerPos, houterPos, hcaps, hin, hout⟩ :=
    exists_splitWeightCaps_add_lt_one D C (by omega) hcomplNe
  have hthreshold := rankOneGap_threshold_of_isTie D htie C hcard inner outer lam houterPos
    hinnerPos.le hlamNonneg hunit hgap hin hout
  have hlam := lam_eq_sum_leverage_sub_of_rankOneGap D C hunit hgap
  refine ⟨inner, outer, hinnerPos, houterPos, hcaps, ?_⟩
  rw [hlam] at hthreshold
  push_cast at hthreshold
  linarith [hthreshold]

/-! ## 7. Why the corank-two lever is silent at `(5,3)`

`Gtz.diamondDesign` is a primitive `(5,3)` tie.  The lever of section 6 is
`Gtz.posDef_subsetSum_of_outside_share_lt` applied to the complement.  Its
hypothesis asks the INSIDE share to stay strictly below `1 - outer` in every
direction.  That hypothesis is refutable the moment the complement atoms share
an orthogonal direction, and at `(5,3)` they always do. -/

/-- **A blind complement puts the whole unit mass inside.**  If a nonzero
direction is orthogonal to every atom outside `C`, Parseval reads the inside
share as the full squared norm. -/
theorem full_inside_share_of_commonOrthogonal (D : WeightedDesign m k) (C : Finset (Fin m))
    {direction : Fin k → ℝ} (horthogonal : ∀ c ∈ Cᶜ, D.atom c ⬝ᵥ direction = 0) :
    ∑ c ∈ C, D.weight c * (D.atom c ⬝ᵥ direction) ^ 2 = direction ⬝ᵥ direction := by
  classical
  have hparseval := dotProduct_self_eq_sum_weight_mul_sq D direction
  have hsplit : (∑ c ∈ C, D.weight c * (D.atom c ⬝ᵥ direction) ^ 2)
      + ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ direction) ^ 2
      = ∑ c, D.weight c * (D.atom c ⬝ᵥ direction) ^ 2 := Finset.sum_add_sum_compl C _
  have houtside : ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ direction) ^ 2 = 0 :=
    Finset.sum_eq_zero fun c hc => by rw [horthogonal c hc]; ring
  rw [houtside, add_zero] at hsplit
  rw [hsplit, ← hparseval]

/-- **THE INSIDE-SHARE CRITERION IS UNSATISFIABLE AT `(5,3)`.**  At every triple
of every `(5,3)` design the complement has two atoms, and two vectors of `R^3`
always share an orthogonal direction.  So the hypothesis that section 6 feeds to
`Gtz.posDef_subsetSum_of_outside_share_lt` fails, with no hypothesis on the
design.

This is the exact separator.  `Gtz.diamondDesign` is a primitive `(5,3)` tie, and
every corank-two theorem of section 6 is silent there for one reason: the
complement of a triple is not a triple. -/
theorem not_insideShareCriterion_fiveThree (D : WeightedDesign 5 3) (C : Finset (Fin 5))
    (hcard : C.card = 3) (outer : ℝ) (houterPos : 0 < outer) :
    ¬ (∀ probe : Fin 3 → ℝ, probe ≠ 0 →
        ∑ c ∈ C, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 < (1 - outer) * (probe ⬝ᵥ probe)) := by
  classical
  intro hcriterion
  have hcomplCard : Cᶜ.card = 2 := by rw [Finset.card_compl, Fintype.card_fin, hcard]
  obtain ⟨first, second, hne, hpair⟩ := Finset.card_eq_two.mp hcomplCard
  obtain ⟨direction, hdirNe, hfirst, hsecond⟩ :=
    exists_orthogonal_to_pair (D.atom first) (D.atom second)
  have horthogonal : ∀ c ∈ Cᶜ, D.atom c ⬝ᵥ direction = 0 := by
    intro c hc
    rw [hpair] at hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hfirst
    · rw [Finset.mem_singleton.mp hc]; exact hsecond
  have hfull := full_inside_share_of_commonOrthogonal D C horthogonal
  have hstrict := hcriterion direction hdirNe
  rw [hfull] at hstrict
  nlinarith [hstrict, dotProduct_self_pos hdirNe, houterPos]

/-- **At `(6,3)` the same obstruction is exactly dependence of the complement.**
A triple with a common orthogonal direction never dominates
(`Gtz.not_dominates_of_commonOrthogonal`), so on the branch the corank-two lever
targets the obstruction is absent. -/
theorem not_dominates_compl_of_commonOrthogonal_sixThree (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) {direction : Fin 3 → ℝ} (hdirNe : direction ≠ 0)
    (horthogonal : ∀ c ∈ Cᶜ, D.atom c ⬝ᵥ direction = 0) :
    ¬ Dominates D Cᶜ :=
  not_dominates_of_commonOrthogonal D Cᶜ ⟨direction, hdirNe, horthogonal⟩

/-! ## 8. Inhabitation of the corank-one arm, at a landed `(6,3)` tie

`Gtz.nonUniformLeverageTieDesign` is a `(6,3)` tie.  Its triple `{0,1,2}` of
heavy atoms dominates weakly, and its gap is

  `(8/3) * ((x0 - x1)^2 + (x0 - x2)^2 + (x1 - x2)^2)`

as a quadratic form.  So the null set is exactly the line through `(1,1,1)`, and
the corank is one.  Every hypothesis of sections 2, 3, 4 and 5 is satisfied
there. -/

/-- The heavy triple of the landed tie. -/
def heavyTriple : Finset (Fin 6) := {0, 1, 2}

theorem heavyTriple_card : heavyTriple.card = 3 := by decide

theorem heavyTriple_compl : heavyTripleᶜ = ({3, 4, 5} : Finset (Fin 6)) := by decide

/-- The gap form of the heavy triple, in closed form. -/
theorem nonUniformLeverageTie_gapForm (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ ((subsetSum nonUniformLeverageTieDesign heavyTriple - 1) *ᵥ probe)
      = (8 / 3) * ((probe 0 - probe 1) ^ 2 + (probe 0 - probe 2) ^ 2
          + (probe 1 - probe 2) ^ 2) := by
  rw [dominationGap_form, heavyTriple]
  rw [show ({0, 1, 2} : Finset (Fin 6)) = insert 0 (insert 1 {2}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [nonUniformLeverageTieDesign_atom, nonUniformLeverageTieAtom, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The heavy triple dominates weakly. -/
theorem nonUniformLeverageTie_dominates_heavyTriple :
    Dominates nonUniformLeverageTieDesign heavyTriple := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one _ _), fun probe => ?_⟩
  rw [star_trivial, nonUniformLeverageTie_gapForm]
  positivity

/-- **THE CORANK-ONE ARM IS INHABITED.**  The heavy triple of the landed `(6,3)`
tie has gap null LINE through `(1,1,1)`. -/
theorem gapNullLine_nonUniformLeverageTieDesign :
    GapNullLine nonUniformLeverageTieDesign heavyTriple ![1, 1, 1] := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have := congrFun hzero 0
    simp at this
  · rw [nonUniformLeverageTie_gapForm]
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  · intro probe hzero
    rw [nonUniformLeverageTie_gapForm] at hzero
    have hfirst := sq_nonneg (probe 0 - probe 1)
    have hsecond := sq_nonneg (probe 0 - probe 2)
    have hthird := sq_nonneg (probe 1 - probe 2)
    have hone : probe 0 = probe 1 := by
      have hsq : (probe 0 - probe 1) ^ 2 = 0 := by linarith
      have := sq_eq_zero_iff.mp hsq
      linarith
    have htwo : probe 0 = probe 2 := by
      have hsq : (probe 0 - probe 2) ^ 2 = 0 := by linarith
      have := sq_eq_zero_iff.mp hsq
      linarith
    refine ⟨probe 0, ?_⟩
    funext coord
    fin_cases coord
    · simp
    · simp [← hone]
    · simp [← htwo]

/-- **THE BUDGET IDENTITY AT THE LANDED TIE, IN CLOSED FORM.**  Both sides read
`8/3`.  The three heavy atoms each pair with the null direction at value one and
carry free coefficient `8/9`.  The three light atoms each pair at value two and
carry weight `2/9`. -/
theorem budget_identity_nonUniformLeverageTieDesign :
    (∑ c ∈ heavyTriple, (1 - nonUniformLeverageTieDesign.weight c)
        * (nonUniformLeverageTieDesign.atom c ⬝ᵥ ![1, 1, 1]) ^ 2 = 8 / 3)
      ∧ (∑ c ∈ heavyTripleᶜ, nonUniformLeverageTieDesign.weight c
        * (nonUniformLeverageTieDesign.atom c ⬝ᵥ ![1, 1, 1]) ^ 2 = 8 / 3) := by
  constructor
  · rw [heavyTriple, show ({0, 1, 2} : Finset (Fin 6)) = insert 0 (insert 1 {2}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [nonUniformLeverageTieDesign_atom, nonUniformLeverageTieDesign_weight,
      nonUniformLeverageTieAtom, nonUniformLeverageTieWeight, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    norm_num
  · rw [heavyTriple_compl,
      show ({3, 4, 5} : Finset (Fin 6)) = insert 3 (insert 4 {5}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [nonUniformLeverageTieDesign_atom, nonUniformLeverageTieDesign_weight,
      nonUniformLeverageTieAtom, nonUniformLeverageTieWeight, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    norm_num

/-- **THE CORANK-ONE NORMAL FORM, AT THE LANDED TIE.**  Every conclusion of
`Gtz.corankOne_normalForm` holds at `Gtz.nonUniformLeverageTieDesign`. -/
theorem corankOne_normalForm_nonUniformLeverageTieDesign :
    (∑ c ∈ heavyTriple, (1 - nonUniformLeverageTieDesign.weight c)
        * (nonUniformLeverageTieDesign.atom c ⬝ᵥ ![1, 1, 1]) ^ 2
      = ∑ c ∈ heavyTripleᶜ, nonUniformLeverageTieDesign.weight c
        * (nonUniformLeverageTieDesign.atom c ⬝ᵥ ![1, 1, 1]) ^ 2)
      ∧ (freeMassMatrix nonUniformLeverageTieDesign heavyTriple).PosDef := by
  refine ⟨nullDirection_budget_identity nonUniformLeverageTieDesign heavyTriple
    gapNullLine_nonUniformLeverageTieDesign.2.1, ?_⟩
  exact freeMassMatrix_posDef_of_dominates nonUniformLeverageTieDesign (by omega)
    heavyTriple nonUniformLeverageTie_dominates_heavyTriple

/-- **THE TRACE CEILING, AT THE LANDED TIE.**  The antecedent of
`Gtz.trace_freeMassInv_gap_le_two_of_isTie` is inhabited. -/
theorem trace_ceiling_nonUniformLeverageTieDesign :
    Matrix.trace ((freeMassMatrix nonUniformLeverageTieDesign heavyTriple)⁻¹
      * (subsetSum nonUniformLeverageTieDesign heavyTriple - 1)) ≤ 2 :=
  trace_freeMassInv_gap_le_two_of_isTie nonUniformLeverageTieDesign
    nonUniformLeverageTieDesign_isTie heavyTriple heavyTriple_card
    nonUniformLeverageTie_dominates_heavyTriple

/-! ## 9. Inhabitation of the corank-two arm

The corank-two hypothesis `subsetSum D C - 1 = lam * gapDir gapDir^T` has no
inhabitant at a `(6,3)` TIE: that locus is exactly the one this fork failed to
close, and 300000 prior samples plus 100000 new ones found no tie in it.  The
hypothesis is nonetheless inhabited at a `(6,3)` DESIGN, and the design below
shows the threshold theorem firing.

The six atoms are `(2,0,0)`, `(0,1,0)`, `(0,0,1)`, `(2,0,0)`, `(0,2,0)`,
`(0,0,2)` with weights `1/6, 1/6, 1/6, 1/12, 5/24, 5/24`.  Every entry is
rational.  The triple `{0,1,2}` has atom sum `diag(4,1,1)` and gap
`3 * e0 e0^T`, a rank-one gap with `lam = 3`.  The caps read `inner = 1/6` and
`outer = 5/24`, so `inner * (1 + lam) = 2/3 < 19/24 = 1 - outer` and the
threshold fires.  Its conclusion is checkable: the complement atom sum is
`diag(4,4,4)` and the complement gap is `diag(3,3,3)`, positive definite. -/

/-- The six atoms of the rank-one-gap witness. -/
noncomputable def rankOneGapWitnessAtom : Fin 6 → Fin 3 → ℝ
  | 0 => ![2, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![0, 0, 1]
  | 3 => ![2, 0, 0]
  | 4 => ![0, 2, 0]
  | 5 => ![0, 0, 2]

/-- The six weights of the rank-one-gap witness. -/
noncomputable def rankOneGapWitnessWeight : Fin 6 → ℝ
  | 0 => 1 / 6
  | 1 => 1 / 6
  | 2 => 1 / 6
  | 3 => 1 / 12
  | 4 => 5 / 24
  | 5 => 5 / 24

/-- **The rank-one-gap witness design.**  A genuine `(6,3)` weighted design with
rational atoms and rational weights. -/
noncomputable def rankOneGapWitnessDesign : WeightedDesign 6 3 where
  atom := rankOneGapWitnessAtom
  weight := rankOneGapWitnessWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [rankOneGapWitnessWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [rankOneGapWitnessWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [rankOneGapWitnessAtom, rankOneGapWitnessWeight, atomMatrix,
        Matrix.cons_val_two] <;> norm_num

theorem rankOneGapWitnessDesign_atom : rankOneGapWitnessDesign.atom = rankOneGapWitnessAtom := rfl

theorem rankOneGapWitnessDesign_weight :
    rankOneGapWitnessDesign.weight = rankOneGapWitnessWeight := rfl

/-- **THE RANK-ONE GAP HYPOTHESIS IS INHABITED.**  The gap of `{0,1,2}` is three
times the atom of the first coordinate axis. -/
theorem rankOneGapWitness_gap :
    subsetSum rankOneGapWitnessDesign heavyTriple - 1
      = (3 : ℝ) • atomMatrix (![1, 0, 0] : Fin 3 → ℝ) := by
  rw [heavyTriple, subsetSum,
    show ({0, 1, 2} : Finset (Fin 6)) = insert 0 (insert 1 {2}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [rankOneGapWitnessDesign_atom, rankOneGapWitnessAtom, atomMatrix,
      Matrix.cons_val_two]

/-- The weight caps of the witness, inside and outside the triple. -/
theorem rankOneGapWitness_caps :
    (∀ c ∈ heavyTriple, rankOneGapWitnessDesign.weight c ≤ 1 / 6)
      ∧ (∀ c ∈ heavyTripleᶜ, rankOneGapWitnessDesign.weight c ≤ 5 / 24) := by
  constructor
  · intro c hc
    have hlabel : c = 0 ∨ c = 1 ∨ c = 2 := by
      have hmem : c ∈ ({0, 1, 2} : Finset (Fin 6)) := hc
      simpa using hmem
    rw [rankOneGapWitnessDesign_weight]
    rcases hlabel with rfl | rfl | rfl <;> norm_num [rankOneGapWitnessWeight]
  · intro c hc
    rw [heavyTriple_compl] at hc
    have hlabel : c = 3 ∨ c = 4 ∨ c = 5 := by simpa using hc
    rw [rankOneGapWitnessDesign_weight]
    rcases hlabel with rfl | rfl | rfl <;> norm_num [rankOneGapWitnessWeight]

/-- **THE THRESHOLD FIRES AT THE WITNESS.**  The complement of the rank-one-gap
triple dominates STRICTLY, so the witness is not a tie.  This is
`Gtz.posDef_compl_of_rankOneGap_of_threshold` at work, with
`inner * (1 + lam) = 2/3` against `1 - outer = 19/24`. -/
theorem posDef_compl_rankOneGapWitness :
    (subsetSum rankOneGapWitnessDesign heavyTripleᶜ - 1).PosDef := by
  refine posDef_compl_of_rankOneGap_of_threshold rankOneGapWitnessDesign heavyTriple
    (1 / 6) (5 / 24) 3 (by norm_num) (by norm_num) (by norm_num) ?_ rankOneGapWitness_gap
    rankOneGapWitness_caps.1 rankOneGapWitness_caps.2 (by norm_num)
  simp [dotProduct, Fin.sum_univ_three]

/-- **THE WITNESS IS NOT A TIE.**  A corank-two gap under the threshold is
incompatible with `Gtz.IsTie`, and the witness shows the incompatibility at a
concrete rational design. -/
theorem not_isTie_rankOneGapWitnessDesign : ¬ IsTie rankOneGapWitnessDesign := fun htie =>
  htie.2 heavyTripleᶜ (card_compl_eq_three_of_card_eq_three heavyTriple heavyTriple_card)
    posDef_compl_rankOneGapWitness

/-- **THE TWO-SHARED SWAP IS FREE AT THE WITNESS.**  Dropping label `2` from the
rank-one-gap triple and adding label `3` gives a triple that does not dominate
strictly, with no computation on the swapped triple itself. -/
theorem not_posDef_swap_rankOneGapWitness :
    ¬ (subsetSum rankOneGapWitnessDesign (insert 3 (heavyTriple.erase 2)) - 1).PosDef :=
  not_posDef_swap_of_rankOneGap rankOneGapWitnessDesign heavyTriple rankOneGapWitness_gap
    (by decide) (by decide)

/-! ## 10. The ledger of this module

Read the four statements below as the exact content added to the tree. -/

/-- **THE FREE-MASS SPLIT AND ITS FOUR READINGS.**  One matrix identity, the
null-direction budget, the free-mass positivity that the tree assumed, and the
spend identity that turns a complement sum into a gap trace. -/
theorem freeMassSplit_ledger (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0) (hne : nullDir ≠ 0) :
    (freeMassMatrix D C = (subsetSum D C - 1) + complementMassMatrix D C)
      ∧ (∑ c ∈ C, (1 - D.weight c) * (D.atom c ⬝ᵥ nullDir) ^ 2
          = ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ nullDir) ^ 2)
      ∧ (0 < ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ nullDir) ^ 2)
      ∧ (freeMassMatrix D C).PosDef
      ∧ (budgetSpend D C
          + Matrix.trace ((freeMassMatrix D C)⁻¹ * (subsetSum D C - 1)) = 3) := by
  refine ⟨freeMassMatrix_eq_gap_add_complementMassMatrix D C,
    nullDirection_budget_identity D C hnull,
    complementMassForm_pos_of_nullDirection D (by omega) C hne hnull,
    freeMassMatrix_posDef_of_dominates D (by omega) C hdominates, ?_⟩
  have := budgetSpend_add_trace_freeMassInv_gap D C
    (isUnit_det_freeMassMatrix_of_dominates D (by omega) C hdominates)
  norm_num at this
  linarith

/-- **THE CORANK-TWO LEDGER AT `(6,3)`.**  What a rank-one gap at a tie costs,
and what it makes free.

The first clause is the threshold, sharp as an inequality on `lam`.  The second
is the leverage reading, sharper by `2 * inner` than the landed
`Gtz.sum_leverage_floor_of_isTie_sixThree`.  The third says the nine triples
that share two labels with `C` carry no tie information. -/
theorem corankTwo_ledger_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) (lam : ℝ) (hlamNonneg : 0 ≤ lam)
    {gapDir : Fin 3 → ℝ} (hunit : gapDir ⬝ᵥ gapDir = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix gapDir) :
    (∃ inner outer : ℝ, 0 < inner ∧ 0 < outer ∧ inner + outer < 1
        ∧ 1 - inner - outer ≤ inner * lam ∧ 0 < lam)
      ∧ (∃ inner outer : ℝ, 0 < inner ∧ 0 < outer ∧ inner + outer < 1
        ∧ 1 - outer ≤ inner * ((∑ c ∈ C, leverageOf (D.atom c)) - 2))
      ∧ (∀ dropped ∈ C, ∀ added ∉ C,
          (insert added (C.erase dropped)).card = 3
            ∧ ¬ (subsetSum D (insert added (C.erase dropped)) - 1).PosDef) :=
  ⟨lam_floor_of_rankOneGap_isTie_sixThree D htie C hcard lam hlamNonneg hunit hgap,
    sum_leverage_floor_sharp_of_rankOneGap_isTie D htie C hcard lam hlamNonneg hunit hgap,
    fun _dropped hdropped _added hadded =>
      twoShared_not_posDef_of_rankOneGap_sixThree D C hcard hgap hdropped hadded⟩

/-- **THE `(5,3)` SEPARATOR, AS ONE STATEMENT.**  The corank-two lever runs at
`(6,3)` and cannot run at `(5,3)`.  The first clause refutes the lever's
hypothesis at every triple of every `(5,3)` design.  The second names the
property that makes the lever legal at `(6,3)`: the complement of a triple is a
triple, and a dominating triple has no common orthogonal direction. -/
theorem fiveThree_separator (D : WeightedDesign 5 3) (C : Finset (Fin 5))
    (hcard : C.card = 3) (outer : ℝ) (houterPos : 0 < outer) :
    (¬ (∀ probe : Fin 3 → ℝ, probe ≠ 0 →
        ∑ c ∈ C, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 < (1 - outer) * (probe ⬝ᵥ probe)))
      ∧ (∀ B : Finset (Fin 6), B.card = 3 → Bᶜ.card = 3) :=
  ⟨not_insideShareCriterion_fiveThree D C hcard outer houterPos,
    fun B hB => card_compl_eq_three_of_card_eq_three B hB⟩

end Gtz
