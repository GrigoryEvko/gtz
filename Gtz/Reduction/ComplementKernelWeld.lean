import Gtz.Reduction.SplitTransfer
import Gtz.Design.KFourBandAtlas
import Gtz.Quantitative.SixThreeCrux
import Gtz.Reduction.PrincipalMinorsThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Complement-kernel weld

For a weighted design, the full excess

  `H = sum_c (1 - t_c) A_c = subsetSum univ - 1`

is positive definite.  If `pick` enumerates labels to omit, the gap of the
complement is `H - Uᵀ U`, where the rows of `U` are the omitted atoms.  Whitening
`H` and applying the rectangular `AB/BA` transfer identifies this gap with

  `1 - U H⁻¹ Uᵀ`.

The theorem is packaged as a `LoewnerEquiv`: it transports both the PSD verdict
needed for domination and the PD verdict needed to exclude strict domination.

## What this module does and does not buy

It BUYS a change of coordinates.  Every complement test -- one per omitted set,
at any size and any rank -- is rewritten as a principal-minor test on a single
inverse-metric Gram matrix, and the first rung of that test is identified with
the already-landed full-base `pivot`, hence is free at a `(6,3)` crux by
`hasStrictlyDominatingCoSingletons`.  The residual selector is therefore an edge
condition on three pairs plus one determinant, with no first-rung clause.

It DISCHARGES NOTHING.  The closing equivalence
`cruxKernelTriangleSelection_iff_gtzWeighted_six_three` is a RESTATEMENT: its
left side unwinds to "no crux exists", which is the target.  Good triangle iff
the complement weakly dominates iff a crux has a dominating triple iff no crux
exists.  The reverse direction is vacuous -- from `GtzWeighted 6 3` no crux
exists, so the universally quantified selection holds over an empty family.  It
is a lossless re-coordinatisation and no open goal is closed by it.

The single-atom case of the kernel is not new: `Gtz.pivot_eq_dot` and
`Gtz/Field/CorankOne.lean` already read one omitted atom against the inverse
co-Parseval operator.  What is new here is the SET version and its packaging as
a Loewner equivalence.
-/

namespace Gtz

open Matrix

variable {size rank omittedSize : ℕ}

/-- The full excess, written in its positive co-Parseval form. -/
noncomputable def complementKernelMetric (design : WeightedDesign size rank) :
    Matrix (Fin rank) (Fin rank) ℝ :=
  ∑ label, (1 - design.weight label) • atomMatrix (design.atom label)

/-- The kernel metric is exactly the tree's full descent excess. -/
theorem complementKernelMetric_eq_fullExcess
    (design : WeightedDesign size rank) :
    complementKernelMetric design = subsetSum design Finset.univ - 1 := by
  exact (fullExcess_eq_coParseval design).symm

/-- The inverse-metric Gram matrix of an enumerated set of omitted atoms. -/
noncomputable def complementKernel (design : WeightedDesign size rank)
    (pick : Fin omittedSize → Fin size) : Matrix (Fin omittedSize) (Fin omittedSize) ℝ :=
  selectedAtomRows design pick * (complementKernelMetric design)⁻¹
    * (selectedAtomRows design pick)ᵀ

/-- The kernel gap whose principal minors are the successive complement tests. -/
noncomputable def complementKernelGap (design : WeightedDesign size rank)
    (pick : Fin omittedSize → Fin size) : Matrix (Fin omittedSize) (Fin omittedSize) ℝ :=
  1 - complementKernel design pick

/-- Whitening inverts the metric it whitens. -/
theorem inverse_eq_mul_transpose_of_congruence_to_one
    {metric whitener : Matrix (Fin rank) (Fin rank) ℝ}
    (hunit : IsUnit whitener.det)
    (hwhiten : whitenerᵀ * metric * whitener = 1) :
    metric⁻¹ = whitener * whitenerᵀ := by
  have htransposeUnit : IsUnit (whitenerᵀ).det := by
    rwa [Matrix.det_transpose]
  have hleft : whitenerᵀ * (metric * whitener) = 1 := by
    rw [← Matrix.mul_assoc]
    exact hwhiten
  have hmetricWhitener : metric * whitener = (whitenerᵀ)⁻¹ := by
    have hpush := congrArg (fun matrix => (whitenerᵀ)⁻¹ * matrix) hleft
    simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ htransposeUnit] using hpush
  refine Matrix.inv_eq_right_inv ?_
  rw [← Matrix.mul_assoc, hmetricWhitener,
    Matrix.nonsing_inv_mul _ htransposeUnit]

/-- The complement dictionary before whitening. -/
theorem complementGap_eq_metric_sub_selectedGram
    (design : WeightedDesign size rank) (pick : Fin omittedSize → Fin size)
    (hinjective : Function.Injective pick) :
    subsetSum design (Finset.image pick Finset.univ)ᶜ - 1
      = complementKernelMetric design
          - (selectedAtomRows design pick)ᵀ * selectedAtomRows design pick := by
  classical
  let omitted : Finset (Fin size) := Finset.image pick Finset.univ
  have hsplit : subsetSum design Finset.univ
      = subsetSum design omitted + subsetSum design omittedᶜ := by
    rw [subsetSum, subsetSum, subsetSum,
      ← Finset.sum_add_sum_compl omitted (fun label => atomMatrix (design.atom label))]
  have hfull : subsetSum design Finset.univ - 1 = complementKernelMetric design := by
    rw [subsetSum, ← design.isParseval, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by
      rw [sub_smul, one_smul]
  have hselected : (selectedAtomRows design pick)ᵀ * selectedAtomRows design pick
      = subsetSum design omitted := by
    exact transpose_mul_selectedAtomRows design pick hinjective
  change subsetSum design omittedᶜ - 1 = _
  rw [hselected]
  rw [← hfull]
  rw [hsplit]
  abel

/-- **THE WELD.**  A complement gap and its inverse-full-excess kernel have the
same PSD and PD verdicts.  The statement is rank-general and the omitted set may
have any size; the `(6,3)` hinge uses `omittedSize = rank = 3`. -/
theorem loewnerEquiv_complementGap_kernel
    (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (pick : Fin omittedSize → Fin size) (hinjective : Function.Injective pick) :
    LoewnerEquiv
      (subsetSum design (Finset.image pick Finset.univ)ᶜ - 1)
      (complementKernelGap design pick) := by
  let metric := complementKernelMetric design
  let rows := selectedAtomRows design pick
  have hmetricPosDef : metric.PosDef := by
    exact coParseval_posDef design hsize
  obtain ⟨whitener, hwhitenerUnit, hwhiten⟩ :=
    exists_congruence_to_one hmetricPosDef
  have hinverse : metric⁻¹ = whitener * whitenerᵀ :=
    inverse_eq_mul_transpose_of_congruence_to_one hwhitenerUnit hwhiten
  have hcomplement :
      subsetSum design (Finset.image pick Finset.univ)ᶜ - 1
        = metric - rowsᵀ * rows := by
    exact complementGap_eq_metric_sub_selectedGram design pick hinjective
  have hsymm : (metric - rowsᵀ * rows)ᵀ = metric - rowsᵀ * rows := by
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      transpose_eq_of_isHermitian hmetricPosDef.1]
  have hcongruence :
      whitenerᵀ * (metric - rowsᵀ * rows) * whitener
        = 1 - (rows * whitener)ᵀ * (rows * whitener) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hwhiten, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have hkernel :
      1 - (rows * whitener) * (rows * whitener)ᵀ
        = complementKernelGap design pick := by
    rw [Matrix.transpose_mul]
    change 1 - rows * whitener * (whitenerᵀ * rowsᵀ)
      = 1 - selectedAtomRows design pick
          * (complementKernelMetric design)⁻¹
          * (selectedAtomRows design pick)ᵀ
    rw [show rows = selectedAtomRows design pick from rfl,
      show (complementKernelMetric design)⁻¹ = whitener * whitenerᵀ from hinverse]
    simp only [Matrix.mul_assoc]
  refine LoewnerEquiv.trans (LoewnerEquiv.of_eq hcomplement) ?_
  refine LoewnerEquiv.trans
    (loewnerEquiv_congr_right hsymm hwhitenerUnit) ?_
  rw [hcongruence]
  refine LoewnerEquiv.trans
    (loewnerEquiv_one_sub_transpose_comm (rows * whitener)) ?_
  exact LoewnerEquiv.of_eq hkernel

/-- Domination of the kept complement is exactly PSD of the kernel gap. -/
theorem dominates_complement_iff_kernel_posSemidef
    (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (pick : Fin omittedSize → Fin size) (hinjective : Function.Injective pick) :
    Dominates design (Finset.image pick Finset.univ)ᶜ
      ↔ (complementKernelGap design pick).PosSemidef :=
  (loewnerEquiv_complementGap_kernel design hsize pick hinjective).1

/-- Strict domination of the kept complement is exactly PD of the kernel gap. -/
theorem posDef_complementGap_iff_kernel_posDef
    (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (pick : Fin omittedSize → Fin size) (hinjective : Function.Injective pick) :
    (subsetSum design (Finset.image pick Finset.univ)ᶜ - 1).PosDef
      ↔ (complementKernelGap design pick).PosDef :=
  (loewnerEquiv_complementGap_kernel design hsize pick hinjective).2

/-- Entrywise, the kernel is the inverse-full-excess pairing of omitted atoms. -/
theorem complementKernel_apply (design : WeightedDesign size rank)
    (pick : Fin omittedSize → Fin size) (first second : Fin omittedSize) :
    complementKernel design pick first second
      = design.atom (pick first) ⬝ᵥ
          ((complementKernelMetric design)⁻¹ *ᵥ design.atom (pick second)) := by
  simp only [complementKernel, selectedAtomRows, Matrix.of_apply,
    Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The first kernel rung is the already-landed full-base pivot. -/
theorem complementKernel_diagonal_eq_pivot
    (design : WeightedDesign size rank) (pick : Fin omittedSize → Fin size)
    (index : Fin omittedSize) :
    complementKernel design pick index index =
      pivot design Finset.univ (pick index) := by
  rw [complementKernel_apply, complementKernelMetric_eq_fullExcess,
    ← pivot_eq_dot]

/-- The inverse-metric kernel is symmetric. -/
theorem complementKernel_transpose (design : WeightedDesign size rank)
    (hsize : 2 ≤ size) (pick : Fin omittedSize → Fin size) :
    (complementKernel design pick)ᵀ = complementKernel design pick := by
  have hinverseSymmetric : ((complementKernelMetric design)⁻¹)ᵀ
      = (complementKernelMetric design)⁻¹ :=
    transpose_eq_of_isHermitian (coParseval_posDef design hsize).inv.1
  rw [complementKernel, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hinverseSymmetric]
  simp only [Matrix.mul_assoc]

/-- The kernel gap is symmetric. -/
theorem complementKernelGap_transpose (design : WeightedDesign size rank)
    (hsize : 2 ≤ size) (pick : Fin omittedSize → Fin size) :
    (complementKernelGap design pick)ᵀ = complementKernelGap design pick := by
  rw [complementKernelGap, Matrix.transpose_sub, Matrix.transpose_one,
    complementKernel_transpose design hsize pick]

/-- **The three welded rungs.**  For an omitted triple, strict domination of its
complement is exactly: the first singleton clearance, the first pair clearance,
and the full triple determinant, all read from one inverse-metric kernel.  An
arbitrary permutation of `pick` puts any desired label and pair in the first two
slots. -/
theorem posDef_complementGap_three_iff_kernel_rungs
    (design : WeightedDesign size 3) (hsize : 2 ≤ size)
    (pick : Fin 3 → Fin size) (hinjective : Function.Injective pick) :
    (subsetSum design (Finset.image pick Finset.univ)ᶜ - 1).PosDef
      ↔ 0 < 1 - complementKernel design pick 0 0
        ∧ 0 < (1 - complementKernel design pick 0 0)
              * (1 - complementKernel design pick 1 1)
            - complementKernel design pick 0 1 ^ 2
        ∧ 0 < (complementKernelGap design pick).det := by
  let gap := complementKernelGap design pick
  have hsymm : gapᵀ = gap := complementKernelGap_transpose design hsize pick
  have hdet :
      gap 0 0 * gap 1 1 * gap 2 2 - gap 0 0 * gap 1 2 ^ 2
          - gap 0 1 ^ 2 * gap 2 2 + 2 * gap 0 1 * gap 0 2 * gap 1 2
          - gap 0 2 ^ 2 * gap 1 1 = gap.det := by
    have h10 : gap 1 0 = gap 0 1 := by
      have hentry := congrFun (congrFun hsymm 0) 1
      simpa only [Matrix.transpose_apply] using hentry
    have h20 : gap 2 0 = gap 0 2 := by
      have hentry := congrFun (congrFun hsymm 0) 2
      simpa only [Matrix.transpose_apply] using hentry
    have h21 : gap 2 1 = gap 1 2 := by
      have hentry := congrFun (congrFun hsymm 1) 2
      simpa only [Matrix.transpose_apply] using hentry
    rw [Matrix.det_fin_three, h10, h20, h21]
    ring
  rw [posDef_complementGap_iff_kernel_posDef design hsize pick hinjective,
    posDef_finThree_iff_leadingMinors gap hsymm, hdet]
  simp only [gap, complementKernelGap, Matrix.sub_apply, Matrix.one_apply,
    if_pos, if_neg (by decide : (0 : Fin 3) ≠ 1), zero_sub,
    neg_sq]

/-- **The weak three-rung weld.**  Domination by the kept complement is exactly
nonnegativity of all seven principal minors of one kernel gap.  Unlike the
strict leading-minor theorem above, this retains singular winners and is the
form relevant to proving `GtzWeighted 6 3` directly. -/
theorem dominates_complement_three_iff_kernel_principal_rungs
    (design : WeightedDesign size 3) (hsize : 2 ≤ size)
    (pick : Fin 3 → Fin size) (hinjective : Function.Injective pick) :
    Dominates design (Finset.image pick Finset.univ)ᶜ
      ↔ 0 ≤ 1 - complementKernel design pick 0 0
        ∧ 0 ≤ 1 - complementKernel design pick 1 1
        ∧ 0 ≤ 1 - complementKernel design pick 2 2
        ∧ complementKernel design pick 0 1 ^ 2
            ≤ (1 - complementKernel design pick 0 0)
              * (1 - complementKernel design pick 1 1)
        ∧ complementKernel design pick 0 2 ^ 2
            ≤ (1 - complementKernel design pick 0 0)
              * (1 - complementKernel design pick 2 2)
        ∧ complementKernel design pick 1 2 ^ 2
            ≤ (1 - complementKernel design pick 1 1)
              * (1 - complementKernel design pick 2 2)
        ∧ 0 ≤ (complementKernelGap design pick).det := by
  let gap := complementKernelGap design pick
  have hsymm : gapᵀ = gap := complementKernelGap_transpose design hsize pick
  have hkernelSymm := complementKernel_transpose design hsize pick
  have hk10 : complementKernel design pick 1 0 = complementKernel design pick 0 1 := by
    have hentry := congrFun (congrFun hkernelSymm 0) 1
    simpa only [Matrix.transpose_apply] using hentry
  have hk20 : complementKernel design pick 2 0 = complementKernel design pick 0 2 := by
    have hentry := congrFun (congrFun hkernelSymm 0) 2
    simpa only [Matrix.transpose_apply] using hentry
  have hk21 : complementKernel design pick 2 1 = complementKernel design pick 1 2 := by
    have hentry := congrFun (congrFun hkernelSymm 1) 2
    simpa only [Matrix.transpose_apply] using hentry
  rw [dominates_complement_iff_kernel_posSemidef design hsize pick hinjective]
  constructor
  · intro hpsd
    have hminor : ∀ (selectionSize : ℕ) (selection : Fin selectionSize → Fin 3),
        (0 : ℝ) ≤ (gap.submatrix selection selection).det :=
      fun _ selection => (hpsd.submatrix selection).det_nonneg
    have hdiagZero := hminor 1 ![0]
    have hdiagOne := hminor 1 ![1]
    have hdiagTwo := hminor 1 ![2]
    have hpairZeroOne := hminor 2 ![0, 1]
    have hpairZeroTwo := hminor 2 ![0, 2]
    have hpairOneTwo := hminor 2 ![1, 2]
    have hdet := hpsd.det_nonneg
    have hdiagZero' : 0 ≤ 1 - complementKernel design pick 0 0 := by
      simpa [gap, complementKernelGap] using hdiagZero
    have hdiagOne' : 0 ≤ 1 - complementKernel design pick 1 1 := by
      simpa [gap, complementKernelGap] using hdiagOne
    have hdiagTwo' : 0 ≤ 1 - complementKernel design pick 2 2 := by
      simpa [gap, complementKernelGap] using hdiagTwo
    have hpairZeroOne' : complementKernel design pick 0 1 ^ 2
        ≤ (1 - complementKernel design pick 0 0)
          * (1 - complementKernel design pick 1 1) := by
      simpa [gap, complementKernelGap, Matrix.det_fin_two, Matrix.one_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        hk10, pow_two] using hpairZeroOne
    have hpairZeroTwo' : complementKernel design pick 0 2 ^ 2
        ≤ (1 - complementKernel design pick 0 0)
          * (1 - complementKernel design pick 2 2) := by
      simpa [gap, complementKernelGap, Matrix.det_fin_two, Matrix.one_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        hk20, pow_two] using hpairZeroTwo
    have hpairOneTwo' : complementKernel design pick 1 2 ^ 2
        ≤ (1 - complementKernel design pick 1 1)
          * (1 - complementKernel design pick 2 2) := by
      simpa [gap, complementKernelGap, Matrix.det_fin_two, Matrix.one_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        hk21, pow_two] using hpairOneTwo
    exact ⟨hdiagZero', hdiagOne', hdiagTwo', hpairZeroOne', hpairZeroTwo', hpairOneTwo', hdet⟩
  · rintro ⟨hdiagZero, hdiagOne, hdiagTwo, hpairZeroOne, hpairZeroTwo,
      hpairOneTwo, hdet⟩
    apply posSemidef_three_of_principalMinors hsymm
    · simpa [gap, complementKernelGap] using hdiagZero
    · simpa [gap, complementKernelGap] using hdiagOne
    · simpa [gap, complementKernelGap] using hdiagTwo
    · simpa [gap, complementKernelGap] using hpairZeroOne
    · simpa [gap, complementKernelGap] using hpairZeroTwo
    · simpa [gap, complementKernelGap] using hpairOneTwo
    · simpa [gap] using hdet

/-! ## The first rung is free at a six-three crux

This is deliberately stated for `SixThreeCrux`, not for an arbitrary tie.  A
crux is the stronger normal form of an actual counterexample and already knows
that every co-singleton strictly dominates.  Transporting that fact through the
kernel weld says that every diagonal clearance is strict.
-/

/-- Every diagonal of every omitted-set kernel is strictly below one at a
`(6,3)` crux.  Thus candidate coherence starts at rung two, not rung one. -/
theorem SixThreeCrux.complementKernel_diagonal_lt_one
    (crux : SixThreeCrux) (pick : Fin omittedSize → Fin 6)
    (index : Fin omittedSize) :
    complementKernel crux.design pick index index < 1 := by
  rw [complementKernel_diagonal_eq_pivot]
  exact (hasStrictlyDominatingCoSingletons_iff_forall_pivot_lt_one
    crux.design (by norm_num)).mp crux.hasStrictlyDominatingCoSingletons (pick index)

/-! ## The exact remaining selector

At a crux the singleton clauses of the weak three-rung weld are automatic.  The
remaining data are therefore an edge condition on each of the three pairs and
one determinant condition on the triangle.  This packages the actual residual
without choosing an ordering-dependent descent path.
-/

/-- The `2 x 2` principal-minor clearance of an inverse-metric kernel pair. -/
noncomputable def complementKernelPairClearance
    (design : WeightedDesign size 3) (pick : Fin omittedSize → Fin size)
    (first second : Fin omittedSize) : ℝ :=
  (1 - complementKernel design pick first first)
      * (1 - complementKernel design pick second second)
    - complementKernel design pick first second ^ 2

/-- A good kernel triangle at a `(6,3)` crux: its three edges pass the weak
second rung and its full determinant passes the weak third rung.  The three
first-rung inequalities are omitted because they are strict at every crux. -/
def IsGoodCruxKernelTriangle (crux : SixThreeCrux) (pick : Fin 3 → Fin 6) : Prop :=
  Function.Injective pick
    ∧ 0 ≤ complementKernelPairClearance crux.design pick 0 1
    ∧ 0 ≤ complementKernelPairClearance crux.design pick 0 2
    ∧ 0 ≤ complementKernelPairClearance crux.design pick 1 2
    ∧ 0 ≤ (complementKernelGap crux.design pick).det

/-- A crux cannot contain a good kernel triangle: the weak principal-minor weld
would turn its kept complement into a dominating triple. -/
theorem SixThreeCrux.not_isGoodCruxKernelTriangle
    (crux : SixThreeCrux) (pick : Fin 3 → Fin 6) :
    ¬ IsGoodCruxKernelTriangle crux pick := by
  rintro ⟨hinjective, hpairZeroOne, hpairZeroTwo, hpairOneTwo, hdet⟩
  have hdiagZero : 0 ≤ 1 - complementKernel crux.design pick 0 0 :=
    le_of_lt (sub_pos.mpr (crux.complementKernel_diagonal_lt_one pick 0))
  have hdiagOne : 0 ≤ 1 - complementKernel crux.design pick 1 1 :=
    le_of_lt (sub_pos.mpr (crux.complementKernel_diagonal_lt_one pick 1))
  have hdiagTwo : 0 ≤ 1 - complementKernel crux.design pick 2 2 :=
    le_of_lt (sub_pos.mpr (crux.complementKernel_diagonal_lt_one pick 2))
  have hpairZeroOne' : complementKernel crux.design pick 0 1 ^ 2
      ≤ (1 - complementKernel crux.design pick 0 0)
        * (1 - complementKernel crux.design pick 1 1) := by
    simpa only [complementKernelPairClearance, sub_nonneg] using hpairZeroOne
  have hpairZeroTwo' : complementKernel crux.design pick 0 2 ^ 2
      ≤ (1 - complementKernel crux.design pick 0 0)
        * (1 - complementKernel crux.design pick 2 2) := by
    simpa only [complementKernelPairClearance, sub_nonneg] using hpairZeroTwo
  have hpairOneTwo' : complementKernel crux.design pick 1 2 ^ 2
      ≤ (1 - complementKernel crux.design pick 1 1)
        * (1 - complementKernel crux.design pick 2 2) := by
    simpa only [complementKernelPairClearance, sub_nonneg] using hpairOneTwo
  have hdominates :
      Dominates crux.design (Finset.image pick Finset.univ)ᶜ := by
    apply (dominates_complement_three_iff_kernel_principal_rungs
      crux.design (by norm_num) pick hinjective).mpr
    exact ⟨hdiagZero, hdiagOne, hdiagTwo, hpairZeroOne', hpairZeroTwo',
      hpairOneTwo', hdet⟩
  have hcard : ((Finset.image pick Finset.univ)ᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, Finset.card_image_of_injective _ hinjective,
      Finset.card_univ, Fintype.card_fin]
    norm_num
  exact crux.hasNoDominatingTriple _ hcard hdominates

/-- The graph-plus-determinant selector which remains after welding the three
descent rungs.  It is deliberately quantified only over the exact counterexample
normal form, so all first-order, heaviness, dual-deflation, and compactness data
available on `SixThreeCrux` remain usable in its proof. -/
def CruxKernelTriangleSelection : Prop :=
  ∀ crux : SixThreeCrux, ∃ pick : Fin 3 → Fin 6,
    IsGoodCruxKernelTriangle crux pick

/-- **A RESTATEMENT, NOT A REDUCTION.**  Selecting a good triangle in the
complement kernel of every hypothetical crux is equivalent to weighted GTZ at
`(6,3)`.  The equivalence is LOSSLESS AND DISCHARGES NOTHING: the left side
unwinds to "no crux exists", which is the target itself.  Good triangle iff the
complement weakly dominates iff a crux has a dominating triple iff no crux
exists; and the reverse direction is vacuous, since `GtzWeighted 6 3` empties
the family the selection quantifies over.  Its value is the CHANGE OF
COORDINATES above -- one inverse-metric kernel, first rung free -- not any
reduction in the open content. -/
theorem cruxKernelTriangleSelection_iff_gtzWeighted_six_three :
    CruxKernelTriangleSelection ↔ GtzWeighted 6 3 := by
  constructor
  · intro hselection
    apply gtzWeighted_six_three_of_isEmpty_sixThreeCrux
    refine ⟨fun crux => ?_⟩
    obtain ⟨pick, hgood⟩ := hselection crux
    exact crux.not_isGoodCruxKernelTriangle pick hgood
  · intro hgtz crux
    exact False.elim (not_gtzWeighted_six_three_of_sixThreeCrux crux hgtz)

end Gtz
