/-
# The circuit swap law: a dominating triple prices every one-atom swap

`Gtz/Wave/DependencyDominationCriterion.lean` reads domination off the linear
DEPENDENCIES of the atoms.  For a `k`-subset `C` of a weighted design,

    Dominates D C  <->  for every `z` with `sum_c z_c g_c = 0` ,
      `sum_{c in C} z_c^2/(1 - t_c)  <=  sum_{c not in C} z_c^2/t_c` .

At `(6,3)` the dependency space is THREE-dimensional and the twenty triples give
twenty comparisons of quadratic forms on that one small space.  No lane has ever
written those comparisons down.  This module does, at the dependencies that
Cramer supplies for free.

## 1. The circuit

Four vectors of `R^3` are dependent with the four omitted brackets as
coefficients (`Gtz.tripleBracket_cramer`).  `Gtz.circuitDep` spreads that
relation over the label set: it is supported on four labels and it is a genuine
dependency of the design (`Gtz.sum_circuitDep_smul_atom`).  Feeding it to the
criterion at a triple `C = {a,b,c}` contained in the four-set makes the RIGHT
side a SINGLE term, because only one label of the support lies outside `C`.

## 2. The law

  **`Gtz.swapLaw_of_dominates`.**  If `{a,b,c}` dominates and `d` is any fourth
  label, then

      `[bcd]^2/(1 - t_a) + [acd]^2/(1 - t_b) + [abd]^2/(1 - t_c)  <=  [abc]^2/t_d` .

Every quantity is a bracket of the design and a weight.  In the volume currency
of `Gtz/Wave/TwentyVolumeMarginals.lean`, multiplying by `t_a t_b t_c t_d` turns
it into a relation among four of the twenty triple masses,

  **`Gtz.swapLaw_volume_of_dominates`:**
      `th_a nu_bcd + th_b nu_acd + th_c nu_abd  <=  nu_abc` ,  `th_x = t_x/(1 - t_x)` .

A dominating triple's own mass dominates the masses of the three triples got by
SWAPPING one of its members for `d`, each discounted by the odds of the member
that leaves.  Reading one term at a time gives `t_d [bcd]^2 <= (1 - t_a) [abc]^2`
(`Gtz.swapLaw_single_of_dominates`), and dropping the discounts gives the
one-weight form `t_d ([bcd]^2 + [acd]^2 + [abd]^2) <= [abc]^2`
(`Gtz.swapLaw_plain_of_dominates`).

## 3. The aggregate at `(6,3)`

At `(6,3)` the complement of a dominating triple is again a triple, so the law
fires three times.  Summing and spending the landed two-point marginal
`sum_r nu_pqr = delta_pq` collapses the nine swapped masses onto the three pair
masses INSIDE the dominator:

  **`Gtz.corner_free_aggregate_of_dominates_sixThree`:**
      `th_a delta_bc + th_b delta_ac + th_c delta_ab  <=  (3 + th_a + th_b + th_c) nu_abc` .

This is the trace reading of the criterion at the dominator, and it is the first
statement the campaign has that couples the pair layer of
`Gtz/Wave/TwentyVolumeMarginals.lean` to the triple layer through DOMINATION
rather than through Hadamard.

## 4. The second circuit family: the pair swap

The circuit of a four-set that meets the dominator in a PAIR leaves TWO terms on
each side, and no third member of the dominator survives at all:

  **`Gtz.pairSwapLaw_of_dominates`.**  If `{a,b,c}` dominates and `d`, `e` are
  two further labels, then

      `[bde]^2/(1 - t_a) + [ade]^2/(1 - t_b) <= [abe]^2/t_d + [abd]^2/t_e` ,

which in volume currency (`Gtz.pairSwapLaw_volume_of_dominates`) is

      `th_a nu_bde + th_b nu_ade  <=  nu_abd + nu_abe` ,

with NO weight on the right.  The two triples that keep one member of `{a,b}` and
take both outside labels are dominated by the two that keep the pair `{a,b}` and
take one outside label.  The third member `c` enters only through the domination
hypothesis.  Dropping the odds to the weights themselves gives the one-sided
`Gtz.pairSwapLaw_weight_of_dominates`.

## 5. The strict criterion, and the tie

The landed criterion is stated weakly only.  Part 1 lands the strict twin at a
symmetric idempotent (`Gtz.posDef_diagonal_sub_block_iff_kernelBound`) and at a
design (`Gtz.posDef_gap_iff_dependencyBound_compl`).  Its contrapositive is the
tie, in dependency currency:

  **`Gtz.exists_dependency_reversal_of_isTie`** — at a tie EVERY `k`-subset
  admits a NONZERO dependency at which the criterion reverses.

At `(6,3)` that is twenty vectors of one three-dimensional space, one per triple.

[MEASURED before proving, in double precision, `scratchpad/circuit`.  Over
200000 random `(6,3)` designs and all 4000000 triples the criterion agreed with
domination with ZERO mismatches, weakly AND strictly.  The swap law was tested
at 829894 dominating triples times three outside labels with ZERO violations and
worst relative excess `0`.  It is SHARP: over a second run of 400000 designs and
1663068 dominating triples the largest value of the ratio
`lhs/rhs` is `0.999088`.  It is strictly WEAKER than domination: 267296 of
1097190 triples passing all three swap conditions do not dominate, so the law is
the DIAGONAL of the criterion and not the criterion.  The aggregate of part 3
reaches `0.867` and the determinant reading `nu_{C'} th_a th_b th_c <= nu_C`
reaches `0.441`, both with zero violations.  The pair-swap law of part 4 was
tested at 3739563 instances of a dominating triple against an inside pair and an
outside pair, again with ZERO violations, and it is sharp too: the largest ratio
is `0.998715`.

Calibration on the `(5,3)` diamond: Parseval residual `2.2e-16`, maximum over
triples of `lambda_min(S_T - 1)` equal to `-8.3e-17` so an exact tie, shares
`(0.4, 0.65, 0.65, 0.65, 0.65)`, maximum `cos^2` over pairs `0.29` so no
parallel pair, EIGHT dominating triples and every one of corank exactly one.
The swap law there has maximum ratio exactly `0.750000` over all eight
dominators and all outside labels, so it is NOT tight at that tie.]
-/
import Gtz.Wave.DependencyDominationCriterion
import Gtz.Wave.TwentyVolumeMarginals
import Gtz.Wave.TieParallelPairWeightRegular
import Gtz.Reduction.PolarCrossWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1 — the strict block-versus-kernel criterion

The landed `Gtz.posSemidef_diagonal_sub_block_iff_kernelBound` is weak only.  Its
strict twin runs the same two Cauchy-Schwarz steps and needs one extra case
split, on whether the vector under test survives the idempotent. -/

/-- Positive definiteness of a symmetric real matrix is exactly strict positivity
of its quadratic form off the origin. -/
theorem posDef_iff_quadForm_pos {dim : ℕ} (gapMatrix : Matrix (Fin dim) (Fin dim) ℝ)
    (hsymm : gapMatrixᵀ = gapMatrix) :
    gapMatrix.PosDef ↔ ∀ testVec : Fin dim → ℝ, testVec ≠ 0 →
      0 < testVec ⬝ᵥ (gapMatrix *ᵥ testVec) := by
  constructor
  · intro hposDef testVec hne
    have hvalue := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hne
    rwa [star_trivial] at hvalue
  · intro hquad
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hsymm, fun testVec hne => ?_⟩
    rw [star_trivial]
    exact hquad testVec hne

/-- **THE STRICT BLOCK-VERSUS-KERNEL CRITERION.**  For a symmetric idempotent
`Q`, a positive `scale` and any index map, the block inequality
`diag scale > Q[pick, pick]` says exactly that every NONZERO vector fixed by `Q`
spends STRICTLY less than its own square mass on the selected coordinates.

The forward direction splits on whether the selected part of the fixed vector
vanishes, the backward direction on whether the idempotent kills the spread of
the test vector.  Everything else is the same pair of Cauchy-Schwarz steps that
the weak twin runs. -/
theorem posDef_diagonal_sub_block_iff_kernelBound {ambient size : ℕ}
    {form : Matrix (Fin ambient) (Fin ambient) ℝ}
    (hsymm : formᵀ = form) (hidem : form * form = form)
    (pick : Fin size → Fin ambient) {scale : Fin size → ℝ}
    (hscale : ∀ slot, 0 < scale slot) :
    (Matrix.diagonal scale - form.submatrix pick pick).PosDef
      ↔ ∀ probe : Fin ambient → ℝ, form *ᵥ probe = probe → probe ≠ 0 →
          ∑ slot, probe (pick slot) ^ 2 / scale slot < ∑ index, probe index ^ 2 := by
  have hblockSymm : (Matrix.diagonal scale - form.submatrix pick pick)ᵀ
      = Matrix.diagonal scale - form.submatrix pick pick := by
    rw [Matrix.transpose_sub, Matrix.diagonal_transpose, Matrix.transpose_submatrix, hsymm]
  have hdiagForm : ∀ selected : Fin size → ℝ,
      selected ⬝ᵥ (Matrix.diagonal scale *ᵥ selected)
        = ∑ slot, scale slot * selected slot ^ 2 := by
    intro selected
    rw [dotProduct]
    exact Finset.sum_congr rfl fun slot _ => by rw [Matrix.mulVec_diagonal]; ring
  rw [posDef_iff_quadForm_pos _ hblockSymm]
  constructor
  · -- the strict block inequality gives the strict kernel bound
    intro hblock probe hfix hne
    set total : ℝ := ∑ slot, probe (pick slot) ^ 2 / scale slot with htotal
    have htotalNonneg : 0 ≤ total :=
      Finset.sum_nonneg fun slot _ => div_nonneg (sq_nonneg _) (hscale slot).le
    have hmass : 0 < ∑ index, probe index ^ 2 := by
      obtain ⟨badIndex, hbad⟩ := Function.ne_iff.mp hne
      refine Finset.sum_pos' (fun index _ => sq_nonneg _) ⟨badIndex, Finset.mem_univ _, ?_⟩
      exact pow_pos (abs_pos.mpr hbad) 2 |>.trans_le (le_of_eq (sq_abs _))
    rcases eq_or_lt_of_le htotalNonneg with hzero | hpos
    · rw [← hzero]; exact hmass
    -- the selected part of the fixed vector is nonzero, so the block form fires
    set selected : Fin size → ℝ := fun slot => probe (pick slot) / scale slot with hselected
    have hselNe : selected ≠ 0 := by
      intro hzeroSel
      have hallzero : total = 0 := by
        rw [htotal]
        refine Finset.sum_eq_zero fun slot _ => ?_
        have hslot : probe (pick slot) / scale slot = 0 := congrFun hzeroSel slot
        have hnum : probe (pick slot) = 0 := by
          have := (div_eq_zero_iff).mp hslot
          rcases this with hgood | hbad
          · exact hgood
          · exact absurd hbad (hscale slot).ne'
        rw [hnum]; simp
      rw [hallzero] at hpos; exact lt_irrefl 0 hpos
    have hdiagValue : selected ⬝ᵥ (Matrix.diagonal scale *ᵥ selected) = total := by
      rw [hdiagForm, htotal]
      refine Finset.sum_congr rfl fun slot _ => ?_
      simp only [hselected]
      field_simp
      try ring
    have hblockValue : selected ⬝ᵥ ((form.submatrix pick pick) *ᵥ selected) < total := by
      have hstep := hblock selected hselNe
      rw [Matrix.sub_mulVec, dotProduct_sub, hdiagValue] at hstep
      linarith
    set spread := dependencySpread pick selected with hspread
    have hspreadQuad : spread ⬝ᵥ (form *ᵥ spread) < total := by
      rw [hspread, dependencySpread_quadForm]; exact hblockValue
    have hpair : ∑ index, (form *ᵥ spread) index * probe index = total := by
      have hcomm : probe ⬝ᵥ (form *ᵥ spread) = spread ⬝ᵥ (form *ᵥ probe) :=
        dot_mulVec_comm hsymm probe spread
      have hleft : ∑ index, (form *ᵥ spread) index * probe index
          = probe ⬝ᵥ (form *ᵥ spread) := by
        rw [dotProduct]
        exact Finset.sum_congr rfl fun index _ => mul_comm _ _
      rw [hleft, hcomm, hfix, dotProduct, hspread,
        dependencySpread_transfer pick selected probe, htotal]
      refine Finset.sum_congr rfl fun slot _ => ?_
      simp only [hselected]
      field_simp
      try ring
    have hnormSq : ∑ index, ((form *ᵥ spread) index) ^ 2 = spread ⬝ᵥ (form *ᵥ spread) := by
      have hsquare : (form *ᵥ spread) ⬝ᵥ (form *ᵥ spread) = spread ⬝ᵥ (form *ᵥ spread) := by
        have hcomm : (form *ᵥ spread) ⬝ᵥ (form *ᵥ spread)
            = spread ⬝ᵥ (form *ᵥ (form *ᵥ spread)) :=
          dot_mulVec_comm hsymm (form *ᵥ spread) spread
        rw [hcomm, Matrix.mulVec_mulVec, hidem]
      rw [← hsquare, dotProduct]
      simp [pow_two]
    have hCS := sum_mul_sq_le Finset.univ (form *ᵥ spread) probe
    rw [hpair, hnormSq] at hCS
    nlinarith [hCS, hspreadQuad, hpos, hmass]
  · -- the strict kernel bound gives the strict block inequality
    intro hkernel selected hselNe
    set spread := dependencySpread pick selected with hspread
    set image : Fin ambient → ℝ := form *ᵥ spread with himage
    have hfix : form *ᵥ image = image := by
      rw [himage, Matrix.mulVec_mulVec, hidem]
    set gap : ℝ := spread ⬝ᵥ (form *ᵥ spread) with hgap
    have hgapBlock : gap = selected ⬝ᵥ ((form.submatrix pick pick) *ᵥ selected) := by
      rw [hgap, hspread, dependencySpread_quadForm]
    have hnormSq : ∑ index, image index ^ 2 = gap := by
      have hsquare : image ⬝ᵥ image = gap := by
        have hcomm : image ⬝ᵥ image = spread ⬝ᵥ (form *ᵥ image) :=
          himage ▸ dot_mulVec_comm hsymm (form *ᵥ spread) spread
        rw [hcomm, himage, Matrix.mulVec_mulVec, hidem, hgap]
      rw [← hsquare, dotProduct]
      simp [pow_two]
    have hscaleSum : 0 < ∑ slot, scale slot * selected slot ^ 2 := by
      obtain ⟨badSlot, hbad⟩ := Function.ne_iff.mp hselNe
      refine Finset.sum_pos' (fun slot _ => mul_nonneg (hscale slot).le (sq_nonneg _))
        ⟨badSlot, Finset.mem_univ _, ?_⟩
      have hsq : 0 < selected badSlot ^ 2 := by
        have := abs_pos.mpr hbad
        nlinarith [sq_abs (selected badSlot), this]
      exact mul_pos (hscale badSlot) hsq
    rw [Matrix.sub_mulVec, dotProduct_sub, hdiagForm, ← hgapBlock]
    by_cases hzeroImage : image = 0
    · have hgapZero : gap = 0 := by
        rw [← hnormSq, hzeroImage]; simp
      rw [hgapZero]; linarith
    · have hgapPos : 0 < gap := by
        rw [← hnormSq]
        obtain ⟨badIndex, hbad⟩ := Function.ne_iff.mp hzeroImage
        refine Finset.sum_pos' (fun index _ => sq_nonneg _) ⟨badIndex, Finset.mem_univ _, ?_⟩
        have := abs_pos.mpr hbad
        nlinarith [sq_abs (image badIndex), this]
      have hpair : ∑ slot, selected slot * image (pick slot) = gap := by
        rw [hgap, dotProduct, hspread]
        exact (dependencySpread_transfer pick selected (form *ᵥ spread)).symm
      have hbound : ∑ slot, image (pick slot) ^ 2 / scale slot < gap := by
        have := hkernel image hfix hzeroImage
        rw [hnormSq] at this
        exact this
      have hCS := sum_mul_sq_le Finset.univ
        (fun slot => Real.sqrt (scale slot) * selected slot)
        (fun slot => image (pick slot) / Real.sqrt (scale slot))
      have hmix : ∀ slot : Fin size,
          (Real.sqrt (scale slot) * selected slot) * (image (pick slot) / Real.sqrt (scale slot))
            = selected slot * image (pick slot) := by
        intro slot
        have hne : Real.sqrt (scale slot) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hscale slot))
        field_simp
        try ring
      have hleftSq : ∀ slot : Fin size,
          (Real.sqrt (scale slot) * selected slot) ^ 2 = scale slot * selected slot ^ 2 := by
        intro slot
        rw [mul_pow, Real.sq_sqrt (hscale slot).le]
      have hrightSq : ∀ slot : Fin size,
          (image (pick slot) / Real.sqrt (scale slot)) ^ 2
            = image (pick slot) ^ 2 / scale slot := by
        intro slot
        rw [div_pow, Real.sq_sqrt (hscale slot).le]
      rw [Finset.sum_congr rfl fun slot _ => hmix slot,
        Finset.sum_congr rfl fun slot _ => hleftSq slot,
        Finset.sum_congr rfl fun slot _ => hrightSq slot, hpair] at hCS
      nlinarith [hCS, hbound, hgapPos, hscaleSum]

/-! ## Part 2 — the strict criterion at a design

The transport is the landed one, verbatim: the strict block criterion of
`Gtz/Wave/TieParallelPairWeightRegular.lean`, the landed rewriting of the
projection block as a co-projection block, and the landed identification of the
fixed vectors of `1 - P` with the dependencies. -/

/-- **STRICT DOMINATION IS A STRICT KERNEL BOUND.** -/
theorem posDef_gap_iff_kernelBound (D : WeightedDesign m k) (hm : 2 ≤ m)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef
      ↔ ∀ probe : Fin m → ℝ, (scaledAtomRows D)ᵀ *ᵥ probe = 0 → probe ≠ 0 →
          ∑ slot, probe (pick slot) ^ 2 / (1 - D.weight (pick slot))
            < ∑ index, probe index ^ 2 := by
  have hscale : ∀ slot : Fin k, 0 < 1 - D.weight (pick slot) := fun slot => by
    linarith [weight_lt_one D hm (pick slot)]
  rw [posDef_gap_iff_posDef_projectionBlock D pick hinj,
    projectionBlock_gap_eq_coProjection_gap D pick hinj,
    posDef_diagonal_sub_block_iff_kernelBound (coProjectionForm_transpose D)
      (coProjectionForm_mul_self D) pick hscale]
  exact forall_congr' fun probe => by rw [mulVec_coProjection_self_iff]

/-- **STRICT DOMINATION IS A STRICT DEPENDENCY BOUND.**  The strict twin of
`Gtz.dominates_iff_dependencyBound`. -/
theorem posDef_gap_iff_dependencyBound (D : WeightedDesign m k) (hm : 2 ≤ m)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef
      ↔ ∀ dep : Fin m → ℝ, dep ≠ 0 → (∑ index, dep index • D.atom index) = 0 →
          ∑ slot, dep (pick slot) ^ 2
              / (D.weight (pick slot) * (1 - D.weight (pick slot)))
            < ∑ index, dep index ^ 2 / D.weight index := by
  have hsqrtPos : ∀ index : Fin m, 0 < Real.sqrt (D.weight index) := fun index =>
    Real.sqrt_pos.mpr (D.weight_pos index)
  have hsq : ∀ index : Fin m, Real.sqrt (D.weight index) ^ 2 = D.weight index := fun index =>
    Real.sq_sqrt (D.weight_pos index).le
  rw [posDef_gap_iff_kernelBound D hm pick hinj]
  constructor
  · intro hkernel dep hdepNe hdep
    have hzero : (scaledAtomRows D)ᵀ *ᵥ (fun index => dep index / Real.sqrt (D.weight index))
        = 0 := by
      rw [transpose_scaledAtomRows_mulVec_eq_zero_iff, ← hdep]
      refine Finset.sum_congr rfl fun index _ => ?_
      have hne : Real.sqrt (D.weight index) ≠ 0 := (hsqrtPos index).ne'
      congr 1
      field_simp
    have hscaledNe : (fun index => dep index / Real.sqrt (D.weight index)) ≠ 0 := by
      obtain ⟨badIndex, hbad⟩ := Function.ne_iff.mp hdepNe
      refine Function.ne_iff.mpr ⟨badIndex, ?_⟩
      simp only [Pi.zero_apply]
      exact div_ne_zero hbad (hsqrtPos badIndex).ne'
    have hstep := hkernel _ hzero hscaledNe
    calc ∑ slot, dep (pick slot) ^ 2
            / (D.weight (pick slot) * (1 - D.weight (pick slot)))
        = ∑ slot, (dep (pick slot) / Real.sqrt (D.weight (pick slot))) ^ 2
            / (1 - D.weight (pick slot)) := by
          refine Finset.sum_congr rfl fun slot _ => ?_
          rw [div_pow, hsq, div_div]
      _ < ∑ index, (dep index / Real.sqrt (D.weight index)) ^ 2 := hstep
      _ = ∑ index, dep index ^ 2 / D.weight index := by
          refine Finset.sum_congr rfl fun index _ => ?_
          rw [div_pow, hsq]
  · intro hdepBound probe hprobe hprobeNe
    have hdep : (∑ index, (Real.sqrt (D.weight index) * probe index) • D.atom index) = 0 :=
      (transpose_scaledAtomRows_mulVec_eq_zero_iff D probe).mp hprobe
    have hdepNe : (fun index => Real.sqrt (D.weight index) * probe index) ≠ 0 := by
      obtain ⟨badIndex, hbad⟩ := Function.ne_iff.mp hprobeNe
      refine Function.ne_iff.mpr ⟨badIndex, ?_⟩
      simp only [Pi.zero_apply]
      exact mul_ne_zero (hsqrtPos badIndex).ne' hbad
    have hstep := hdepBound _ hdepNe hdep
    calc ∑ slot, probe (pick slot) ^ 2 / (1 - D.weight (pick slot))
        = ∑ slot, (Real.sqrt (D.weight (pick slot)) * probe (pick slot)) ^ 2
            / (D.weight (pick slot) * (1 - D.weight (pick slot))) := by
          refine Finset.sum_congr rfl fun slot _ => ?_
          rw [mul_pow, hsq, mul_div_mul_left _ _ (D.weight_pos (pick slot)).ne']
      _ < ∑ index, (Real.sqrt (D.weight index) * probe index) ^ 2 / D.weight index := hstep
      _ = ∑ index, probe index ^ 2 := by
          refine Finset.sum_congr rfl fun index _ => ?_
          rw [mul_pow, hsq, mul_comm, mul_div_assoc, div_self (D.weight_pos index).ne',
            mul_one]

/-- **THE SPLIT IDENTITY.**  Moving the selected part of the ambient sum across
turns `1/(t_c(1 - t_c)) - 1/t_c` into `1/(1 - t_c)`, at every dependency vector
and with no inequality anywhere.  Both the landed weak criterion and the strict
one of this module are this identity plus `linarith`. -/
theorem dependencyBound_split (D : WeightedDesign m k) (hm : 2 ≤ m)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) (dep : Fin m → ℝ) :
    (∑ slot, dep (pick slot) ^ 2
          / (D.weight (pick slot) * (1 - D.weight (pick slot))))
        - ∑ index, dep index ^ 2 / D.weight index
      = (∑ index ∈ Finset.image pick Finset.univ, dep index ^ 2 / (1 - D.weight index))
        - ∑ index ∈ (Finset.image pick Finset.univ)ᶜ, dep index ^ 2 / D.weight index := by
  classical
  set selection : Finset (Fin m) := Finset.image pick Finset.univ with hselection
  have himage : ∀ f : Fin m → ℝ, ∑ index ∈ selection, f index = ∑ slot, f (pick slot) := by
    intro f
    rw [hselection, Finset.sum_image fun left _ right _ hpick => hinj hpick]
  have hsplit : ∑ index, dep index ^ 2 / D.weight index
      = (∑ index ∈ selection, dep index ^ 2 / D.weight index)
        + ∑ index ∈ selectionᶜ, dep index ^ 2 / D.weight index :=
    (Finset.sum_add_sum_compl selection _).symm
  have hgap : ∀ slot : Fin k,
      dep (pick slot) ^ 2 / (D.weight (pick slot) * (1 - D.weight (pick slot)))
          - dep (pick slot) ^ 2 / D.weight (pick slot)
        = dep (pick slot) ^ 2 / (1 - D.weight (pick slot)) := by
    intro slot
    have hw : D.weight (pick slot) ≠ 0 := (D.weight_pos (pick slot)).ne'
    have hco : (1 : ℝ) - D.weight (pick slot) ≠ 0 := by
      have := weight_lt_one D hm (pick slot); intro hzero; linarith [hzero]
    field_simp
    ring
  have hleft : (∑ slot, dep (pick slot) ^ 2
          / (D.weight (pick slot) * (1 - D.weight (pick slot))))
        - ∑ index ∈ selection, dep index ^ 2 / D.weight index
      = ∑ index ∈ selection, dep index ^ 2 / (1 - D.weight index) := by
    rw [himage (fun index => dep index ^ 2 / D.weight index),
      himage (fun index => dep index ^ 2 / (1 - D.weight index)), ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun slot _ => hgap slot
  rw [hsplit]
  linarith [hleft]

/-- **STRICT DOMINATION, WITH THE SELECTION AND ITS COMPLEMENT ON OPPOSITE
SIDES.**  The strict twin of `Gtz.dominates_iff_dependencyBound_compl`. -/
theorem posDef_gap_iff_dependencyBound_compl (D : WeightedDesign m k) (hm : 2 ≤ m)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef
      ↔ ∀ dep : Fin m → ℝ, dep ≠ 0 → (∑ index, dep index • D.atom index) = 0 →
          ∑ index ∈ Finset.image pick Finset.univ, dep index ^ 2 / (1 - D.weight index)
            < ∑ index ∈ (Finset.image pick Finset.univ)ᶜ, dep index ^ 2 / D.weight index := by
  rw [posDef_gap_iff_dependencyBound D hm pick hinj]
  refine forall_congr' fun dep => forall_congr' fun _ => forall_congr' fun _ => ?_
  have hsplit := dependencyBound_split D hm pick hinj dep
  constructor
  · intro hbound; linarith
  · intro hbound; linarith

/-- **THE TIE, IN DEPENDENCY CURRENCY.**  A tie carries no strictly dominating
`k`-subset, so EVERY `k`-subset admits a nonzero dependency at which the
criterion reverses.  At `(6,3)` that is twenty vectors of one three-dimensional
space, one for each triple, and no design datum other than the weights and the
dependency space appears. -/
theorem exists_dependency_reversal_of_isTie (D : WeightedDesign m k) (hm : 2 ≤ m)
    (htie : IsTie D) (pick : Fin k → Fin m) (hinj : Function.Injective pick) :
    ∃ dep : Fin m → ℝ, dep ≠ 0 ∧ (∑ index, dep index • D.atom index) = 0
      ∧ ∑ index ∈ (Finset.image pick Finset.univ)ᶜ, dep index ^ 2 / D.weight index
        ≤ ∑ index ∈ Finset.image pick Finset.univ, dep index ^ 2 / (1 - D.weight index) := by
  classical
  have hcard : (Finset.image pick Finset.univ).card = k := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hnot := htie.2 (Finset.image pick Finset.univ) hcard
  rw [posDef_gap_iff_dependencyBound_compl D hm pick hinj] at hnot
  push Not at hnot
  obtain ⟨dep, hdepNe, hdep, hrev⟩ := hnot
  exact ⟨dep, hdepNe, hdep, hrev⟩

/-! ## Part 3 — the circuit dependency

Four vectors of `R^3` are dependent and the coefficients are the four omitted
brackets.  `Gtz.tripleBracket_cramer` is landed; what is new is spreading it
over the label set of a design so that the criterion can eat it. -/

/-- A single-label vector pairs against the atoms by reading one atom. -/
theorem sum_piSingle_smul_atom (D : WeightedDesign m 3) (label : Fin m) (value : ℝ) :
    ∑ index, (Pi.single label value : Fin m → ℝ) index • D.atom index
      = value • D.atom label := by
  classical
  rw [Finset.sum_eq_single label]
  · rw [Pi.single_eq_same]
  · intro other _ hne
    rw [Pi.single_eq_of_ne hne, zero_smul]
  · intro hnot
    exact absurd (Finset.mem_univ label) hnot

/-- **THE CIRCUIT OF A FOUR-SET.**  The Cramer dependency of four labels,
spread over the whole label set: it is supported on `{a,b,c,d}` and its four
coefficients are the four omitted brackets. -/
noncomputable def circuitDep (D : WeightedDesign m 3) (a b c d : Fin m) : Fin m → ℝ :=
  Pi.single a (tripleBracket (D.atom b) (D.atom c) (D.atom d))
    + Pi.single b (-(tripleBracket (D.atom a) (D.atom c) (D.atom d)))
    + Pi.single c (tripleBracket (D.atom a) (D.atom b) (D.atom d))
    + Pi.single d (-(tripleBracket (D.atom a) (D.atom b) (D.atom c)))

/-- **THE CIRCUIT IS A DEPENDENCY.**  One reading of the landed Cramer law. -/
theorem sum_circuitDep_smul_atom (D : WeightedDesign m 3) (a b c d : Fin m) :
    (∑ index, circuitDep D a b c d index • D.atom index) = 0 := by
  classical
  have hexpand : ∀ index : Fin m, circuitDep D a b c d index • D.atom index
      = (Pi.single a (tripleBracket (D.atom b) (D.atom c) (D.atom d)) : Fin m → ℝ) index
          • D.atom index
        + (Pi.single b (-(tripleBracket (D.atom a) (D.atom c) (D.atom d))) : Fin m → ℝ) index
          • D.atom index
        + (Pi.single c (tripleBracket (D.atom a) (D.atom b) (D.atom d)) : Fin m → ℝ) index
          • D.atom index
        + (Pi.single d (-(tripleBracket (D.atom a) (D.atom b) (D.atom c))) : Fin m → ℝ) index
          • D.atom index := by
    intro index
    rw [circuitDep]
    simp only [Pi.add_apply, add_smul]
  rw [Finset.sum_congr rfl fun index _ => hexpand index]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_piSingle_smul_atom, sum_piSingle_smul_atom, sum_piSingle_smul_atom,
    sum_piSingle_smul_atom]
  have hcramer := tripleBracket_cramer (D.atom a) (D.atom b) (D.atom c) (D.atom d)
  rw [neg_smul, neg_smul]
  rw [← hcramer]
  abel

/-- Off the four labels of its four-set the circuit vanishes. -/
theorem circuitDep_apply_of_notMem (D : WeightedDesign m 3) {a b c d x : Fin m}
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hxd : x ≠ d) :
    circuitDep D a b c d x = 0 := by
  classical
  rw [circuitDep]
  simp only [Pi.add_apply, Pi.single_eq_of_ne hxa, Pi.single_eq_of_ne hxb,
    Pi.single_eq_of_ne hxc, Pi.single_eq_of_ne hxd]
  ring

theorem circuitDep_apply_first (D : WeightedDesign m 3) {a b c d : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    circuitDep D a b c d a = tripleBracket (D.atom b) (D.atom c) (D.atom d) := by
  classical
  rw [circuitDep]
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab, Pi.single_eq_of_ne hac,
    Pi.single_eq_of_ne had]
  ring

theorem circuitDep_apply_second (D : WeightedDesign m 3) {a b c d : Fin m}
    (hab : a ≠ b) (hbc : b ≠ c) (hbd : b ≠ d) :
    circuitDep D a b c d b = -(tripleBracket (D.atom a) (D.atom c) (D.atom d)) := by
  classical
  rw [circuitDep]
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hab),
    Pi.single_eq_of_ne hbc, Pi.single_eq_of_ne hbd]
  ring

theorem circuitDep_apply_third (D : WeightedDesign m 3) {a b c d : Fin m}
    (hac : a ≠ c) (hbc : b ≠ c) (hcd : c ≠ d) :
    circuitDep D a b c d c = tripleBracket (D.atom a) (D.atom b) (D.atom d) := by
  classical
  rw [circuitDep]
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hac),
    Pi.single_eq_of_ne (Ne.symm hbc), Pi.single_eq_of_ne hcd]
  ring

theorem circuitDep_apply_fourth (D : WeightedDesign m 3) {a b c d : Fin m}
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d) :
    circuitDep D a b c d d = -(tripleBracket (D.atom a) (D.atom b) (D.atom c)) := by
  classical
  rw [circuitDep]
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm had),
    Pi.single_eq_of_ne (Ne.symm hbd), Pi.single_eq_of_ne (Ne.symm hcd)]
  ring

/-! ## Part 4 — the swap law -/

/-- Three distinct labels enumerate their own triple. -/
theorem image_tripleVec_eq {a b c : Fin m} :
    Finset.image (![a, b, c] : Fin 3 → Fin m) Finset.univ = ({a, b, c} : Finset (Fin m)) := by
  classical
  ext probe
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨slot, rfl⟩
    fin_cases slot
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- Three distinct labels give an injective enumeration. -/
theorem injective_tripleVec {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (![a, b, c] : Fin 3 → Fin m) := by
  intro left right hvalue
  fin_cases left <;> fin_cases right <;> simp_all

/-- **THE CIRCUIT SWAP LAW.**  A dominating triple prices every one-atom swap.
Feeding the criterion the circuit of the four-set `{a,b,c,d}` leaves a SINGLE
term on the outside, because `d` is the only label of the circuit's support that
misses the triple.

No hypothesis on the design beyond domination, and every quantity is a bracket
and a weight. -/
theorem swapLaw_of_dominates (D : WeightedDesign m 3) (hm : 2 ≤ m) {a b c d : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hdom : Dominates D ({a, b, c} : Finset (Fin m))) :
    tripleBracket (D.atom b) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight a)
        + tripleBracket (D.atom a) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight b)
        + tripleBracket (D.atom a) (D.atom b) (D.atom d) ^ 2 / (1 - D.weight c)
      ≤ tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 / D.weight d := by
  classical
  set pick : Fin 3 → Fin m := ![a, b, c] with hpick
  have hinj : Function.Injective pick := injective_tripleVec hab hac hbc
  have himage : Finset.image pick Finset.univ = ({a, b, c} : Finset (Fin m)) :=
    image_tripleVec_eq
  have hdom' : Dominates D (Finset.image pick Finset.univ) := by rw [himage]; exact hdom
  have hcrit := (dominates_iff_dependencyBound_compl D hm pick hinj).mp hdom'
    (circuitDep D a b c d) (sum_circuitDep_smul_atom D a b c d)
  rw [himage] at hcrit
  -- the selected side is three terms
  have hleft : ∑ index ∈ ({a, b, c} : Finset (Fin m)),
        circuitDep D a b c d index ^ 2 / (1 - D.weight index)
      = tripleBracket (D.atom b) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight a)
        + tripleBracket (D.atom a) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight b)
        + tripleBracket (D.atom a) (D.atom b) (D.atom d) ^ 2 / (1 - D.weight c) := by
    rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton, circuitDep_apply_first D hab hac had,
      circuitDep_apply_second D hab hbc hbd, circuitDep_apply_third D hac hbc hcd]
    rw [neg_pow]
    ring
  -- the outside side is a single term
  have hdmem : d ∈ (({a, b, c} : Finset (Fin m))ᶜ) := by
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm had, Ne.symm hbd, Ne.symm hcd⟩
  have hright : ∑ index ∈ (({a, b, c} : Finset (Fin m))ᶜ),
        circuitDep D a b c d index ^ 2 / D.weight index
      = tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 / D.weight d := by
    rw [Finset.sum_eq_single_of_mem d hdmem]
    · rw [circuitDep_apply_fourth D had hbd hcd, neg_pow]
      ring
    · intro other hother hne
      have hnota : other ≠ a := by
        intro heq; rw [heq] at hother; simp at hother
      have hnotb : other ≠ b := by
        intro heq; rw [heq] at hother; simp at hother
      have hnotc : other ≠ c := by
        intro heq; rw [heq] at hother; simp at hother
      rw [circuitDep_apply_of_notMem D hnota hnotb hnotc hne]
      simp
  rw [hleft, hright] at hcrit
  exact hcrit

/-- **THE SWAP LAW, ONE TERM AT A TIME.**  Each of the three swapped brackets is
capped on its own, because the other two terms are nonnegative. -/
theorem swapLaw_single_of_dominates (D : WeightedDesign m 3) (hm : 2 ≤ m) {a b c d : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hdom : Dominates D ({a, b, c} : Finset (Fin m))) :
    D.weight d * tripleBracket (D.atom b) (D.atom c) (D.atom d) ^ 2
      ≤ (1 - D.weight a) * tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 := by
  have hlaw := swapLaw_of_dominates D hm hab hac had hbc hbd hcd hdom
  have hwa : (0 : ℝ) < 1 - D.weight a := by linarith [weight_lt_one D hm a]
  have hwb : (0 : ℝ) < 1 - D.weight b := by linarith [weight_lt_one D hm b]
  have hwc : (0 : ℝ) < 1 - D.weight c := by linarith [weight_lt_one D hm c]
  have hwd : (0 : ℝ) < D.weight d := D.weight_pos d
  have h2 : 0 ≤ tripleBracket (D.atom a) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight b) :=
    div_nonneg (sq_nonneg _) hwb.le
  have h3 : 0 ≤ tripleBracket (D.atom a) (D.atom b) (D.atom d) ^ 2 / (1 - D.weight c) :=
    div_nonneg (sq_nonneg _) hwc.le
  have hane : (1 : ℝ) - D.weight a ≠ 0 := ne_of_gt hwa
  have hdne : D.weight d ≠ 0 := ne_of_gt hwd
  have hstep : tripleBracket (D.atom b) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight a)
      ≤ tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 / D.weight d := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hstep (mul_pos hwa hwd).le
  have hleftEq : (1 - D.weight a) * D.weight d
        * (tripleBracket (D.atom b) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight a))
      = D.weight d * tripleBracket (D.atom b) (D.atom c) (D.atom d) ^ 2 := by
    field_simp
    try ring
  have hrightEq : (1 - D.weight a) * D.weight d
        * (tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 / D.weight d)
      = (1 - D.weight a) * tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 := by
    field_simp
    try ring
  rw [hleftEq, hrightEq] at hscaled
  exact hscaled

/-- **THE SWAP LAW WITH THE DISCOUNTS DROPPED.**  Every co-weight is at most one,
so the three swapped squared volumes together are capped by the dominator's own,
against the single weight of the incoming label. -/
theorem swapLaw_plain_of_dominates (D : WeightedDesign m 3) (hm : 2 ≤ m) {a b c d : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hdom : Dominates D ({a, b, c} : Finset (Fin m))) :
    D.weight d * (tripleBracket (D.atom b) (D.atom c) (D.atom d) ^ 2
        + tripleBracket (D.atom a) (D.atom c) (D.atom d) ^ 2
        + tripleBracket (D.atom a) (D.atom b) (D.atom d) ^ 2)
      ≤ tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 := by
  have hlaw := swapLaw_of_dominates D hm hab hac had hbc hbd hcd hdom
  have hwa : (0 : ℝ) < 1 - D.weight a := by linarith [weight_lt_one D hm a]
  have hwb : (0 : ℝ) < 1 - D.weight b := by linarith [weight_lt_one D hm b]
  have hwc : (0 : ℝ) < 1 - D.weight c := by linarith [weight_lt_one D hm c]
  have hwd : (0 : ℝ) < D.weight d := D.weight_pos d
  have hdrop : ∀ (value co : ℝ), 0 ≤ value → 0 < co → co ≤ 1 → value ≤ value / co := by
    intro value co hvalue hco hle
    rw [le_div_iff₀ hco]
    nlinarith [hvalue, hco, hle]
  have ha := hdrop (tripleBracket (D.atom b) (D.atom c) (D.atom d) ^ 2) (1 - D.weight a)
    (sq_nonneg _) hwa (by linarith [D.weight_pos a])
  have hb := hdrop (tripleBracket (D.atom a) (D.atom c) (D.atom d) ^ 2) (1 - D.weight b)
    (sq_nonneg _) hwb (by linarith [D.weight_pos b])
  have hc := hdrop (tripleBracket (D.atom a) (D.atom b) (D.atom d) ^ 2) (1 - D.weight c)
    (sq_nonneg _) hwc (by linarith [D.weight_pos c])
  have hsum : tripleBracket (D.atom b) (D.atom c) (D.atom d) ^ 2
      + tripleBracket (D.atom a) (D.atom c) (D.atom d) ^ 2
      + tripleBracket (D.atom a) (D.atom b) (D.atom d) ^ 2
      ≤ tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 / D.weight d := by linarith
  rw [le_div_iff₀ hwd] at hsum
  linarith [hsum]

/-- **THE CONTRAPOSITIVE.**  A four-set whose swap law fails refuses domination
to its own triple.  This is the shape a search reports. -/
theorem not_dominates_of_swapLaw_violation (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {a b c d : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hviolate : tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 / D.weight d
      < tripleBracket (D.atom b) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight a)
        + tripleBracket (D.atom a) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight b)
        + tripleBracket (D.atom a) (D.atom b) (D.atom d) ^ 2 / (1 - D.weight c)) :
    ¬ Dominates D ({a, b, c} : Finset (Fin m)) := by
  intro hdom
  exact absurd (swapLaw_of_dominates D hm hab hac had hbc hbd hcd hdom) (not_le.mpr hviolate)

/-! ## Part 5 — the swap law in volume currency

Scaling by the four weights turns every bracket into a triple mass of
`Gtz/Wave/TwentyVolumeMarginals.lean`, and the two co-weights become the ODDS of
the label that leaves. -/

/-- **THE ODDS OF A LABEL**, `t_c/(1 - t_c)`.  It is the discount the swap law
charges the member that a swap removes. -/
noncomputable def weightOdds (D : WeightedDesign m k) (label : Fin m) : ℝ :=
  D.weight label / (1 - D.weight label)

theorem weightOdds_pos (D : WeightedDesign m k) (hm : 2 ≤ m) (label : Fin m) :
    0 < weightOdds D label := by
  rw [weightOdds]
  exact div_pos (D.weight_pos label) (by linarith [weight_lt_one D hm label])

/-- **THE SWAP LAW IN VOLUME CURRENCY.**  A dominating triple's own mass
dominates the three masses obtained by swapping one member out for `d`, each
discounted by the odds of the member that leaves.

Every term is one of the twenty triple masses of a `(6,3)` design, so the law
lives entirely in the determinantal measure. -/
theorem swapLaw_volume_of_dominates (D : WeightedDesign m 3) (hm : 2 ≤ m) {a b c d : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hdom : Dominates D ({a, b, c} : Finset (Fin m))) :
    weightOdds D a * selectionVolume D b c d
        + weightOdds D b * selectionVolume D a c d
        + weightOdds D c * selectionVolume D a b d
      ≤ selectionVolume D a b c := by
  have hlaw := swapLaw_of_dominates D hm hab hac had hbc hbd hcd hdom
  have hwa : (0 : ℝ) < 1 - D.weight a := by linarith [weight_lt_one D hm a]
  have hwb : (0 : ℝ) < 1 - D.weight b := by linarith [weight_lt_one D hm b]
  have hwc : (0 : ℝ) < 1 - D.weight c := by linarith [weight_lt_one D hm c]
  have hta := D.weight_pos a
  have htb := D.weight_pos b
  have htc := D.weight_pos c
  have htd := D.weight_pos d
  have hscale : (0 : ℝ) < D.weight a * D.weight b * D.weight c * D.weight d := by positivity
  have hstep := mul_le_mul_of_nonneg_left hlaw hscale.le
  have hleftEq : D.weight a * D.weight b * D.weight c * D.weight d
        * (tripleBracket (D.atom b) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight a)
          + tripleBracket (D.atom a) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight b)
          + tripleBracket (D.atom a) (D.atom b) (D.atom d) ^ 2 / (1 - D.weight c))
      = weightOdds D a * selectionVolume D b c d
        + weightOdds D b * selectionVolume D a c d
        + weightOdds D c * selectionVolume D a b d := by
    rw [weightOdds, weightOdds, weightOdds, selectionVolume, selectionVolume, selectionVolume]
    field_simp
    try ring
  have hrightEq : D.weight a * D.weight b * D.weight c * D.weight d
        * (tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 / D.weight d)
      = selectionVolume D a b c := by
    rw [selectionVolume]
    field_simp
    try ring
  rw [hleftEq, hrightEq] at hstep
  exact hstep

/-! ## Part 6 — the aggregate at `(6,3)`

At `(6,3)` the complement of a dominating triple is again a triple, so the swap
law fires three times.  The nine swapped masses collapse onto the three pair
masses inside the dominator through the landed two-point marginal, and the
corner correction is exactly three copies of the dominator's own mass. -/

/-- **THE THREE OUTSIDE MASSES THROUGH A PAIR.**  The landed two-point marginal
`Gtz.sum_selectionVolume_eq_pairVolume` totals the SIX triples through a pair;
two of them repeat a label and vanish, one is the inside triple, and what is left
is the three that reach outside. -/
theorem sum_outside_selectionVolume_sixThree (D : WeightedDesign 6 3) {p q r x y z : Fin 6}
    (hbij : Function.Bijective (![p, q, r, x, y, z] : Fin 6 → Fin 6)) :
    selectionVolume D p q x + selectionVolume D p q y + selectionVolume D p q z
      = pairVolume D p q - selectionVolume D p q r := by
  have hrow := sum_selectionVolume_eq_pairVolume D p q
  have hre : ∑ third : Fin 6, selectionVolume D p q third
      = ∑ slot : Fin 6, selectionVolume D p q ((![p, q, r, x, y, z] : Fin 6 → Fin 6) slot) :=
    (Fintype.sum_bijective _ hbij _ _ fun _ => rfl).symm
  rw [hre, Fin.sum_univ_six] at hrow
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four] at hrow
  rw [selectionVolume_repeat_outer, selectionVolume_repeat_right] at hrow
  have hlast : (![p, q, r, x, y, z] : Fin 6 → Fin 6) 5 = z := rfl
  rw [hlast] at hrow
  linarith

/-- The triple mass does not care about the order of its three labels: the
rotation used by the aggregate. -/
theorem selectionVolume_rotate (D : WeightedDesign m 3) (first second third : Fin m) :
    selectionVolume D second third first = selectionVolume D first second third := by
  rw [selectionVolume_swap_right D second third first, selectionVolume_swap_left D second first third]

/-- **THE AGGREGATE SWAP LAW AT `(6,3)`.**  Summed over the three outside labels,
the swap law couples the PAIR layer of the determinantal measure to the TRIPLE
layer through domination:

    `th_a delta_bc + th_b delta_ac + th_c delta_ab
       <= (3 + th_a + th_b + th_c) nu_abc` .

The three pair masses on the left are the ones INSIDE the dominator, and the
right side mentions only the dominator's own mass and the three odds.  This is
the trace reading of the dependency criterion at the dominator. -/
theorem aggregate_swapLaw_of_dominates_sixThree (D : WeightedDesign 6 3) {a b c d e f : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hdom : Dominates D ({a, b, c} : Finset (Fin 6))) :
    weightOdds D a * pairVolume D b c + weightOdds D b * pairVolume D a c
        + weightOdds D c * pairVolume D a b
      ≤ (3 + weightOdds D a + weightOdds D b + weightOdds D c) * selectionVolume D a b c := by
  have hm : (2 : ℕ) ≤ 6 := by norm_num
  have hlawD := swapLaw_volume_of_dominates D hm hab hac had hbc hbd hcd hdom
  have hlawE := swapLaw_volume_of_dominates D hm hab hac hae hbc hbe hce hdom
  have hlawF := swapLaw_volume_of_dominates D hm hab hac haf hbc hbf hcf hdom
  -- the three pair rows
  have hrowBC := sum_outside_selectionVolume_sixThree D
    (bijective_six hbc (Ne.symm hab) hbd hbe hbf (Ne.symm hac) hcd hce hcf had hae haf
      hde hdf hef)
  have hrowAC := sum_outside_selectionVolume_sixThree D
    (bijective_six hac hab had hae haf (Ne.symm hbc) hcd hce hcf hbd hbe hbf hde hdf hef)
  have hrowAB := sum_outside_selectionVolume_sixThree D
    (bijective_six hab hac had hae haf hbc hbd hbe hbf hcd hce hcf hde hdf hef)
  -- rewrite the inside triples into the dominator's own mass
  rw [selectionVolume_rotate D a b c] at hrowBC
  rw [selectionVolume_swap_right D a c b] at hrowAC
  have hsum3 : weightOdds D a * selectionVolume D b c d + weightOdds D b * selectionVolume D a c d
        + weightOdds D c * selectionVolume D a b d
      + (weightOdds D a * selectionVolume D b c e + weightOdds D b * selectionVolume D a c e
        + weightOdds D c * selectionVolume D a b e)
      + (weightOdds D a * selectionVolume D b c f + weightOdds D b * selectionVolume D a c f
        + weightOdds D c * selectionVolume D a b f)
      ≤ 3 * selectionVolume D a b c := by linarith [hlawD, hlawE, hlawF]
  have hcollapse : weightOdds D a * selectionVolume D b c d
        + weightOdds D b * selectionVolume D a c d + weightOdds D c * selectionVolume D a b d
      + (weightOdds D a * selectionVolume D b c e + weightOdds D b * selectionVolume D a c e
        + weightOdds D c * selectionVolume D a b e)
      + (weightOdds D a * selectionVolume D b c f + weightOdds D b * selectionVolume D a c f
        + weightOdds D c * selectionVolume D a b f)
      = weightOdds D a * (pairVolume D b c - selectionVolume D a b c)
        + weightOdds D b * (pairVolume D a c - selectionVolume D a b c)
        + weightOdds D c * (pairVolume D a b - selectionVolume D a b c) := by
    rw [← hrowBC, ← hrowAC, ← hrowAB]
    ring
  rw [hcollapse] at hsum3
  linarith [hsum3]

/-! ## Part 7 — the second circuit family: the pair swap

The circuit of a four-set that meets the dominator in a PAIR rather than in the
whole triple leaves two terms on each side of the criterion.  The third member of
the dominator drops out of the conclusion entirely: it survives only inside the
domination hypothesis. -/

/-- **THE PAIR SWAP LAW.**  A dominating triple `{a,b,c}` prices the two triples
that keep ONE of `a`, `b` and take both of two further labels `d`, `e`, against
the two that keep the PAIR `{a,b}` and take one of `d`, `e`.

The circuit is the one of the four-set `{a,b,d,e}`, whose support meets the
dominator in `{a,b}` and its complement in `{d,e}`. -/
theorem pairSwapLaw_of_dominates (D : WeightedDesign m 3) (hm : 2 ≤ m) {a b c d e : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hdom : Dominates D ({a, b, c} : Finset (Fin m))) :
    tripleBracket (D.atom b) (D.atom d) (D.atom e) ^ 2 / (1 - D.weight a)
        + tripleBracket (D.atom a) (D.atom d) (D.atom e) ^ 2 / (1 - D.weight b)
      ≤ tripleBracket (D.atom a) (D.atom b) (D.atom e) ^ 2 / D.weight d
        + tripleBracket (D.atom a) (D.atom b) (D.atom d) ^ 2 / D.weight e := by
  classical
  set pick : Fin 3 → Fin m := ![a, b, c] with hpick
  have hinj : Function.Injective pick := injective_tripleVec hab hac hbc
  have himage : Finset.image pick Finset.univ = ({a, b, c} : Finset (Fin m)) :=
    image_tripleVec_eq
  have hdom' : Dominates D (Finset.image pick Finset.univ) := by rw [himage]; exact hdom
  have hcrit := (dominates_iff_dependencyBound_compl D hm pick hinj).mp hdom'
    (circuitDep D a b d e) (sum_circuitDep_smul_atom D a b d e)
  rw [himage] at hcrit
  -- the third member of the dominator misses the circuit's support
  have hthird : circuitDep D a b d e c = 0 :=
    circuitDep_apply_of_notMem D (Ne.symm hac) (Ne.symm hbc) hcd hce
  have hleft : ∑ index ∈ ({a, b, c} : Finset (Fin m)),
        circuitDep D a b d e index ^ 2 / (1 - D.weight index)
      = tripleBracket (D.atom b) (D.atom d) (D.atom e) ^ 2 / (1 - D.weight a)
        + tripleBracket (D.atom a) (D.atom d) (D.atom e) ^ 2 / (1 - D.weight b) := by
    rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton, circuitDep_apply_first D hab had hae,
      circuitDep_apply_second D hab hbd hbe, hthird]
    rw [neg_pow]
    simp
    try ring
  -- the outside side has exactly two live labels
  have hpairSub : ({d, e} : Finset (Fin m)) ⊆ (({a, b, c} : Finset (Fin m))ᶜ) := by
    intro probe hprobe
    simp only [Finset.mem_insert, Finset.mem_singleton] at hprobe
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    rcases hprobe with rfl | rfl
    · exact ⟨Ne.symm had, Ne.symm hbd, Ne.symm hcd⟩
    · exact ⟨Ne.symm hae, Ne.symm hbe, Ne.symm hce⟩
  have hright : ∑ index ∈ (({a, b, c} : Finset (Fin m))ᶜ),
        circuitDep D a b d e index ^ 2 / D.weight index
      = tripleBracket (D.atom a) (D.atom b) (D.atom e) ^ 2 / D.weight d
        + tripleBracket (D.atom a) (D.atom b) (D.atom d) ^ 2 / D.weight e := by
    rw [← Finset.sum_subset hpairSub ?_]
    · rw [Finset.sum_insert (by simp [hde]), Finset.sum_singleton,
        circuitDep_apply_third D had hbd hde, circuitDep_apply_fourth D hae hbe hde]
      rw [neg_pow]
      simp
      try ring
    · intro other hother hnot
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hother
      rw [circuitDep_apply_of_notMem D hother.1 hother.2.1 hnot.1 hnot.2]
      simp
  rw [hleft, hright] at hcrit
  exact hcrit

/-- **THE PAIR SWAP LAW IN VOLUME CURRENCY.**  No weight survives on the right.
The two triples that keep one member of the inside pair and take both outside
labels are dominated, at the odds of the member they keep out, by the two triples
that keep the whole inside pair. -/
theorem pairSwapLaw_volume_of_dominates (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {a b c d e : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hdom : Dominates D ({a, b, c} : Finset (Fin m))) :
    weightOdds D a * selectionVolume D b d e + weightOdds D b * selectionVolume D a d e
      ≤ selectionVolume D a b e + selectionVolume D a b d := by
  have hlaw := pairSwapLaw_of_dominates D hm hab hac had hae hbc hbd hbe hcd hce hde hdom
  have hwa : (0 : ℝ) < 1 - D.weight a := by linarith [weight_lt_one D hm a]
  have hwb : (0 : ℝ) < 1 - D.weight b := by linarith [weight_lt_one D hm b]
  have hta := D.weight_pos a
  have htb := D.weight_pos b
  have htd := D.weight_pos d
  have hte := D.weight_pos e
  have hscale : (0 : ℝ) < D.weight a * D.weight b * D.weight d * D.weight e := by positivity
  have hstep := mul_le_mul_of_nonneg_left hlaw hscale.le
  have hleftEq : D.weight a * D.weight b * D.weight d * D.weight e
        * (tripleBracket (D.atom b) (D.atom d) (D.atom e) ^ 2 / (1 - D.weight a)
          + tripleBracket (D.atom a) (D.atom d) (D.atom e) ^ 2 / (1 - D.weight b))
      = weightOdds D a * selectionVolume D b d e
        + weightOdds D b * selectionVolume D a d e := by
    rw [weightOdds, weightOdds, selectionVolume, selectionVolume]
    field_simp
    try ring
  have hrightEq : D.weight a * D.weight b * D.weight d * D.weight e
        * (tripleBracket (D.atom a) (D.atom b) (D.atom e) ^ 2 / D.weight d
          + tripleBracket (D.atom a) (D.atom b) (D.atom d) ^ 2 / D.weight e)
      = selectionVolume D a b e + selectionVolume D a b d := by
    rw [selectionVolume, selectionVolume]
    field_simp
    try ring
  rw [hleftEq, hrightEq] at hstep
  exact hstep

/-- The odds of a label are at least its weight, because the co-weight is at most
one. -/
theorem weight_le_weightOdds (D : WeightedDesign m k) (hm : 2 ≤ m) (label : Fin m) :
    D.weight label ≤ weightOdds D label := by
  have hco : (0 : ℝ) < 1 - D.weight label := by linarith [weight_lt_one D hm label]
  rw [weightOdds, le_div_iff₀ hco]
  nlinarith [D.weight_pos label, hco]

/-- **THE PAIR SWAP LAW, WITH THE ODDS DROPPED TO THE WEIGHTS.**  The weakest and
cleanest reading: the two outside-heavy masses, weighted by the two inside
weights, are capped by the two inside-heavy masses with no weight at all. -/
theorem pairSwapLaw_weight_of_dominates (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {a b c d e : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hdom : Dominates D ({a, b, c} : Finset (Fin m))) :
    D.weight a * selectionVolume D b d e + D.weight b * selectionVolume D a d e
      ≤ selectionVolume D a b e + selectionVolume D a b d := by
  have hlaw := pairSwapLaw_volume_of_dominates D hm hab hac had hae hbc hbd hbe hcd hce hde hdom
  have hoddsA := weight_le_weightOdds D hm a
  have hoddsB := weight_le_weightOdds D hm b
  have hvolA := selectionVolume_nonneg D b d e
  have hvolB := selectionVolume_nonneg D a d e
  nlinarith [hlaw, hoddsA, hoddsB, hvolA, hvolB]

/-- **THE PAIR SWAP LAW, ONE TERM AT A TIME.** -/
theorem pairSwapLaw_single_of_dominates (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {a b c d e : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hdom : Dominates D ({a, b, c} : Finset (Fin m))) :
    weightOdds D a * selectionVolume D b d e
      ≤ selectionVolume D a b e + selectionVolume D a b d := by
  have hlaw := pairSwapLaw_volume_of_dominates D hm hab hac had hae hbc hbd hbe hcd hce hde hdom
  have hodds := (weightOdds_pos D hm b).le
  have hvol := selectionVolume_nonneg D a d e
  nlinarith [hlaw, hodds, hvol]

/-- **THE CONTRAPOSITIVE OF THE PAIR SWAP LAW.** -/
theorem not_dominates_of_pairSwapLaw_violation (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {a b c d e : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hviolate : selectionVolume D a b e + selectionVolume D a b d
      < weightOdds D a * selectionVolume D b d e
        + weightOdds D b * selectionVolume D a d e) :
    ¬ Dominates D ({a, b, c} : Finset (Fin m)) := by
  intro hdom
  exact absurd
    (pairSwapLaw_volume_of_dominates D hm hab hac had hae hbc hbd hbe hcd hce hde hdom)
    (not_le.mpr hviolate)

end Gtz
