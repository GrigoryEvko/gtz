/-
# Branch (i) fails on the CLOSURE of its own stratum

`Gtz.StressFreeHingeHoldsSixThree` -- branch (i) of the `(6,3)` stress
trichotomy -- says that a `WeightedDesign 6 3` whose six atom matrices are a
basis of the symmetric three-by-three matrices is never a tie.  Equivalently,
by `stressFreeHingeHoldsSixThree_iff_no_stressFree_tie`, that such a design
always has a STRICTLY dominating triple.

This file shows that the statement becomes FALSE the moment the strict
positivity of the weights is relaxed to nonnegativity at a single label, and
that the failure is structural rather than accidental: it happens at EVERY
`(5,3)` tie whose atoms are independent.

## The construction

Take a `(5,3)` tie and adjoin a sixth atom carrying weight zero.  Parseval,
the weight sum, and nonnegativity all survive verbatim, because a zero weight
contributes nothing.  The twenty triples split in two:

* the ten triples inside the base are the base's own, and a tie has no strictly
  dominating triple among them;
* each of the ten triples through the new atom contains two base atoms, and a
  nonzero direction orthogonal to BOTH -- which exists in three dimensions for
  any two vectors -- sees the gap form as `(sixth . x)^2 - |x|^2`, at most
  `(leverage(sixth) - 1) |x|^2`.  So a sixth atom of leverage at most one kills
  all ten at once.

Adding a sixth atom off the span of the base's five leaves the family
independent, so the relaxed system sits in the closure of branch (i)'s stratum
and has no strictly dominating triple at all.

## What it says about the branch

`weight_pos` is LOAD-BEARING at every label.  No proof of branch (i) can be
weight-blind, and no certificate carrying a threshold uniform in the weights can
prove it: the margin `max_C lambda_min(S_C) - 1` is continuous, vanishes at this
relaxed system, and the system is a limit of genuine designs, so the margin has
INFIMUM ZERO on the stress-free stratum.  Measured on the diamond, in exact
rational arithmetic: the extension with sixth atom `(1/2, 1/3, 1/5)` in the
diamond's own whitened frame is stress-free with no strictly dominating triple,
and pushing the sixth weight up to `t` restores a margin of about `8 t` -- the
margin is LINEAR in the sixth weight and nothing bounds it below.

That is a single cause for a list of separately recorded failures: the isotropy
test, the free-mass budget, and the exchange-spend gate are all threshold
certificates, and each was measured to lose reach exactly as the frontier is
approached.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Reduction.RayleighCertificate
import Gtz.Ties.RepeatedAtomExclusion
import Gtz.Design.MarginTransfer
import Gtz.Certificates.ResidueDissolution
import Gtz.Design.DiamondPrimitive
import Gtz.Design.RigidityBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ## The gap form of a bare triple of atoms -/

/-- The quadratic form of a three-atom gap, without a design wrapper. -/
theorem tripleGap_form (first second third probe : Fin 3 → ℝ) :
    probe ⬝ᵥ ((atomMatrix first + atomMatrix second + atomMatrix third
        - (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ probe)
      = (first ⬝ᵥ probe) ^ 2 + (second ⬝ᵥ probe) ^ 2 + (third ⬝ᵥ probe) ^ 2
        - probe ⬝ᵥ probe := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, Matrix.add_mulVec,
    Matrix.add_mulVec, dotProduct_add, dotProduct_add, atom_form_eq_sq,
    atom_form_eq_sq, atom_form_eq_sq]

/-- Cauchy-Schwarz in three dimensions, by the Lagrange identity. -/
theorem sq_dotProduct_le_mul_dotProduct_self (left right : Fin 3 → ℝ) :
    (left ⬝ᵥ right) ^ 2 ≤ (left ⬝ᵥ left) * (right ⬝ᵥ right) := by
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [sq_nonneg (left 0 * right 1 - left 1 * right 0),
    sq_nonneg (left 0 * right 2 - left 2 * right 0),
    sq_nonneg (left 1 * right 2 - left 2 * right 1)]

/-- **A SHORT EXTRA ATOM KILLS EVERY TRIPLE IT SITS IN.**  Two of the triple's
atoms leave a nonzero direction orthogonal to both, and along it the gap form is
`(extra . x)^2 - |x|^2`, which Cauchy-Schwarz bounds by
`(leverage(extra) - 1) |x|^2`.  So an extra atom of leverage at most one is in
no strictly dominating triple whatsoever. -/
theorem not_posDef_tripleGap_of_leverage_le_one (extra partnerOne partnerTwo : Fin 3 → ℝ)
    (hleverage : leverageOf extra ≤ 1) :
    ¬ (atomMatrix extra + atomMatrix partnerOne + atomMatrix partnerTwo
        - (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef := by
  intro hposDef
  obtain ⟨witness, hwitnessNe, hpartnerOne, hpartnerTwo⟩ :=
    exists_ne_zero_dotProduct_pair_eq_zero partnerOne partnerTwo
  have hnormPos : 0 < witness ⬝ᵥ witness := dotProduct_self_pos hwitnessNe
  have hvalue := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hwitnessNe
  rw [star_trivial, tripleGap_form, hpartnerOne, hpartnerTwo] at hvalue
  have hcauchy := sq_dotProduct_le_mul_dotProduct_self extra witness
  have hself : extra ⬝ᵥ extra = leverageOf extra := by
    simp only [leverageOf, dotProduct, pow_two]
  rw [hself] at hcauchy
  nlinarith [hvalue, hcauchy, hnormPos, hleverage]

/-! ## The relaxed system built from a `(5,3)` tie -/

/-- The atoms of the base with one more appended. -/
noncomputable def extendedAtom (base : WeightedDesign 5 3) (extra : Fin 3 → ℝ) :
    Fin 6 → Fin 3 → ℝ :=
  Fin.snoc base.atom extra

/-- The weights of the base with a ZERO appended. -/
noncomputable def extendedWeight (base : WeightedDesign 5 3) : Fin 6 → ℝ :=
  Fin.snoc base.weight 0

theorem extendedAtom_castSucc (base : WeightedDesign 5 3) (extra : Fin 3 → ℝ)
    (label : Fin 5) : extendedAtom base extra label.castSucc = base.atom label := by
  simp [extendedAtom]

theorem extendedAtom_last (base : WeightedDesign 5 3) (extra : Fin 3 → ℝ) :
    extendedAtom base extra (Fin.last 5) = extra := by
  rw [extendedAtom, Fin.snoc_last]

theorem extendedWeight_castSucc (base : WeightedDesign 5 3) (label : Fin 5) :
    extendedWeight base label.castSucc = base.weight label := by
  simp [extendedWeight]

theorem extendedWeight_last (base : WeightedDesign 5 3) :
    extendedWeight base (Fin.last 5) = 0 := by
  rw [extendedWeight, Fin.snoc_last]

/-- Nonnegativity survives: five positive weights and one zero. -/
theorem extendedWeight_nonneg (base : WeightedDesign 5 3) (label : Fin 6) :
    0 ≤ extendedWeight base label := by
  refine Fin.lastCases ?_ ?_ label
  · rw [extendedWeight_last]
  · intro inner
    rw [extendedWeight_castSucc]
    exact (base.weight_pos inner).le

/-- The weight sum survives: the appended zero contributes nothing. -/
theorem extendedWeight_sum_one (base : WeightedDesign 5 3) :
    ∑ label, extendedWeight base label = 1 := by
  rw [Fin.sum_univ_castSucc, extendedWeight_last, add_zero]
  rw [Finset.sum_congr rfl fun label _ => extendedWeight_castSucc base label]
  exact base.weight_sum_one

/-- Parseval survives, for the same reason. -/
theorem extendedAtom_isParseval (base : WeightedDesign 5 3) (extra : Fin 3 → ℝ) :
    ∑ label, extendedWeight base label • atomMatrix (extendedAtom base extra label) = 1 := by
  rw [Fin.sum_univ_castSucc, extendedWeight_last, zero_smul, add_zero]
  rw [Finset.sum_congr rfl fun label _ => by
    rw [extendedWeight_castSucc, extendedAtom_castSucc]]
  exact base.isParseval

/-! ## No triple of the relaxed system dominates strictly -/

/-- Three labels of the base give the base's own gap matrix. -/
theorem extendedTriple_of_castSucc (base : WeightedDesign 5 3) (extra : Fin 3 → ℝ)
    (first second third : Fin 5) (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    atomMatrix (extendedAtom base extra first.castSucc)
        + atomMatrix (extendedAtom base extra second.castSucc)
        + atomMatrix (extendedAtom base extra third.castSucc)
        - (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = subsetSum base {first, second, third} - 1 := by
  classical
  rw [subsetSum, Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
    Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton]
  rw [extendedAtom_castSucc, extendedAtom_castSucc, extendedAtom_castSucc]
  abel

/-- **NO TRIPLE OF THE RELAXED SYSTEM DOMINATES STRICTLY.**  Triples inside the
base are refused by the tie; triples through the appended atom are refused by
its leverage. -/
theorem not_posDef_extendedTriple (base : WeightedDesign 5 3) (htie : IsTie base)
    (extra : Fin 3 → ℝ) (hleverage : leverageOf extra ≤ 1)
    (first second third : Fin 6) (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    ¬ (atomMatrix (extendedAtom base extra first)
        + atomMatrix (extendedAtom base extra second)
        + atomMatrix (extendedAtom base extra third)
        - (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef := by
  classical
  -- if any of the three labels is the appended one, the leverage argument fires
  by_cases hfirstLast : first = Fin.last 5
  · subst hfirstLast
    rw [extendedAtom_last]
    exact not_posDef_tripleGap_of_leverage_le_one _ _ _ hleverage
  by_cases hsecondLast : second = Fin.last 5
  · subst hsecondLast
    rw [extendedAtom_last]
    intro hposDef
    refine not_posDef_tripleGap_of_leverage_le_one extra
      (extendedAtom base extra first) (extendedAtom base extra third) hleverage ?_
    have hreorder : atomMatrix extra + atomMatrix (extendedAtom base extra first)
          + atomMatrix (extendedAtom base extra third)
        = atomMatrix (extendedAtom base extra first) + atomMatrix extra
          + atomMatrix (extendedAtom base extra third) := by abel
    rw [hreorder]
    exact hposDef
  by_cases hthirdLast : third = Fin.last 5
  · subst hthirdLast
    rw [extendedAtom_last]
    intro hposDef
    refine not_posDef_tripleGap_of_leverage_le_one extra
      (extendedAtom base extra first) (extendedAtom base extra second) hleverage ?_
    have hreorder : atomMatrix extra + atomMatrix (extendedAtom base extra first)
          + atomMatrix (extendedAtom base extra second)
        = atomMatrix (extendedAtom base extra first)
          + atomMatrix (extendedAtom base extra second) + atomMatrix extra := by abel
    rw [hreorder]
    exact hposDef
  -- otherwise all three sit inside the base and the tie refuses them
  obtain ⟨innerFirst, rfl⟩ := Fin.exists_castSucc_eq.mpr hfirstLast
  obtain ⟨innerSecond, rfl⟩ := Fin.exists_castSucc_eq.mpr hsecondLast
  obtain ⟨innerThird, rfl⟩ := Fin.exists_castSucc_eq.mpr hthirdLast
  have hone : innerFirst ≠ innerSecond := fun heq => hfirstSecond (by rw [heq])
  have htwo : innerFirst ≠ innerThird := fun heq => hfirstThird (by rw [heq])
  have hthree : innerSecond ≠ innerThird := fun heq => hsecondThird (by rw [heq])
  rw [extendedTriple_of_castSucc base extra innerFirst innerSecond innerThird hone htwo hthree]
  refine htie.2 {innerFirst, innerSecond, innerThird} ?_
  rw [Finset.card_insert_of_notMem (by simp [hone, htwo]),
    Finset.card_insert_of_notMem (by simp [hthree]), Finset.card_singleton]


/-! ## The extra atom always exists

Five atoms leave a conic.  Building the six-by-six grid whose first five rows are
the Veronese coordinates of the base atoms and whose last row is ZERO gives a
singular matrix, so it has a nonzero kernel vector, and that vector is a nonzero
symmetric form annihilating all five atoms.  A nonzero symmetric form is nonzero
at one of six standard test directions, and rescaling that direction to unit
leverage produces an extra atom short enough for the leverage argument and off
the span for the independence argument.  No dimension theory is used anywhere:
the padded zero row does the counting. -/

/-- The Veronese coordinates of a three-vector, ordered to match
`conicOfCoefficients`. -/
def atomVeroneseRow (vector : Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![vector 0 * vector 0, vector 1 * vector 1, vector 2 * vector 2,
    vector 0 * vector 1, vector 0 * vector 2, vector 1 * vector 2]

/-- The symmetric form whose quadratic form has the prescribed Veronese
coefficients. -/
noncomputable def conicOfCoefficients (coefficient : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![coefficient 0, coefficient 3 / 2, coefficient 4 / 2;
     coefficient 3 / 2, coefficient 1, coefficient 5 / 2;
     coefficient 4 / 2, coefficient 5 / 2, coefficient 2]

/-- The quadratic form of `conicOfCoefficients` is the Veronese pairing. -/
theorem conicOfCoefficients_form (coefficient : Fin 6 → ℝ) (vector : Fin 3 → ℝ) :
    vector ⬝ᵥ (conicOfCoefficients coefficient *ᵥ vector)
      = ∑ index, coefficient index * atomVeroneseRow vector index := by
  simp only [conicOfCoefficients, atomVeroneseRow, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val, Matrix.of_apply]
  ring

/-- A nonzero coefficient vector gives a form that is nonzero at one of the six
standard test directions. -/
theorem exists_testDirection_form_ne_zero {coefficient : Fin 6 → ℝ}
    (hnonzero : coefficient ≠ 0) :
    ∃ vector : Fin 3 → ℝ,
      vector ⬝ᵥ (conicOfCoefficients coefficient *ᵥ vector) ≠ 0 := by
  by_contra hall
  push Not at hall
  refine hnonzero (funext fun index => ?_)
  have hbasis : ∀ probe : Fin 3 → ℝ,
      ∑ slot, coefficient slot * atomVeroneseRow probe slot = 0 := by
    intro probe
    rw [← conicOfCoefficients_form]
    exact hall probe
  have hzero := hbasis ![1, 0, 0]
  have hone := hbasis ![0, 1, 0]
  have htwo := hbasis ![0, 0, 1]
  have hzeroOne := hbasis ![1, 1, 0]
  have hzeroTwo := hbasis ![1, 0, 1]
  have honeTwo := hbasis ![0, 1, 1]
  simp only [atomVeroneseRow, Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val] at hzero hone htwo hzeroOne hzeroTwo honeTwo
  norm_num at hzero hone htwo hzeroOne hzeroTwo honeTwo
  have hthree : coefficient 3 = 0 := by linarith
  have hfour : coefficient 4 = 0 := by linarith
  have hfive : coefficient 5 = 0 := by linarith
  fin_cases index <;> simp only [Pi.zero_apply] <;> assumption

/-- **A CONIC THROUGH FIVE ATOMS, AND A DIRECTION OFF IT.**  Every family of five
three-vectors leaves a nonzero symmetric form annihilating all five, and some
direction of unit leverage is not annihilated by that form. -/
theorem exists_unitLeverage_offConic (baseAtom : Fin 5 → Fin 3 → ℝ) :
    ∃ extra : Fin 3 → ℝ, leverageOf extra = 1
      ∧ ∃ conic : Matrix (Fin 3) (Fin 3) ℝ,
        (∀ label : Fin 5, baseAtom label ⬝ᵥ (conic *ᵥ baseAtom label) = 0)
        ∧ extra ⬝ᵥ (conic *ᵥ extra) ≠ 0 := by
  classical
  set grid : Matrix (Fin 6) (Fin 6) ℝ :=
    Matrix.of fun rowIndex colIndex =>
      if hrow : (rowIndex : ℕ) < 5 then
        atomVeroneseRow (baseAtom (Fin.mk (rowIndex : ℕ) hrow)) colIndex
      else 0 with hgridDef
  have hdet : grid.det = 0 := by
    refine Matrix.det_eq_zero_of_row_eq_zero (Fin.last 5) fun colIndex => ?_
    simp [hgridDef]
  obtain ⟨coefficient, hnonzero, hkernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨seed, hseed⟩ := exists_testDirection_form_ne_zero hnonzero
  have hseedNe : seed ≠ 0 := by
    intro hzero
    rw [hzero] at hseed
    simp at hseed
  have hleverageSelf : leverageOf seed = seed ⬝ᵥ seed := by
    simp only [leverageOf, dotProduct, pow_two]
  have hleveragePos : 0 < leverageOf seed := by
    rw [hleverageSelf]
    exact dotProduct_self_pos hseedNe
  have hsqrtPos : 0 < Real.sqrt (leverageOf seed) := Real.sqrt_pos.mpr hleveragePos
  have hsq : ((Real.sqrt (leverageOf seed))⁻¹) ^ 2 = (leverageOf seed)⁻¹ := by
    rw [← Real.sqrt_inv, Real.sq_sqrt (by positivity)]
  refine ⟨(Real.sqrt (leverageOf seed))⁻¹ • seed, ?_, conicOfCoefficients coefficient,
    fun label => ?_, ?_⟩
  · have hscale : ∀ (factor : ℝ) (vec : Fin 3 → ℝ),
        leverageOf (factor • vec) = factor ^ 2 * leverageOf vec := by
      intro factor vec
      simp only [leverageOf, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
    rw [hscale, hsq, inv_mul_cancel₀ hleveragePos.ne']
  · have hrow := congrFun hkernel (Fin.castSucc label)
    rw [conicOfCoefficients_form]
    simp only [Matrix.mulVec, dotProduct, hgridDef, Matrix.of_apply, Pi.zero_apply] at hrow
    rw [← hrow]
    refine Finset.sum_congr rfl fun slot _ => ?_
    have hlt : ((Fin.castSucc label : Fin 6) : ℕ) < 5 := label.isLt
    rw [dif_pos hlt, mul_comm]
    congr 2
  · have hscaled : ((Real.sqrt (leverageOf seed))⁻¹ • seed)
          ⬝ᵥ (conicOfCoefficients coefficient
            *ᵥ ((Real.sqrt (leverageOf seed))⁻¹ • seed))
        = ((Real.sqrt (leverageOf seed))⁻¹) ^ 2
          * (seed ⬝ᵥ (conicOfCoefficients coefficient *ᵥ seed)) := by
      rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [hscaled]
    exact mul_ne_zero (by positivity) hseed

/-- **THE EXTENSION IS STRESS-FREE.**  Pairing a stress against the conic kills
every base coefficient at once and leaves the extra atom's coefficient times a
nonzero number, so that coefficient vanishes; the base's own independence then
finishes. -/
theorem extendedAtom_stressFree_of_offConic (base : WeightedDesign 5 3)
    (hbaseIndependent : ∀ stressCoeff : Fin 5 → ℝ,
      (∑ label, stressCoeff label • atomMatrix (base.atom label)) = 0 → stressCoeff = 0)
    (extra : Fin 3 → ℝ) {conic : Matrix (Fin 3) (Fin 3) ℝ}
    (hbaseOnConic : ∀ label : Fin 5, base.atom label ⬝ᵥ (conic *ᵥ base.atom label) = 0)
    (hextraOffConic : extra ⬝ᵥ (conic *ᵥ extra) ≠ 0)
    (stressCoeff : Fin 6 → ℝ)
    (hstress : (∑ label, stressCoeff label • atomMatrix (extendedAtom base extra label)) = 0) :
    stressCoeff = 0 := by
  classical
  have hpair := congrArg (fun target => Matrix.trace (target * conic)) hstress
  simp only [Matrix.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
    smul_eq_mul, atomMatrix_trace_pairing, Matrix.zero_mul, Matrix.trace_zero] at hpair
  rw [Fin.sum_univ_castSucc, extendedAtom_last] at hpair
  rw [Finset.sum_congr rfl fun label _ => by
    rw [extendedAtom_castSucc, hbaseOnConic label, mul_zero]] at hpair
  simp only [Finset.sum_const_zero, zero_add] at hpair
  have hlast : stressCoeff (Fin.last 5) = 0 := by
    rcases mul_eq_zero.mp hpair with hzero | hzero
    · exact hzero
    · exact absurd hzero hextraOffConic
  have hbaseStress : (∑ label : Fin 5,
      stressCoeff label.castSucc • atomMatrix (base.atom label)) = 0 := by
    rw [Fin.sum_univ_castSucc, extendedAtom_last, hlast, zero_smul, add_zero] at hstress
    rw [← hstress]
    exact Finset.sum_congr rfl fun label _ => by rw [extendedAtom_castSucc]
  have hbaseZero := hbaseIndependent _ hbaseStress
  funext label
  refine Fin.lastCases ?_ ?_ label
  · exact hlast
  · intro inner
    exact congrFun hbaseZero inner

/-! ## The headline -/

/-- **BRANCH (i) FAILS ON THE CLOSURE OF ITS STRATUM.**  Every `(5,3)` tie
extends, by one atom of leverage at most one carrying weight zero, to a
six-atom system that satisfies every clause of a stress-free `(6,3)` design
except the STRICT positivity of one weight -- and that has no strictly
dominating triple.

The stress-freeness of the extension is a hypothesis here rather than a
conclusion because it depends on the direction of the extra atom: the extension
is stress-free exactly when the extra atom is off the unique conic through the
base's five directions, which is an open dense condition but not an automatic
one.  Everything else is unconditional. -/
theorem exists_relaxed_stressFree_sixThree_without_posDef_triple
    (base : WeightedDesign 5 3) (htie : IsTie base)
    (extra : Fin 3 → ℝ) (hleverage : leverageOf extra ≤ 1)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ label, stressCoeff label • atomMatrix (extendedAtom base extra label)) = 0 →
        stressCoeff = 0) :
    ∃ (atom : Fin 6 → Fin 3 → ℝ) (weight : Fin 6 → ℝ),
      (∀ label, 0 ≤ weight label)
      ∧ (∑ label, weight label) = 1
      ∧ (∑ label, weight label • atomMatrix (atom label)) = 1
      ∧ (∀ stressCoeff : Fin 6 → ℝ,
          (∑ label, stressCoeff label • atomMatrix (atom label)) = 0 → stressCoeff = 0)
      ∧ ∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
          ¬ (atomMatrix (atom first) + atomMatrix (atom second) + atomMatrix (atom third)
              - (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef :=
  ⟨extendedAtom base extra, extendedWeight base, extendedWeight_nonneg base,
    extendedWeight_sum_one base, extendedAtom_isParseval base extra, hstressFree,
    fun first second third hfirstSecond hfirstThird hsecondThird =>
      not_posDef_extendedTriple base htie extra hleverage first second third
        hfirstSecond hfirstThird hsecondThird⟩

/-- **THE WEIGHT-POSITIVITY OBSTRUCTION.**  Read as a no-go: the relaxed
branch-(i) statement, with `0 < weight` weakened to `0 <= weight` and everything
else verbatim, is FALSE as soon as one `(5,3)` tie admits a stress-free
extension.  So `weight_pos` is load-bearing at every one of the six labels, and
any argument that does not use it -- in particular any certificate whose
threshold is uniform in the weights -- cannot prove branch (i). -/
theorem not_relaxedStressFreeHinge_of_extension
    (base : WeightedDesign 5 3) (htie : IsTie base)
    (extra : Fin 3 → ℝ) (hleverage : leverageOf extra ≤ 1)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ label, stressCoeff label • atomMatrix (extendedAtom base extra label)) = 0 →
        stressCoeff = 0) :
    ¬ ∀ (atom : Fin 6 → Fin 3 → ℝ) (weight : Fin 6 → ℝ),
        (∀ label, 0 ≤ weight label) →
        (∑ label, weight label) = 1 →
        (∑ label, weight label • atomMatrix (atom label)) = 1 →
        (∀ stressCoeff : Fin 6 → ℝ,
          (∑ label, stressCoeff label • atomMatrix (atom label)) = 0 → stressCoeff = 0) →
        ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third
          ∧ (atomMatrix (atom first) + atomMatrix (atom second) + atomMatrix (atom third)
              - (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef := by
  intro hclaim
  obtain ⟨atom, weight, hnonneg, hsum, hparseval, hfree, hnone⟩ :=
    exists_relaxed_stressFree_sixThree_without_posDef_triple base htie extra hleverage
      hstressFree
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hposDef⟩ :=
    hclaim atom weight hnonneg hsum hparseval hfree
  exact hnone first second third hfirstSecond hfirstThird hsecondThird hposDef


/-! ## The capstone: one hypothesis, and it is about the base alone -/

/-- **EVERY `(5,3)` TIE WITH INDEPENDENT ATOMS REFUTES THE RELAXED BRANCH (i).**
The extra atom is produced rather than assumed: five atoms leave a conic, some
unit-leverage direction is off it, unit leverage is short enough to kill every
triple through the new atom, and being off the conic is exactly what makes the
six atoms independent.  So the only input is the base. -/
theorem exists_relaxed_stressFree_counterexample_of_fiveThree_tie
    (base : WeightedDesign 5 3) (htie : IsTie base)
    (hbaseIndependent : ∀ stressCoeff : Fin 5 → ℝ,
      (∑ label, stressCoeff label • atomMatrix (base.atom label)) = 0 → stressCoeff = 0) :
    ∃ (atom : Fin 6 → Fin 3 → ℝ) (weight : Fin 6 → ℝ),
      (∀ label, 0 ≤ weight label)
      ∧ (∑ label, weight label) = 1
      ∧ (∑ label, weight label • atomMatrix (atom label)) = 1
      ∧ (∀ stressCoeff : Fin 6 → ℝ,
          (∑ label, stressCoeff label • atomMatrix (atom label)) = 0 → stressCoeff = 0)
      ∧ ∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
          ¬ (atomMatrix (atom first) + atomMatrix (atom second) + atomMatrix (atom third)
              - (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef := by
  obtain ⟨extra, hleverage, conic, hbaseOnConic, hextraOffConic⟩ :=
    exists_unitLeverage_offConic base.atom
  exact exists_relaxed_stressFree_sixThree_without_posDef_triple base htie extra
    (le_of_eq hleverage)
    (extendedAtom_stressFree_of_offConic base hbaseIndependent extra hbaseOnConic hextraOffConic)

/-- **THE NO-GO, IN ITS FINAL FORM.**  Relax `0 < weight` to `0 <= weight` in
branch (i) and leave every other clause verbatim: the resulting statement is
FALSE, witnessed by any `(5,3)` tie whose five atoms are independent.

Read as a constraint on proofs of branch (i): strict positivity of the weights is
load-bearing, so no argument that treats the weights as merely nonnegative can
work, and in particular no certificate whose threshold is uniform in the weights
can -- the witness here is a limit of genuine stress-free `(6,3)` designs along
which the margin tends to zero. -/
theorem not_relaxedStressFreeHinge_of_fiveThree_tie
    (base : WeightedDesign 5 3) (htie : IsTie base)
    (hbaseIndependent : ∀ stressCoeff : Fin 5 → ℝ,
      (∑ label, stressCoeff label • atomMatrix (base.atom label)) = 0 → stressCoeff = 0) :
    ¬ ∀ (atom : Fin 6 → Fin 3 → ℝ) (weight : Fin 6 → ℝ),
        (∀ label, 0 ≤ weight label) →
        (∑ label, weight label) = 1 →
        (∑ label, weight label • atomMatrix (atom label)) = 1 →
        (∀ stressCoeff : Fin 6 → ℝ,
          (∑ label, stressCoeff label • atomMatrix (atom label)) = 0 → stressCoeff = 0) →
        ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third
          ∧ (atomMatrix (atom first) + atomMatrix (atom second) + atomMatrix (atom third)
              - (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef := by
  intro hclaim
  obtain ⟨atom, weight, hnonneg, hsum, hparseval, hfree, hnone⟩ :=
    exists_relaxed_stressFree_counterexample_of_fiveThree_tie base htie hbaseIndependent
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hposDef⟩ :=
    hclaim atom weight hnonneg hsum hparseval hfree
  exact hnone first second third hfirstSecond hfirstThird hsecondThird hposDef

/-! ## The diamond instance

`Gtz.diamondDesign` is a kernel-checked primitive `(5,3)` tie (as is
`Gtz.uniformTieParentDesign`, a different design with the same dependent-triple
matroid), so it is a concrete witness this no-go wants.  Its five atoms ARE
independent in the symmetric three-by-three matrices, and that fact is now
PROVED below.  The whitener is a `Classical.choose`, but independence never
reads its entries: the five raw edge rank-ones of
`(1,-1,0), (1,0,-1), (1,0,0), (0,1,-1), (0,1,0)` are independent because five
entries of a vanishing combination read the coefficients off directly, and
`atomMatrix_graphicAtom` transports any vanishing combination of the design's
atoms through the invertible whitener congruence and the positive
conductance-to-weight scales down to the raw ones.  The premise the instance
used to carry is retired. -/

/-- The five raw diamond edge rank-ones are linearly independent: the three
off-diagonal entries of a vanishing combination kill the three non-axis
coefficients, the two remaining diagonal entries kill the rest. -/
theorem diamondEdgeAtomMatrices_linearIndependent (coeff : Fin 5 → ℝ)
    (hvanish : (∑ edge, coeff edge • atomMatrix (diamondGraph.edgeVector edge)) = 0) :
    coeff = 0 := by
  have hentry : ∀ row col : Fin 3,
      (∑ edge, coeff edge • atomMatrix (diamondGraph.edgeVector edge)) row col = 0 := by
    intro row col
    rw [hvanish]
    rfl
  have hZeroOne := hentry 0 1
  have hZeroTwo := hentry 0 2
  have hOneTwo := hentry 1 2
  have hZeroZero := hentry 0 0
  have hOneOne := hentry 1 1
  simp [Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply,
    MultigraphOnGround.edgeVector, diamondGraph, Fin.sum_univ_five,
    Fin.isValue] at hZeroOne hZeroTwo hOneTwo hZeroZero hOneOne
  funext edge
  fin_cases edge <;> simp <;> linarith

/-- **The diamond design's five atom matrices are linearly independent** — the
fact the instance below used to take as a hypothesis.  A vanishing combination
of the design's atoms is a vanishing combination of the whitener-congruated
raw rank-ones with the conductance-to-weight ratios folded in; the congruence
is invertible and the ratios are positive, so the raw independence finishes. -/
theorem diamondDesign_atomMatrices_linearIndependent :
    ∀ stressCoeff : Fin 5 → ℝ,
      (∑ label, stressCoeff label • atomMatrix (diamondDesign.atom label)) = 0 →
        stressCoeff = 0 := by
  intro stressCoeff hvanish
  have hatomShape : ∀ label : Fin 5,
      atomMatrix (diamondDesign.atom label)
        = (diamondData.conductance label / diamondData.weight label) •
            ((diamondData.whitener)ᵀ
              * atomMatrix (diamondGraph.edgeVector label) * diamondData.whitener) :=
    fun label => diamondData.atomMatrix_graphicAtom label
  have hscaledVanish :
      (diamondData.whitener)ᵀ
          * (∑ label, (stressCoeff label
                * (diamondData.conductance label / diamondData.weight label)) •
              atomMatrix (diamondGraph.edgeVector label))
          * diamondData.whitener = 0 := by
    have hpull := congr_sum_smul_atomMatrix (diamondData.whitener)ᵀ
      (fun label => stressCoeff label
        * (diamondData.conductance label / diamondData.weight label))
      diamondGraph.edgeVector Finset.univ
    rw [Matrix.transpose_transpose] at hpull
    rw [hpull, ← hvanish]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [hatomShape label, smul_smul]
  have hwhitenerDet : IsUnit (diamondData.whitener).det := diamondData.whitener_isUnit
  have hwhitenerTransposeDet : IsUnit ((diamondData.whitener)ᵀ).det := by
    rwa [Matrix.det_transpose]
  have hrawVanish :
      (∑ label, (stressCoeff label
            * (diamondData.conductance label / diamondData.weight label)) •
          atomMatrix (diamondGraph.edgeVector label)) = 0 := by
    set rawSum := ∑ label, (stressCoeff label
        * (diamondData.conductance label / diamondData.weight label)) •
        atomMatrix (diamondGraph.edgeVector label) with hrawSumDef
    have hconjIsZero : ((diamondData.whitener)ᵀ)⁻¹
        * ((diamondData.whitener)ᵀ * rawSum * diamondData.whitener)
        * (diamondData.whitener)⁻¹ = 0 := by
      rw [hscaledVanish, Matrix.mul_zero, Matrix.zero_mul]
    have hconjIsRawSum : ((diamondData.whitener)ᵀ)⁻¹
        * ((diamondData.whitener)ᵀ * rawSum * diamondData.whitener)
        * (diamondData.whitener)⁻¹ = rawSum := by
      rw [Matrix.mul_assoc (diamondData.whitener)ᵀ rawSum diamondData.whitener,
        ← Matrix.mul_assoc ((diamondData.whitener)ᵀ)⁻¹ (diamondData.whitener)ᵀ
          (rawSum * diamondData.whitener),
        Matrix.nonsing_inv_mul _ hwhitenerTransposeDet, Matrix.one_mul,
        Matrix.mul_assoc rawSum diamondData.whitener (diamondData.whitener)⁻¹,
        Matrix.mul_nonsing_inv _ hwhitenerDet, Matrix.mul_one]
    exact hconjIsRawSum.symm.trans hconjIsZero
  have hscaledCoeff := diamondEdgeAtomMatrices_linearIndependent
    (fun label => stressCoeff label
      * (diamondData.conductance label / diamondData.weight label)) hrawVanish
  funext label
  have hlabelZero := congrFun hscaledCoeff label
  have hratioPos : 0 < diamondData.conductance label / diamondData.weight label :=
    div_pos (diamondData.conductance_pos label) (diamondData.weight_pos label)
  have hproductZero : stressCoeff label
      * (diamondData.conductance label / diamondData.weight label) = 0 := hlabelZero
  rcases mul_eq_zero.mp hproductZero with hcoeffZero | hratioZero
  · exact hcoeffZero
  · exact absurd hratioZero hratioPos.ne'

/-- **THE INSTANCE, PREMISE-FREE.**  The relaxed branch-(i) statement is
false, unconditionally: the diamond is a kernel-checked tie and its atoms are
independent by the theorem above.

**#BOGUS-READING — THIS DOES NOT KILL THE HINGE AT `(6,3)`.**  The weight clause
below is `0 <= weight`, NOT `0 < weight`.  The witness is the `(5,3)` diamond
padded with a sixth atom of weight zero, and `Gtz.WeightedDesign` carries
`weight_pos` as a structure field.  The padded witness is therefore not a
`Gtz.WeightedDesign 6 3` at all.  `Gtz.StressFreeHingeHoldsSixThree`
(Gtz/Reduction/TrichotomyLedger.lean:629) is OPEN.  Refer to the index in
Gtz/Wave/WiringSynonymClass.lean. -/
theorem not_relaxedStressFreeHinge_of_diamond :
    ¬ ∀ (atom : Fin 6 → Fin 3 → ℝ) (weight : Fin 6 → ℝ),
        (∀ label, 0 ≤ weight label) →
        (∑ label, weight label) = 1 →
        (∑ label, weight label • atomMatrix (atom label)) = 1 →
        (∀ stressCoeff : Fin 6 → ℝ,
          (∑ label, stressCoeff label • atomMatrix (atom label)) = 0 → stressCoeff = 0) →
        ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third
          ∧ (atomMatrix (atom first) + atomMatrix (atom second) + atomMatrix (atom third)
              - (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef :=
  not_relaxedStressFreeHinge_of_fiveThree_tie diamondDesign diamondDesign_isTie
    diamondDesign_atomMatrices_linearIndependent

end Gtz
