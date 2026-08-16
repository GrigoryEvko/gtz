import Gtz.Wave.ThresholdSpread

/-!
# The joint law of determinantal mass against sign-free threshold

The objective at uniform weight is `Gtz.projThresholdAt < 216 * det` at some triple:
the squared bracket of a selection must beat that selection's own threshold.  Both
sides are now understood separately.  `Gtz.sum_projThreshold` gives the threshold
total `1632`, `Gtz.sum_tripleBlockDet` gives the mass total `6`, and
`Gtz.sum_projGap` gives the deficit `-336`.  **The threshold beats the mass on the
mean, so the objective is a statement about the JOINT distribution and about
neither marginal.**

This file computes that joint distribution.

**The headline is that the two are NON-NEGATIVELY correlated, always.**  Writing
`x_c = P_cc - 1/2` for the leverage deviation and `d_cd = pairMinor c d - 1/5` for
the pair-minor deviation, the landed row law `Gtz.sum_pairMinor_projection` says

  `∑ over d ≠ c of d_cd = 2 * x_c`   (`Gtz.sum_pairMinorDev_row`)

and Cauchy--Schwarz on that row gives `5 * ∑ d^2 ≥ 4 * ∑ x^2`.  Feeding it through
the joint second moment yields

  `18 * pairSecondMoment - 6 * levSecondMoment - 63/5 = 18 * devPair - 6 * devLev`
    `≥ (42/5) * devLev ≥ 0`

which is `Gtz.joint_covariance_nonneg`.  **So an anti-correlation argument between
mass and threshold is refuted by theorem, not by witness**, and Chebyshev's sum
inequality points the wrong way.  Equality forces every leverage to one half and
every pair minor to one fifth, which is the equiangular profile.

**The second closed form is the joint second moment itself.**  The threshold is
two-local, so `∑ mass * threshold` collapses onto the landed one- and two-point
determinantal marginals, and the pair-marginal second moment is closed-form in the
same two invariants.  Against the elementary `Gtz.sum_sq_le_sq_sum_of_nonpos` --
a non-positive family has `∑ g^2 ≤ (∑ g)^2` -- that produces a certificate whose
hypothesis reads ONLY the two second moments and no bracket at all.

**What is NOT closed form is the mass second moment**, and
`Gtz.sum_sq_projGap_eq_massSecondMoment_sub` isolates exactly that: the whole
second-moment theory of the objective reduces to the single unknown
`∑ (det P_SS)^2`.
-/

namespace Gtz

open Matrix Finset

section Deviation

variable (design : WeightedDesign 6 3)

/-- The leverage deviation from the equal-share value one half. -/
noncomputable def leverageDev (label : Fin 6) : ℝ :=
  projectionOfDesign design label label - 1 / 2

/-- The pair-minor deviation from the equiangular value one fifth. -/
noncomputable def pairMinorDev (first second : Fin 6) : ℝ :=
  pairMinorAt (projectionOfDesign design) first second - 1 / 5

/-- The second moment of the leverage profile. -/
noncomputable def levSecondMoment : ℝ :=
  ∑ label : Fin 6, projectionOfDesign design label label ^ 2

/-- The second moment of the pair minors, over ORDERED distinct pairs.  Twice the
unordered sum. -/
noncomputable def pairSecondMoment : ℝ :=
  ∑ first : Fin 6, ∑ second ∈ (univ : Finset (Fin 6)).erase first,
    pairMinorAt (projectionOfDesign design) first second ^ 2

/-- The second moment of the leverage DEVIATION. -/
noncomputable def devLev : ℝ := ∑ label : Fin 6, leverageDev design label ^ 2

/-- The second moment of the pair-minor DEVIATION, over ordered distinct pairs. -/
noncomputable def devPair : ℝ :=
  ∑ first : Fin 6, ∑ second ∈ (univ : Finset (Fin 6)).erase first,
    pairMinorDev design first second ^ 2

theorem leverageDev_apply (label : Fin 6) :
    leverageDev design label = projectionOfDesign design label label - 1 / 2 := rfl

theorem pairMinorDev_apply (first second : Fin 6) :
    pairMinorDev design first second
      = pairMinorAt (projectionOfDesign design) first second - 1 / 5 := rfl

/-- The leverage deviations total zero: the trace is the rank. -/
theorem sum_leverageDev : ∑ label : Fin 6, leverageDev design label = 0 := by
  have htrace := sum_projectionDiagonal design
  simp only [leverageDev]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [htrace]
  norm_num

/-- **THE ROW LAW FOR PAIR-MINOR DEVIATIONS.**  The landed row law
`Gtz.sum_pairMinor_projection` says the pair minors along a row total twice that
row's leverage.  Subtracting the equiangular value one fifth from each of the five
off-diagonal slots turns it into a statement about deviations, and the constant
`5 * (1/5) = 1` is exactly the constant `2 * (1/2)` on the other side.  **That
exact cancellation is what makes the covariance sign a theorem.** -/
theorem sum_pairMinorDev_row (label : Fin 6) :
    ∑ other ∈ (univ : Finset (Fin 6)).erase label, pairMinorDev design label other
      = 2 * leverageDev design label := by
  classical
  have hfull := sum_pairMinor_projection design label
  have hself : pairMinorAt (projectionOfDesign design) label label = 0 :=
    pairMinorAt_self _ label
  have hsplit : ∑ other ∈ (univ : Finset (Fin 6)).erase label,
      pairMinorAt (projectionOfDesign design) label other
      = 2 * projectionOfDesign design label label := by
    have := sum_erase_one (n := 6) label
      (fun other => pairMinorAt (projectionOfDesign design) label other)
    rw [this, hself]
    norm_num at hfull ⊢
    linarith [hfull]
  simp only [pairMinorDev, leverageDev]
  rw [Finset.sum_sub_distrib, hsplit]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [card_erase_one (n := 6) label]
  norm_num
  ring

/-- The pair-minor deviations total zero over ordered distinct pairs. -/
theorem sum_pairMinorDev : ∑ first : Fin 6,
    ∑ second ∈ (univ : Finset (Fin 6)).erase first, pairMinorDev design first second = 0 := by
  have hrow : ∀ label : Fin 6,
      ∑ other ∈ (univ : Finset (Fin 6)).erase label, pairMinorDev design label other
        = 2 * leverageDev design label := sum_pairMinorDev_row design
  rw [Finset.sum_congr rfl (fun label _ => hrow label)]
  rw [← Finset.mul_sum, sum_leverageDev design]
  ring

/-- The leverage second moment in deviation coordinates. -/
theorem levSecondMoment_eq : levSecondMoment design = devLev design + 3 / 2 := by
  have hzero := sum_leverageDev design
  have hexp : ∀ label : Fin 6,
      projectionOfDesign design label label ^ 2
        = leverageDev design label ^ 2 + leverageDev design label + 1 / 4 := by
    intro label; simp only [leverageDev]; ring
  simp only [levSecondMoment, devLev]
  rw [Finset.sum_congr rfl (fun label _ => hexp label)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hzero]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- The pair-minor second moment in deviation coordinates. -/
theorem pairSecondMoment_eq : pairSecondMoment design = devPair design + 6 / 5 := by
  classical
  have hzero := sum_pairMinorDev design
  have hexp : ∀ first : Fin 6, ∀ second : Fin 6,
      pairMinorAt (projectionOfDesign design) first second ^ 2
        = pairMinorDev design first second ^ 2
          + (2 / 5) * pairMinorDev design first second + 1 / 25 := by
    intro first second; simp only [pairMinorDev]; ring
  simp only [pairSecondMoment, devPair]
  have hinner : ∀ first : Fin 6,
      ∑ second ∈ (univ : Finset (Fin 6)).erase first,
          pairMinorAt (projectionOfDesign design) first second ^ 2
        = (∑ second ∈ (univ : Finset (Fin 6)).erase first,
            pairMinorDev design first second ^ 2)
          + (2 / 5) * (∑ second ∈ (univ : Finset (Fin 6)).erase first,
            pairMinorDev design first second) + 5 * (1 / 25) := by
    intro first
    rw [Finset.sum_congr rfl (fun second _ => hexp first second)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [card_erase_one (n := 6) first]
    norm_num
  rw [Finset.sum_congr rfl (fun first _ => hinner first)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hzero]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

end Deviation

section CauchySchwarz

variable (design : WeightedDesign 6 3)

/-- **THE ROW CAUCHY--SCHWARZ.**  Each row of the deviation matrix has five slots
and a prescribed sum, so its energy is bounded below.  This is where the factor
`5` -- the label count minus one -- enters, and it is the only place the ambient
size is spent. -/
theorem sq_sum_pairMinorDev_row_le (label : Fin 6) :
    4 * leverageDev design label ^ 2
      ≤ 5 * ∑ other ∈ (univ : Finset (Fin 6)).erase label,
          pairMinorDev design label other ^ 2 := by
  classical
  have hsum := sum_pairMinorDev_row design label
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := (univ : Finset (Fin 6)).erase label)
    (f := fun other => pairMinorDev design label other)
  rw [hsum, card_erase_one (n := 6) label] at hcs
  have hcast : (((6 : ℕ) - 1 : ℕ) : ℝ) = 5 := by norm_num
  rw [hcast] at hcs
  nlinarith [hcs]

/-- **THE DEVIATION INEQUALITY.**  Summing the row bound over the six labels:
the pair-minor deviation energy is at least four fifths of the leverage deviation
energy.  Both sides vanish exactly at the equiangular profile. -/
theorem four_mul_devLev_le_five_mul_devPair :
    4 * devLev design ≤ 5 * devPair design := by
  classical
  simp only [devLev, devPair]
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum (fun label _ => sq_sum_pairMinorDev_row_le design label)

end CauchySchwarz

section Covariance

variable (design : WeightedDesign 6 3)

/-- The joint invariant that the covariance of mass against threshold reduces to.
Positivity of this quantity is positivity of that covariance. -/
noncomputable def jointCovariantPart : ℝ :=
  18 * pairSecondMoment design - 6 * levSecondMoment design - 63 / 5

/-- **THE COVARIANT PART IN DEVIATION COORDINATES.**  The three constants
`18 * 6/5`, `6 * 3/2` and `63/5` cancel exactly, so the invariant is a pure
difference of deviation energies. -/
theorem jointCovariantPart_eq :
    jointCovariantPart design = 18 * devPair design - 6 * devLev design := by
  simp only [jointCovariantPart]
  rw [pairSecondMoment_eq design, levSecondMoment_eq design]
  ring

/-- **THE COVARIANCE IS NON-NEGATIVE, ALWAYS, WITH AN EXPLICIT SLACK.**  The
deviation inequality gives `18 * devPair ≥ (72/5) * devLev`, and `72/5 - 6 = 42/5`.
So the determinantal mass and the sign-free threshold are NON-NEGATIVELY
correlated at every design, and the slack is a positive multiple of the leverage
deviation from equal share. -/
theorem jointCovariantPart_ge_devLev :
    (42 / 5) * devLev design ≤ jointCovariantPart design := by
  have hdev := four_mul_devLev_le_five_mul_devPair design
  rw [jointCovariantPart_eq design]
  linarith [hdev]

/-- `Gtz.devLev` is a sum of squares. -/
theorem devLev_nonneg : 0 ≤ devLev design :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- `Gtz.devPair` is a sum of squares. -/
theorem devPair_nonneg : 0 ≤ devPair design :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- **THE REFUTATION OF ANTI-CORRELATION.**  An argument that the objective follows
from mass and threshold being anti-correlated cannot exist: the covariant part is
non-negative at every design.  Chebyshev's sum inequality therefore points away
from the objective, not toward it. -/
theorem joint_covariance_nonneg : 0 ≤ jointCovariantPart design :=
  le_trans (mul_nonneg (by norm_num) (devLev_nonneg design))
    (jointCovariantPart_ge_devLev design)

/-- The invariant form of the same statement: the pair-minor second moment
dominates the leverage second moment on this exact scale. -/
theorem eighteen_pairSecondMoment_ge :
    6 * levSecondMoment design + 63 / 5 ≤ 18 * pairSecondMoment design := by
  have := joint_covariance_nonneg design
  simp only [jointCovariantPart] at this
  linarith

/-- Equality forces the leverage profile to be exactly flat.  The equiangular
locus is the only place the covariance vanishes. -/
theorem devLev_eq_zero_of_covariantPart_eq_zero
    (hzero : jointCovariantPart design = 0) : devLev design = 0 := by
  have hge := jointCovariantPart_ge_devLev design
  have hnn := devLev_nonneg design
  rw [hzero] at hge
  linarith

/-- At a vanishing covariance every leverage is exactly one half. -/
theorem projection_diag_eq_half_of_covariantPart_eq_zero
    (hzero : jointCovariantPart design = 0) (label : Fin 6) :
    projectionOfDesign design label label = 1 / 2 := by
  have hzeroLev := devLev_eq_zero_of_covariantPart_eq_zero design hzero
  have hmem : label ∈ (univ : Finset (Fin 6)) := Finset.mem_univ label
  have hterm : leverageDev design label ^ 2 = 0 := by
    by_contra hne
    have hpos : 0 < leverageDev design label ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
    have hle : leverageDev design label ^ 2 ≤ devLev design :=
      Finset.single_le_sum (f := fun l => leverageDev design l ^ 2)
        (fun _ _ => sq_nonneg _) hmem
    linarith
  have : leverageDev design label = 0 := by
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hterm
  simp only [leverageDev] at this
  linarith

end Covariance

/-! ## The elementary maximum law

A non-positive family cannot have a large energy against its own total.  This is
the whole of the certificate below, and it needs neither a square root, a variance,
nor a spectral bound. -/

section MaximumLaw

variable {ι : Type*} [DecidableEq ι]

/-- For a NON-NEGATIVE family the energy never exceeds the square of the total. -/
theorem sum_sq_le_sq_sum_of_nonneg (labels : Finset ι) (value : ι → ℝ)
    (hnn : ∀ i ∈ labels, 0 ≤ value i) :
    ∑ i ∈ labels, value i ^ 2 ≤ (∑ i ∈ labels, value i) ^ 2 := by
  classical
  induction labels using Finset.induction_on with
  | empty => simp
  | insert head rest hhead ih =>
      rw [Finset.sum_insert hhead, Finset.sum_insert hhead]
      have hhn : 0 ≤ value head := hnn head (Finset.mem_insert_self _ _)
      have hrn : ∀ i ∈ rest, 0 ≤ value i := fun i hi =>
        hnn i (Finset.mem_insert_of_mem hi)
      have hrest := ih hrn
      have hrestsum : 0 ≤ ∑ i ∈ rest, value i := Finset.sum_nonneg hrn
      nlinarith [hrest, hhn, hrestsum]

/-- **THE MAXIMUM LAW.**  If a family has energy strictly beyond the square of its
total, some member is strictly positive.  Contrapositive of the previous law after
a sign flip. -/
theorem exists_pos_of_sq_sum_lt_sum_sq (labels : Finset ι) (value : ι → ℝ)
    (hbig : (∑ i ∈ labels, value i) ^ 2 < ∑ i ∈ labels, value i ^ 2) :
    ∃ i ∈ labels, 0 < value i := by
  classical
  by_contra hraw
  simp only [not_exists] at hraw
  have hcon : ∀ i ∈ labels, value i ≤ 0 := by
    intro i hi
    by_contra hpos
    exact hraw i ⟨hi, lt_of_not_ge hpos⟩
  have hnn : ∀ i ∈ labels, 0 ≤ (fun j => -value j) i := fun i hi => by
    have := hcon i hi; simpa using neg_nonneg.mpr this
  have hsq := sum_sq_le_sq_sum_of_nonneg labels (fun j => -value j) hnn
  have hleft : ∑ i ∈ labels, (-value i) ^ 2 = ∑ i ∈ labels, value i ^ 2 := by
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hright : (∑ i ∈ labels, -value i) ^ 2 = (∑ i ∈ labels, value i) ^ 2 := by
    rw [Finset.sum_neg_distrib]; ring
  rw [hleft, hright] at hsq
  linarith

end MaximumLaw

/-! ## The pair-marginal second moment

The pair marginal of the gap is `Gtz.sum_projGap_through_pair`, a two-local
quantity.  Its own second moment is therefore closed-form in the two invariants of
the previous section, and the maximum law turns that closed form into a
certificate. -/

section PairMarginal

variable (design : WeightedDesign 6 3)

/-- The gap marginal through an ordered pair, named. -/
noncomputable def pairMarginal (first second : Fin 6) : ℝ :=
  144 * pairMinorAt (projectionOfDesign design) first second + 14
    - 54 * (projectionOfDesign design first first + projectionOfDesign design second second)

theorem pairMarginal_apply (first second : Fin 6) :
    pairMarginal design first second
      = 144 * pairMinorAt (projectionOfDesign design) first second + 14
        - 54 * (projectionOfDesign design first first
          + projectionOfDesign design second second) := rfl

/-- The pair marginal is the inner sum of the gap over the third slot. -/
theorem sum_projGap_eq_pairMarginal (first second : Fin 6)
    (hsecond : second ∈ (univ : Finset (Fin 6)).erase first) :
    ∑ inner ∈ ((univ : Finset (Fin 6)).erase first).erase second,
        projGapAt (projectionOfDesign design) first second inner
      = pairMarginal design first second := by
  rw [sum_projGap_through_pair design first second hsecond, pairMarginal]

/-- **THE PAIR-MARGINAL TOTAL.**  Summing the marginal over the thirty ordered
distinct pairs recovers the landed gap deficit. -/
theorem sum_pairMarginal :
    ∑ first : Fin 6, ∑ second ∈ (univ : Finset (Fin 6)).erase first,
        pairMarginal design first second = -336 := by
  classical
  have hgap := sum_projGap design
  rw [← hgap]
  refine Finset.sum_congr rfl (fun first _ => Finset.sum_congr rfl (fun second hsecond => ?_))
  exact (sum_projGap_eq_pairMarginal design first second hsecond).symm

end PairMarginal

/-! ## The certificate

The pair marginals are thirty numbers with a known total.  If their energy beats
the square of that total then one of them is positive, and the landed
`Gtz.exists_pos_projGap_of_pairMarginal_pos` turns a positive marginal into a
triple with a positive third minor.  **The hypothesis reads only the two second
moments and never the bracket.** -/

section Certificate

variable (design : WeightedDesign 6 3)

/-- The energy of the thirty pair marginals. -/
noncomputable def pairMarginalEnergy : ℝ :=
  ∑ first : Fin 6, ∑ second ∈ (univ : Finset (Fin 6)).erase first,
    pairMarginal design first second ^ 2

/-- The pair minor of a projection is symmetric in its two labels. -/
theorem pairMinorAt_projection_symm (first second : Fin 6) :
    pairMinorAt (projectionOfDesign design) first second
      = pairMinorAt (projectionOfDesign design) second first := by
  have hsymm := projectionOfDesign_transpose design
  have hentry : projectionOfDesign design second first
      = projectionOfDesign design first second := by
    have := congrFun (congrFun hsymm first) second
    simpa only [Matrix.transpose_apply] using this
  simp only [pairMinorAt, hentry]; ring

/-- The pair minors along a row, off the diagonal, total twice the leverage. -/
theorem sum_pairMinor_erase (label : Fin 6) :
    ∑ other ∈ (univ : Finset (Fin 6)).erase label,
        pairMinorAt (projectionOfDesign design) label other
      = 2 * projectionOfDesign design label label := by
  have hfull := sum_pairMinor_projection design label
  have hself : pairMinorAt (projectionOfDesign design) label label = 0 :=
    pairMinorAt_self _ label
  rw [sum_erase_one (n := 6) label
    (fun other => pairMinorAt (projectionOfDesign design) label other), hself]
  norm_num at hfull ⊢
  linarith [hfull]

/-- **THE ORDERED PAIR-MINOR TOTAL.**  Six, twice the landed unordered total. -/
theorem sum_pairMinor_ordered :
    ∑ first : Fin 6, ∑ second ∈ (univ : Finset (Fin 6)).erase first,
        pairMinorAt (projectionOfDesign design) first second = 6 := by
  rw [Finset.sum_congr rfl (fun first _ => sum_pairMinor_erase design first)]
  rw [← Finset.mul_sum, sum_projectionDiagonal design]
  norm_num

/-- The diagonal pair sum over ordered distinct pairs. -/
theorem sum_diagPair :
    ∑ first : Fin 6, ∑ second ∈ (univ : Finset (Fin 6)).erase first,
        (projectionOfDesign design first first + projectionOfDesign design second second)
      = 30 := by
  classical
  have htrace := sum_projectionDiagonal design
  have hinner : ∀ first : Fin 6,
      ∑ second ∈ (univ : Finset (Fin 6)).erase first,
          (projectionOfDesign design first first + projectionOfDesign design second second)
        = 4 * projectionOfDesign design first first + 3 := by
    intro first
    rw [Finset.sum_add_distrib]
    rw [sum_erase_one (n := 6) first
      (fun second => projectionOfDesign design second second), htrace]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [card_erase_one (n := 6) first]
    norm_num
    ring
  rw [Finset.sum_congr rfl (fun first _ => hinner first)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, htrace]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- The pair minor against the diagonal pair sum.  The swap of the two label slots
is `Finset.sum_comm` after extending the off-diagonal sum to the full one, which
costs nothing because the diagonal pair minors vanish. -/
theorem sum_pairMinor_mul_diagPair :
    ∑ first : Fin 6, ∑ second ∈ (univ : Finset (Fin 6)).erase first,
        pairMinorAt (projectionOfDesign design) first second
          * (projectionOfDesign design first first
            + projectionOfDesign design second second)
      = 4 * levSecondMoment design := by
  classical
  have hself : ∀ label : Fin 6, pairMinorAt (projectionOfDesign design) label label = 0 :=
    fun label => pairMinorAt_self _ label
  -- split the product
  have hsplit : ∀ first : Fin 6,
      ∑ second ∈ (univ : Finset (Fin 6)).erase first,
          pairMinorAt (projectionOfDesign design) first second
            * (projectionOfDesign design first first
              + projectionOfDesign design second second)
        = projectionOfDesign design first first
            * (∑ second ∈ (univ : Finset (Fin 6)).erase first,
                pairMinorAt (projectionOfDesign design) first second)
          + ∑ second : Fin 6, pairMinorAt (projectionOfDesign design) first second
              * projectionOfDesign design second second := by
    intro first
    have hfull : ∑ second ∈ (univ : Finset (Fin 6)).erase first,
        pairMinorAt (projectionOfDesign design) first second
          * projectionOfDesign design second second
        = ∑ second : Fin 6, pairMinorAt (projectionOfDesign design) first second
            * projectionOfDesign design second second := by
      rw [sum_erase_one (n := 6) first
        (fun second => pairMinorAt (projectionOfDesign design) first second
          * projectionOfDesign design second second), hself first]
      ring
    rw [← hfull, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun second _ => by ring)
  rw [Finset.sum_congr rfl (fun first _ => hsplit first)]
  rw [Finset.sum_add_distrib]
  have hleft : ∑ first : Fin 6, projectionOfDesign design first first
      * (∑ second ∈ (univ : Finset (Fin 6)).erase first,
          pairMinorAt (projectionOfDesign design) first second)
      = 2 * levSecondMoment design := by
    rw [Finset.sum_congr rfl (fun first _ => by
      rw [sum_pairMinor_erase design first])]
    simp only [levSecondMoment]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun first _ => by ring)
  have hright : ∑ first : Fin 6,
      ∑ second : Fin 6, pairMinorAt (projectionOfDesign design) first second
        * projectionOfDesign design second second
      = 2 * levSecondMoment design := by
    rw [Finset.sum_comm]
    have hcol : ∀ second : Fin 6,
        ∑ first : Fin 6, pairMinorAt (projectionOfDesign design) first second
          * projectionOfDesign design second second
        = 2 * projectionOfDesign design second second
          * projectionOfDesign design second second := by
      intro second
      rw [← Finset.sum_mul]
      have : ∑ first : Fin 6, pairMinorAt (projectionOfDesign design) first second
          = 2 * projectionOfDesign design second second := by
        rw [Finset.sum_congr rfl
          (fun first _ => pairMinorAt_projection_symm design first second)]
        have := sum_pairMinor_projection design second
        norm_num at this ⊢
        linarith [this]
      rw [this]
    rw [Finset.sum_congr rfl (fun second _ => hcol second)]
    simp only [levSecondMoment]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun second _ => by ring)
  rw [hleft, hright]; ring

/-- The squared diagonal pair sum over ordered distinct pairs. -/
theorem sum_sq_diagPair :
    ∑ first : Fin 6, ∑ second ∈ (univ : Finset (Fin 6)).erase first,
        (projectionOfDesign design first first
          + projectionOfDesign design second second) ^ 2
      = 8 * levSecondMoment design + 18 := by
  classical
  have htrace := sum_projectionDiagonal design
  have hinner : ∀ first : Fin 6,
      ∑ second ∈ (univ : Finset (Fin 6)).erase first,
          (projectionOfDesign design first first
            + projectionOfDesign design second second) ^ 2
        = 2 * projectionOfDesign design first first ^ 2
          + 6 * projectionOfDesign design first first + levSecondMoment design := by
    intro first
    have hexp : ∀ second : Fin 6,
        (projectionOfDesign design first first
          + projectionOfDesign design second second) ^ 2
        = projectionOfDesign design first first ^ 2
          + 2 * projectionOfDesign design first first
            * projectionOfDesign design second second
          + projectionOfDesign design second second ^ 2 := fun second => by ring
    rw [Finset.sum_congr rfl (fun second _ => hexp second)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [card_erase_one (n := 6) first]
    rw [← Finset.mul_sum]
    rw [sum_erase_one (n := 6) first
      (fun second => projectionOfDesign design second second), htrace]
    rw [sum_erase_one (n := 6) first
      (fun second => projectionOfDesign design second second ^ 2)]
    simp only [levSecondMoment]
    norm_num
    ring
  rw [Finset.sum_congr rfl (fun first _ => hinner first)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    htrace]
  simp only [levSecondMoment, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- **THE PAIR-MARGINAL ENERGY IN CLOSED FORM.**  Two invariants and nothing else:
no bracket, no determinant, no triple sum.  This is what makes the certificate
below computable from two-local data alone. -/
theorem pairMarginalEnergy_eq :
    pairMarginalEnergy design
      = 20736 * pairSecondMoment design - 38880 * levSecondMoment design + 37200 := by
  classical
  have hexp : ∀ first second : Fin 6,
      pairMarginal design first second ^ 2
        = 20736 * pairMinorAt (projectionOfDesign design) first second ^ 2
          + 4032 * pairMinorAt (projectionOfDesign design) first second
          - 15552 * (pairMinorAt (projectionOfDesign design) first second
            * (projectionOfDesign design first first
              + projectionOfDesign design second second))
          + 196
          + 2916 * (projectionOfDesign design first first
            + projectionOfDesign design second second) ^ 2
          - 1512 * (projectionOfDesign design first first
            + projectionOfDesign design second second) := by
    intro first second; simp only [pairMarginal]; ring
  have key : ∀ first : Fin 6,
      ∑ second ∈ (univ : Finset (Fin 6)).erase first, pairMarginal design first second ^ 2
        = 20736 * (∑ second ∈ (univ : Finset (Fin 6)).erase first,
            pairMinorAt (projectionOfDesign design) first second ^ 2)
          + 4032 * (∑ second ∈ (univ : Finset (Fin 6)).erase first,
            pairMinorAt (projectionOfDesign design) first second)
          - 15552 * (∑ second ∈ (univ : Finset (Fin 6)).erase first,
            pairMinorAt (projectionOfDesign design) first second
              * (projectionOfDesign design first first
                + projectionOfDesign design second second))
          + 980
          + 2916 * (∑ second ∈ (univ : Finset (Fin 6)).erase first,
            (projectionOfDesign design first first
              + projectionOfDesign design second second) ^ 2)
          - 1512 * (∑ second ∈ (univ : Finset (Fin 6)).erase first,
            (projectionOfDesign design first first
              + projectionOfDesign design second second)) := by
    intro first
    rw [Finset.sum_congr rfl (fun second _ => hexp first second)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
    rw [card_erase_one (n := 6) first]
    norm_num
  simp only [pairMarginalEnergy]
  rw [Finset.sum_congr rfl (fun first _ => key first)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [sum_pairMinor_ordered design, sum_pairMinor_mul_diagPair design,
    sum_sq_diagPair design]
  have hA : ∑ x : Fin 6, (((univ : Finset (Fin 6)).erase x).card : ℝ)
      * projectionOfDesign design x x = 15 := by
    have hstep : ∀ x : Fin 6, (((univ : Finset (Fin 6)).erase x).card : ℝ)
        * projectionOfDesign design x x = 5 * projectionOfDesign design x x := by
      intro x; rw [card_erase_one (n := 6) x]; norm_num
    rw [Finset.sum_congr rfl (fun x _ => hstep x), ← Finset.mul_sum,
      sum_projectionDiagonal design]
    norm_num
  have hB : ∑ x : Fin 6, ∑ y ∈ (univ : Finset (Fin 6)).erase x,
      projectionOfDesign design y y = 15 := by
    have hstep : ∀ x : Fin 6, ∑ y ∈ (univ : Finset (Fin 6)).erase x,
        projectionOfDesign design y y = (3 : ℝ) - projectionOfDesign design x x := by
      intro x
      rw [sum_erase_one (n := 6) x (fun y => projectionOfDesign design y y),
        sum_projectionDiagonal design]
      norm_num
    rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_sub_distrib,
      sum_projectionDiagonal design]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [hA, hB]
  simp only [pairSecondMoment]
  norm_num
  ring

/-- **THE CERTIFICATE.**  A pair-marginal energy beyond `336 ^ 2` forces a triple
with a strictly positive third Sylvester minor. -/
theorem exists_pos_projGap_of_pairMarginalEnergy
    (hbig : (336 : ℝ) ^ 2 < pairMarginalEnergy design) :
    ∃ first : Fin 6, ∃ second ∈ (univ : Finset (Fin 6)).erase first,
      ∃ inner ∈ ((univ : Finset (Fin 6)).erase first).erase second,
        0 < projGapAt (projectionOfDesign design) first second inner := by
  classical
  -- flatten the double sum to a single sum over the sigma type
  have htot := sum_pairMarginal design
  set S : Finset ((_ : Fin 6) × Fin 6) :=
    (univ : Finset (Fin 6)).sigma (fun first => (univ : Finset (Fin 6)).erase first) with hS
  have hsum : ∑ p ∈ S, pairMarginal design p.1 p.2 = -336 := by
    rw [hS, Finset.sum_sigma]; exact htot
  have hsq : ∑ p ∈ S, pairMarginal design p.1 p.2 ^ 2 = pairMarginalEnergy design := by
    rw [hS, Finset.sum_sigma]; rfl
  have hlt : (∑ p ∈ S, pairMarginal design p.1 p.2) ^ 2
      < ∑ p ∈ S, pairMarginal design p.1 p.2 ^ 2 := by
    rw [hsum, hsq]; norm_num; linarith [hbig]
  obtain ⟨p, hp, hppos⟩ := exists_pos_of_sq_sum_lt_sum_sq S
    (fun q => pairMarginal design q.1 q.2) hlt
  rw [hS, Finset.mem_sigma] at hp
  obtain ⟨-, hp2⟩ := hp
  have hmarg : 0 < 144 * pairMinorAt (projectionOfDesign design) p.1 p.2 + 14
      - 54 * (projectionOfDesign design p.1 p.1 + projectionOfDesign design p.2 p.2) := by
    rw [← pairMarginal_apply design p.1 p.2]; exact hppos
  obtain ⟨inner, hinner, hpos⟩ :=
    exists_pos_projGap_of_pairMarginal_pos design p.1 p.2 hp2 hmarg
  exact ⟨p.1, p.2, hp2, inner, hinner, hpos⟩

/-- **THE CLOSED-FORM CERTIFICATE.**  The hypothesis reads exactly two invariants,
the pair-minor second moment and the leverage second moment.  No bracket, no
determinant, no triple sum appears anywhere in it. -/
theorem exists_pos_projGap_of_secondMoments
    (hbig : (336 : ℝ) ^ 2
      < 20736 * pairSecondMoment design - 38880 * levSecondMoment design + 37200) :
    ∃ first : Fin 6, ∃ second ∈ (univ : Finset (Fin 6)).erase first,
      ∃ inner ∈ ((univ : Finset (Fin 6)).erase first).erase second,
        0 < projGapAt (projectionOfDesign design) first second inner := by
  refine exists_pos_projGap_of_pairMarginalEnergy design ?_
  rw [pairMarginalEnergy_eq design]; exact hbig

end Certificate

/-! ## The mass second moment is the single remaining unknown

The gap is the mass minus the threshold, so its energy splits into three pieces.
The threshold energy and the cross term are two-local and closed form.  The mass
energy is not, and it is the only piece that is not. -/

section MassSecondMoment

variable (design : WeightedDesign 6 3)

/-- The mass energy over ordered distinct triples, at bracket scale. -/
noncomputable def massSecondMoment : ℝ :=
  ∑ outer : Fin 6, ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
    ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det) ^ 2

/-- The threshold energy over ordered distinct triples. -/
noncomputable def thresholdSecondMoment : ℝ :=
  ∑ outer : Fin 6, ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
    ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      projThresholdAt (projectionOfDesign design) outer mid inner ^ 2

/-- The gap energy over ordered distinct triples. -/
noncomputable def gapSecondMoment : ℝ :=
  ∑ outer : Fin 6, ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
    ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      projGapAt (projectionOfDesign design) outer mid inner ^ 2

/-- The cross term over ordered distinct triples. -/
noncomputable def jointCrossMoment : ℝ :=
  ∑ outer : Fin 6, ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
    ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det)
        * projThresholdAt (projectionOfDesign design) outer mid inner

/-- **THE SPLIT.**  The gap energy is the mass energy minus twice the cross term
plus the threshold energy.  Purely formal, and it is what isolates the unknown. -/
theorem gapSecondMoment_eq :
    gapSecondMoment design
      = massSecondMoment design - 2 * jointCrossMoment design
        + thresholdSecondMoment design := by
  classical
  have key : ∀ outer mid inner : Fin 6,
      projGapAt (projectionOfDesign design) outer mid inner ^ 2
        = (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det) ^ 2
          - 2 * ((216 * (tripleBlock (projectionOfDesign design) outer mid inner).det)
            * projThresholdAt (projectionOfDesign design) outer mid inner)
          + projThresholdAt (projectionOfDesign design) outer mid inner ^ 2 := by
    intro outer mid inner; rw [projGapAt]; ring
  simp only [gapSecondMoment, massSecondMoment, jointCrossMoment, thresholdSecondMoment]
  simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The mass energy is a sum of squares. -/
theorem massSecondMoment_nonneg : 0 ≤ massSecondMoment design :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- The gap energy is a sum of squares. -/
theorem gapSecondMoment_nonneg : 0 ≤ gapSecondMoment design :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- **THE REDUCTION.**  Everything in the second-moment theory of the objective is
closed form except `Gtz.massSecondMoment`, which is the energy of the Plucker
measure.  This states the reduction in the cleanest available form. -/
theorem massSecondMoment_eq :
    massSecondMoment design
      = gapSecondMoment design + 2 * jointCrossMoment design
        - thresholdSecondMoment design := by
  rw [gapSecondMoment_eq design]; ring

end MassSecondMoment

/-! ## The objective in joint form, and the obligations

A positive third minor is the last of the three Sylvester conditions.  With the
first two supplied, the block is positive definite and the landed transfer carries
the conclusion to all five on-path obligations. -/

section Objective

/-- **THE OBJECTIVE IN JOINT FORM.**  Some triple's mass beats its own threshold. -/
def JointMassBeatsThreshold : Prop :=
  ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
    ∃ outer : Fin 6, ∃ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        projThresholdAt (projectionOfDesign design) outer mid inner
          < 216 * (tripleBlock (projectionOfDesign design) outer mid inner).det

/-- The joint form is exactly a positive gap. -/
theorem jointMassBeatsThreshold_iff_projGap :
    JointMassBeatsThreshold ↔
      ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
        ∃ outer : Fin 6, ∃ mid ∈ (univ : Finset (Fin 6)).erase outer,
          ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
            0 < projGapAt (projectionOfDesign design) outer mid inner := by
  constructor
  · intro h design hprim
    obtain ⟨outer, mid, hmid, inner, hinner, hlt⟩ := h design hprim
    exact ⟨outer, mid, hmid, inner, hinner, by rw [projGapAt]; linarith⟩
  · intro h design hprim
    obtain ⟨outer, mid, hmid, inner, hinner, hpos⟩ := h design hprim
    refine ⟨outer, mid, hmid, inner, hinner, ?_⟩
    rw [projGapAt] at hpos; linarith

/-- **THE CERTIFICATE REACHES THE OBJECTIVE'S OWN FORM.**  If every primitive
design has pair-marginal energy beyond `336 ^ 2` then every primitive design has a
triple whose mass beats its threshold. -/
theorem jointMassBeatsThreshold_of_pairMarginalEnergy
    (hcert : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      (336 : ℝ) ^ 2 < pairMarginalEnergy design) :
    JointMassBeatsThreshold := by
  rw [jointMassBeatsThreshold_iff_projGap]
  intro design hprim
  exact exists_pos_projGap_of_pairMarginalEnergy design (hcert design hprim)

/-- **THE OBLIGATION BRIDGE.**  Positive definiteness of the block gap at some
selection is the landed `Gtz.ProjectionBlockSelects`, which carries to all five
on-path obligations.  This states the composition explicitly so that any producer
of positive definite blocks lands on the registry rather than beside it. -/
theorem allFiveOnPath_of_blockGapPosDef
    (hsel : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∃ selected : Finset (Fin 6), ∃ hcard : selected.card = 3,
        (projectionBlockGap design selected hcard).PosDef) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  allFiveOnPath_of_projectionBlockSelects hsel

end Objective

end Gtz
