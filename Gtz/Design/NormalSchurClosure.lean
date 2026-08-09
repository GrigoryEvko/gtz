import Gtz.Design.LineClassObstructions
import Gtz.Design.OneDeterminantReduction
import Gtz.Ties.RankTwoMassCircuit
import Gtz.LinAlg.SchurRankOne
import Gtz.Quantitative.DesignQuadraticFloors
import Gtz.Ties.TotalTieCorankOne
import Gtz.Reduction.RayleighCertificate
import Gtz.Reduction.TwoVanishedBoundary
import Gtz.Core.Sanity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The normal-Schur closure of the flat-complement anatomy

Every line stratum hands over a distinguished direction: the normal of a line.
Against that normal the complementary triple is STRICTLY over-covering for free
(`Gtz.complement_strictly_overcovers_normal`), so one of the three Sylvester
conditions on the complementary gap is already discharged.  This file turns that
single free positivity into a complete criterion.

* **The direction-Schur criterion.**  A symmetric matrix with a direction of
  strictly positive Rayleigh value is positive definite exactly when its Schur
  complement at that direction is positive on the orthogonal hyperplane.  Pure
  linear algebra, any rank, no design content.

* **The design reading.**  Instantiated at a domination gap the criterion becomes
  weight-free and quantifier-light: with `h_c` the normal readings and `u_c` the
  in-plane readings of the SELECTED atoms,
  `(S_C - 1).PosDef` iff `|n|^2 < Σ h_c^2` and, at every nonzero in-plane probe,
  `(Σ u_c h_c)^2 < (Σ h_c^2 - |n|^2)(Σ u_c^2 - |p|^2)`.
  Both the line atoms and the weights have vanished from the residual.

* **The blindness closure.**  On a line stratum the complementary triple is
  INDEPENDENT, so no nonzero probe can blind it; combined with the polarised
  Parseval budget carried by that same triple this forbids the readings from
  being proportional.  Strict Cauchy-Schwarz therefore holds at every nonzero
  in-plane probe, unconditionally -- the degenerate branch where all three
  two-by-two minors vanish is EMPTY on both chartless strata.

* **The residual matrix.**  `Gtz.normalSchurResidual` is the explicit symmetric
  matrix that annihilates the normal and reads the Schur complement; adding the
  normal's own rank-one projector makes it positive definite exactly on the
  residual branch, so the substrate's `Gtz.leadingMinors_pos_iff_posDef_fin_three`
  converts the quantified residual into three polynomial signs.
-/

namespace Gtz

open Matrix

variable {rank : ℕ}

/-! ## 1. The direction-Schur criterion -/

/-- Symmetry read as an exchange of the two slots of the pairing. -/
theorem dotProduct_mulVec_swap_of_transpose_eq
    {gapMatrix : Matrix (Fin rank) (Fin rank) ℝ} (hsymm : gapMatrixᵀ = gapMatrix)
    (leftVec rightVec : Fin rank → ℝ) :
    leftVec ⬝ᵥ (gapMatrix *ᵥ rightVec) = rightVec ⬝ᵥ (gapMatrix *ᵥ leftVec) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]

/-- The quadratic form expanded along a direction: a genuine quadratic in the
shift, with the cross term merged by symmetry. -/
theorem dotProduct_mulVec_expand_along_normal
    {gapMatrix : Matrix (Fin rank) (Fin rank) ℝ} (hsymm : gapMatrixᵀ = gapMatrix)
    (planeProbe normalVec : Fin rank → ℝ) (shift : ℝ) :
    (planeProbe + shift • normalVec) ⬝ᵥ (gapMatrix *ᵥ (planeProbe + shift • normalVec))
      = planeProbe ⬝ᵥ (gapMatrix *ᵥ planeProbe)
        + 2 * shift * (planeProbe ⬝ᵥ (gapMatrix *ᵥ normalVec))
        + shift ^ 2 * (normalVec ⬝ᵥ (gapMatrix *ᵥ normalVec)) := by
  have hexpand : (planeProbe + shift • normalVec)
        ⬝ᵥ (gapMatrix *ᵥ (planeProbe + shift • normalVec))
      = planeProbe ⬝ᵥ (gapMatrix *ᵥ planeProbe)
        + shift * (planeProbe ⬝ᵥ (gapMatrix *ᵥ normalVec))
        + shift * (normalVec ⬝ᵥ (gapMatrix *ᵥ planeProbe))
        + shift * shift * (normalVec ⬝ᵥ (gapMatrix *ᵥ normalVec)) := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  rw [hexpand, dotProduct_mulVec_swap_of_transpose_eq hsymm normalVec planeProbe]
  ring

/-- A probe with a nonzero component inside the hyperplane cannot vanish, whatever
the shift along the normal. -/
theorem shiftedPlaneProbe_ne_zero {planeProbe normalVec : Fin rank → ℝ}
    (hplaneOrth : planeProbe ⬝ᵥ normalVec = 0) (hplaneNe : planeProbe ≠ 0) (shift : ℝ) :
    planeProbe + shift • normalVec ≠ 0 := by
  intro hzero
  have hdot : (planeProbe + shift • normalVec) ⬝ᵥ planeProbe = 0 := by
    rw [hzero, zero_dotProduct]
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul,
    dotProduct_comm normalVec planeProbe, hplaneOrth, mul_zero, add_zero] at hdot
  exact (dotProduct_self_pos hplaneNe).ne' hdot

/-- Every probe splits into a hyperplane part and a multiple of the normal. -/
theorem exists_planeSplit_of_ne_zero {normalVec : Fin rank → ℝ} (hnormalNe : normalVec ≠ 0)
    (probeVec : Fin rank → ℝ) :
    ∃ planeProbe : Fin rank → ℝ, ∃ shift : ℝ,
      planeProbe ⬝ᵥ normalVec = 0 ∧ probeVec = planeProbe + shift • normalVec := by
  have hnormPos : 0 < normalVec ⬝ᵥ normalVec := dotProduct_self_pos hnormalNe
  refine ⟨probeVec - ((probeVec ⬝ᵥ normalVec) / (normalVec ⬝ᵥ normalVec)) • normalVec,
    (probeVec ⬝ᵥ normalVec) / (normalVec ⬝ᵥ normalVec), ?_, ?_⟩
  · rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    field_simp
    ring
  · rw [sub_add_cancel]

/-- **The direction-Schur criterion.**  A symmetric matrix is positive definite
exactly when it is strictly positive at one chosen direction and its Schur
complement at that direction is strictly positive on the orthogonal hyperplane.
No unit-length hypothesis: the normal may carry any nonzero length. -/
theorem posDef_iff_normalSchur {gapMatrix : Matrix (Fin rank) (Fin rank) ℝ}
    (hsymm : gapMatrixᵀ = gapMatrix)
    {normalVec : Fin rank → ℝ} (hnormalNe : normalVec ≠ 0) :
    gapMatrix.PosDef ↔
      (0 < normalVec ⬝ᵥ (gapMatrix *ᵥ normalVec) ∧
        ∀ planeProbe : Fin rank → ℝ, planeProbe ⬝ᵥ normalVec = 0 → planeProbe ≠ 0 →
          (planeProbe ⬝ᵥ (gapMatrix *ᵥ normalVec)) ^ 2
            < (normalVec ⬝ᵥ (gapMatrix *ᵥ normalVec))
              * (planeProbe ⬝ᵥ (gapMatrix *ᵥ planeProbe))) := by
  constructor
  · intro hposDef
    have hquad := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2
    have hnormalPos : 0 < normalVec ⬝ᵥ (gapMatrix *ᵥ normalVec) := by
      have hval := hquad hnormalNe
      rwa [star_trivial] at hval
    refine ⟨hnormalPos, ?_⟩
    intro planeProbe hplaneOrth hplaneNe
    have hval := hquad (shiftedPlaneProbe_ne_zero hplaneOrth hplaneNe
      (-((planeProbe ⬝ᵥ (gapMatrix *ᵥ normalVec))
        / (normalVec ⬝ᵥ (gapMatrix *ᵥ normalVec)))))
    rw [star_trivial, dotProduct_mulVec_expand_along_normal hsymm] at hval
    have hnormalNeZero : normalVec ⬝ᵥ (gapMatrix *ᵥ normalVec) ≠ 0 := hnormalPos.ne'
    field_simp at hval
    nlinarith [hval, hnormalPos]
  · rintro ⟨hnormalPos, hschur⟩
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_of_transpose_eq hsymm, ?_⟩
    intro probeVec hprobeNe
    rw [star_trivial]
    obtain ⟨planeProbe, shift, hplaneOrth, hdecomp⟩ :=
      exists_planeSplit_of_ne_zero hnormalNe probeVec
    rw [hdecomp, dotProduct_mulVec_expand_along_normal hsymm]
    by_cases hplaneZero : planeProbe = 0
    · have hshiftNe : shift ≠ 0 := by
        intro hshiftZero
        exact hprobeNe (by rw [hdecomp, hplaneZero, hshiftZero, zero_smul, add_zero])
      rw [hplaneZero, zero_dotProduct, zero_dotProduct]
      have hshiftSqPos : 0 < shift ^ 2 := by positivity
      nlinarith [hnormalPos, hshiftSqPos]
    · have hstrict := hschur planeProbe hplaneOrth hplaneZero
      nlinarith [sq_nonneg (shift * (normalVec ⬝ᵥ (gapMatrix *ᵥ normalVec))
        + planeProbe ⬝ᵥ (gapMatrix *ᵥ normalVec)), hnormalPos, hstrict]

/-! ## 2. The polarised subset-sum forms -/

/-- The unweighted atom sum as a BILINEAR form.  The tree carried only the
diagonal reading `Gtz.dotProduct_subsetSum_mulVec_of_finset`; the cross term is
what a Schur complement needs. -/
theorem dotProduct_subsetSum_mulVec_pair {size : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (probeLeft probeRight : Fin rank → ℝ) :
    probeLeft ⬝ᵥ (subsetSum design selected *ᵥ probeRight)
      = ∑ label ∈ selected,
          (design.atom label ⬝ᵥ probeLeft) * (design.atom label ⬝ᵥ probeRight) := by
  rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun label _ => dotProduct_atomMatrix_mulVec_pair _ _ _

/-- The domination gap as a bilinear form. -/
theorem dominationGap_form_pair {size : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (probeLeft probeRight : Fin rank → ℝ) :
    probeLeft ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probeRight)
      = (∑ label ∈ selected,
          (design.atom label ⬝ᵥ probeLeft) * (design.atom label ⬝ᵥ probeRight))
        - probeLeft ⬝ᵥ probeRight := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, dotProduct_subsetSum_mulVec_pair]

/-! ## 3. The design reading of the criterion -/

/-- **The normal-Schur criterion for a domination gap.**  Weight-free: only the
readings of the SELECTED atoms against the normal and against the in-plane probe
appear.  The first conjunct is the normal over-cover; the second is the whole
residual. -/
theorem posDef_subsetSum_sub_one_iff_normalSchur {size : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    {normalVec : Fin rank → ℝ} (hnormalNe : normalVec ≠ 0) :
    (subsetSum design selected - 1).PosDef ↔
      (normalVec ⬝ᵥ normalVec
          < ∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2 ∧
        ∀ planeProbe : Fin rank → ℝ, planeProbe ⬝ᵥ normalVec = 0 → planeProbe ≠ 0 →
          (∑ label ∈ selected,
              (design.atom label ⬝ᵥ planeProbe) * (design.atom label ⬝ᵥ normalVec)) ^ 2
            < ((∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2)
                - normalVec ⬝ᵥ normalVec)
              * ((∑ label ∈ selected, (design.atom label ⬝ᵥ planeProbe) ^ 2)
                  - planeProbe ⬝ᵥ planeProbe)) := by
  rw [posDef_iff_normalSchur (transpose_subsetSum_sub_one design selected) hnormalNe]
  constructor
  · rintro ⟨hnormalPos, hschur⟩
    rw [dominationGap_form] at hnormalPos
    refine ⟨by linarith, ?_⟩
    intro planeProbe hplaneOrth hplaneNe
    have hstrict := hschur planeProbe hplaneOrth hplaneNe
    rw [dominationGap_form_pair, dominationGap_form, dominationGap_form, hplaneOrth,
      sub_zero] at hstrict
    exact hstrict
  · rintro ⟨hovercover, hschur⟩
    refine ⟨by rw [dominationGap_form]; linarith, ?_⟩
    intro planeProbe hplaneOrth hplaneNe
    have hstrict := hschur planeProbe hplaneOrth hplaneNe
    rw [dominationGap_form_pair, dominationGap_form, dominationGap_form, hplaneOrth, sub_zero]
    exact hstrict

/-! ## 4. The blindness closure: no probe can blind an independent triple -/

/-- Three atoms whose bracket is nonzero cannot all be blind to one nonzero
probe: a common orthogonal kills the bracket. -/
theorem not_all_blind_of_tripleBracket_ne_zero
    {leftVec midVec rightVec probeVec : Fin 3 → ℝ}
    (hbracket : tripleBracket leftVec midVec rightVec ≠ 0) (hprobeNe : probeVec ≠ 0) :
    ¬ (leftVec ⬝ᵥ probeVec = 0 ∧ midVec ⬝ᵥ probeVec = 0 ∧ rightVec ⬝ᵥ probeVec = 0) := by
  rintro ⟨hleft, hmid, hright⟩
  exact hbracket (tripleBracket_eq_zero_of_commonOrthogonal hprobeNe hleft hmid hright)

/-- **An atom off a flat pair has a nonzero height.**  If two atoms of an
independent triple are orthogonal to the normal, the third cannot be. -/
theorem atom_normal_dot_ne_zero_of_atomBracket_ne_zero {size : ℕ}
    (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0)
    (flatFirst flatSecond offLabel : Fin size)
    (hflatFirst : design.atom flatFirst ⬝ᵥ normalVec = 0)
    (hflatSecond : design.atom flatSecond ⬝ᵥ normalVec = 0)
    (hbracket : atomBracket design flatFirst flatSecond offLabel ≠ 0) :
    design.atom offLabel ⬝ᵥ normalVec ≠ 0 := by
  intro hoffZero
  exact hbracket (tripleBracket_eq_zero_of_commonOrthogonal hnormalNe hflatFirst
    hflatSecond hoffZero)

/-- The polarised twin of `Gtz.normalParseval_on_complement`: the MIXED Parseval
budget against a normal and a second probe is carried entirely by the atoms off
the flat set. -/
theorem mixedParseval_on_complement {size : ℕ}
    (design : WeightedDesign size rank) (lineTriple : Finset (Fin size))
    (normalVec planeProbe : Fin rank → ℝ)
    (horthogonal : ∀ lineLabel ∈ lineTriple, design.atom lineLabel ⬝ᵥ normalVec = 0) :
    ∑ freeLabel ∈ lineTripleᶜ,
        design.weight freeLabel
          * ((design.atom freeLabel ⬝ᵥ normalVec) * (design.atom freeLabel ⬝ᵥ planeProbe))
      = normalVec ⬝ᵥ planeProbe := by
  classical
  have hparseval := dotProduct_eq_sum_weight_mul_pair design normalVec planeProbe
  have hlineVanishes : ∑ lineLabel ∈ lineTriple,
      design.weight lineLabel
        * ((design.atom lineLabel ⬝ᵥ normalVec)
            * (design.atom lineLabel ⬝ᵥ planeProbe)) = 0 :=
    Finset.sum_eq_zero fun lineLabel hmem => by rw [horthogonal lineLabel hmem]; ring
  rw [← Finset.sum_add_sum_compl lineTriple
      (fun atomLabel => design.weight atomLabel
        * ((design.atom atomLabel ⬝ᵥ normalVec)
            * (design.atom atomLabel ⬝ᵥ planeProbe))),
    hlineVanishes, zero_add] at hparseval
  exact hparseval.symm

/-- The diagonal budget at any size, read off the polarised one.  The tree's
`Gtz.normalParseval_on_complement` is pinned to `WeightedDesign 6 3`. -/
theorem normalParseval_on_flatComplement {size : ℕ}
    (design : WeightedDesign size rank) (lineTriple : Finset (Fin size))
    (normalVec : Fin rank → ℝ)
    (horthogonal : ∀ lineLabel ∈ lineTriple, design.atom lineLabel ⬝ᵥ normalVec = 0) :
    ∑ freeLabel ∈ lineTripleᶜ,
        design.weight freeLabel * (design.atom freeLabel ⬝ᵥ normalVec) ^ 2
      = normalVec ⬝ᵥ normalVec := by
  classical
  rw [← mixedParseval_on_complement design lineTriple normalVec normalVec horthogonal]
  exact Finset.sum_congr rfl fun label _ => by ring

/-- A three-label sum written out. -/
theorem sum_tripleLabels_eq {size : ℕ} {valueType : Type} [AddCommMonoid valueType]
    (firstLabel secondLabel thirdLabel : Fin size) (values : Fin size → valueType)
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel) :
    ∑ label ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)), values label
      = values firstLabel + values secondLabel + values thirdLabel := by
  classical
  rw [Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
    Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton, add_assoc]

/-- **Strict Cauchy-Schwarz for the readings of a flat complement.**  On a design
whose complementary triple is INDEPENDENT and whose first free atom has nonzero
height, the normal readings and the in-plane readings are never proportional --
so the two-by-two minors never all vanish.  The mixed Parseval budget is what
forces proportionality to collapse to blindness, and blindness is what the
independence forbids.  Unconditional in the weights. -/
theorem strict_cauchySchwarz_readings_of_flatComplement {size : ℕ}
    (design : WeightedDesign size 3) (lineTriple : Finset (Fin size))
    (firstFree secondFree thirdFree : Fin size)
    (hcomplement : lineTripleᶜ = {firstFree, secondFree, thirdFree})
    (hfirstSecond : firstFree ≠ secondFree) (hfirstThird : firstFree ≠ thirdFree)
    (hsecondThird : secondFree ≠ thirdFree)
    (normalVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0)
    (horthogonal : ∀ lineLabel ∈ lineTriple, design.atom lineLabel ⬝ᵥ normalVec = 0)
    (hbracket : atomBracket design firstFree secondFree thirdFree ≠ 0)
    (hfirstHeight : design.atom firstFree ⬝ᵥ normalVec ≠ 0)
    (planeProbe : Fin 3 → ℝ) (hplaneOrth : planeProbe ⬝ᵥ normalVec = 0)
    (hplaneNe : planeProbe ≠ 0) :
    (∑ freeLabel ∈ lineTripleᶜ,
        (design.atom freeLabel ⬝ᵥ planeProbe) * (design.atom freeLabel ⬝ᵥ normalVec)) ^ 2
      < (∑ freeLabel ∈ lineTripleᶜ, (design.atom freeLabel ⬝ᵥ normalVec) ^ 2)
        * (∑ freeLabel ∈ lineTripleᶜ, (design.atom freeLabel ⬝ᵥ planeProbe) ^ 2) := by
  classical
  have hmixed := mixedParseval_on_complement design lineTriple normalVec planeProbe horthogonal
  have hnormalBudget :=
    normalParseval_on_flatComplement design lineTriple normalVec horthogonal
  rw [dotProduct_comm normalVec planeProbe, hplaneOrth] at hmixed
  rw [hcomplement] at hmixed hnormalBudget ⊢
  rw [sum_tripleLabels_eq firstFree secondFree thirdFree _ hfirstSecond hfirstThird
    hsecondThird] at hmixed hnormalBudget ⊢
  rw [sum_tripleLabels_eq firstFree secondFree thirdFree _ hfirstSecond hfirstThird
    hsecondThird, sum_tripleLabels_eq firstFree secondFree thirdFree _ hfirstSecond
    hfirstThird hsecondThird]
  have hnormPos : 0 < normalVec ⬝ᵥ normalVec := dotProduct_self_pos hnormalNe
  by_contra hcontra
  push Not at hcontra
  have hminorsZero :
      (design.atom firstFree ⬝ᵥ normalVec) * (design.atom secondFree ⬝ᵥ planeProbe)
          - (design.atom secondFree ⬝ᵥ normalVec) * (design.atom firstFree ⬝ᵥ planeProbe) = 0
        ∧ (design.atom firstFree ⬝ᵥ normalVec) * (design.atom thirdFree ⬝ᵥ planeProbe)
          - (design.atom thirdFree ⬝ᵥ normalVec) * (design.atom firstFree ⬝ᵥ planeProbe) = 0
        ∧ (design.atom secondFree ⬝ᵥ normalVec) * (design.atom thirdFree ⬝ᵥ planeProbe)
          - (design.atom thirdFree ⬝ᵥ normalVec) * (design.atom secondFree ⬝ᵥ planeProbe) = 0 := by
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [hcontra,
      sq_nonneg ((design.atom firstFree ⬝ᵥ normalVec) * (design.atom secondFree ⬝ᵥ planeProbe)
        - (design.atom secondFree ⬝ᵥ normalVec) * (design.atom firstFree ⬝ᵥ planeProbe)),
      sq_nonneg ((design.atom firstFree ⬝ᵥ normalVec) * (design.atom thirdFree ⬝ᵥ planeProbe)
        - (design.atom thirdFree ⬝ᵥ normalVec) * (design.atom firstFree ⬝ᵥ planeProbe)),
      sq_nonneg ((design.atom secondFree ⬝ᵥ normalVec) * (design.atom thirdFree ⬝ᵥ planeProbe)
        - (design.atom thirdFree ⬝ᵥ normalVec) * (design.atom secondFree ⬝ᵥ planeProbe))]
  obtain ⟨hminorFirstSecond, hminorFirstThird, _⟩ := hminorsZero
  have hfirstBlind : design.atom firstFree ⬝ᵥ planeProbe = 0 := by
    have hweighted : (design.atom firstFree ⬝ᵥ planeProbe) * (normalVec ⬝ᵥ normalVec) = 0 := by
      rw [← hnormalBudget]
      linear_combination (design.atom firstFree ⬝ᵥ normalVec) * hmixed
        - (design.weight secondFree * (design.atom secondFree ⬝ᵥ normalVec))
            * hminorFirstSecond
        - (design.weight thirdFree * (design.atom thirdFree ⬝ᵥ normalVec))
            * hminorFirstThird
    rcases mul_eq_zero.mp hweighted with hzero | hzero
    · exact hzero
    · exact absurd hzero hnormPos.ne'
  have hsecondBlind : design.atom secondFree ⬝ᵥ planeProbe = 0 := by
    have hprod := hminorFirstSecond
    rw [hfirstBlind, mul_zero, sub_zero] at hprod
    rcases mul_eq_zero.mp hprod with hzero | hzero
    · exact absurd hzero hfirstHeight
    · exact hzero
  have hthirdBlind : design.atom thirdFree ⬝ᵥ planeProbe = 0 := by
    have hprod := hminorFirstThird
    rw [hfirstBlind, mul_zero, sub_zero] at hprod
    rcases mul_eq_zero.mp hprod with hzero | hzero
    · exact absurd hzero hfirstHeight
    · exact hzero
  exact not_all_blind_of_tripleBracket_ne_zero hbracket hplaneNe
    ⟨hfirstBlind, hsecondBlind, hthirdBlind⟩

/-! ## 5. The two chartless strata -/

/-- **The flat-line complement's criterion, with the over-cover discharged.**
On any `(6,3)` design carrying a nonempty flat line, the complementary triple
strictly dominates exactly when the plane-Schur inequality holds at every nonzero
in-plane probe.  The normal leg of Sylvester is free. -/
theorem flatLineComplement_posDef_iff_planeSchur (design : WeightedDesign 6 3)
    (lineTriple : Finset (Fin 6)) (hlineNonempty : lineTriple.Nonempty)
    (normalVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0)
    (horthogonal : ∀ lineLabel ∈ lineTriple, design.atom lineLabel ⬝ᵥ normalVec = 0) :
    (subsetSum design lineTripleᶜ - 1).PosDef ↔
      ∀ planeProbe : Fin 3 → ℝ, planeProbe ⬝ᵥ normalVec = 0 → planeProbe ≠ 0 →
        (∑ freeLabel ∈ lineTripleᶜ,
            (design.atom freeLabel ⬝ᵥ planeProbe)
              * (design.atom freeLabel ⬝ᵥ normalVec)) ^ 2
          < ((∑ freeLabel ∈ lineTripleᶜ, (design.atom freeLabel ⬝ᵥ normalVec) ^ 2)
              - normalVec ⬝ᵥ normalVec)
            * ((∑ freeLabel ∈ lineTripleᶜ, (design.atom freeLabel ⬝ᵥ planeProbe) ^ 2)
                - planeProbe ⬝ᵥ planeProbe) := by
  rw [posDef_subsetSum_sub_one_iff_normalSchur design lineTripleᶜ hnormalNe]
  have hovercover := complement_strictly_overcovers_normal design lineTriple normalVec
    hlineNonempty hnormalNe horthogonal
  rw [dotProduct_subsetSum_mulVec_of_finset] at hovercover
  exact ⟨fun hboth => hboth.2, fun hschur => ⟨hovercover, hschur⟩⟩

/-- The one-line stratum's free triple, criterion form. -/
theorem oneLine_freeTriple_posDef_iff_planeSchur (design : WeightedDesign 6 3)
    (normalVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0) :
    (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef ↔
      ∀ planeProbe : Fin 3 → ℝ, planeProbe ⬝ᵥ normalVec = 0 → planeProbe ≠ 0 →
        (∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
            (design.atom freeLabel ⬝ᵥ planeProbe)
              * (design.atom freeLabel ⬝ᵥ normalVec)) ^ 2
          < ((∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
                (design.atom freeLabel ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec)
            * ((∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
                (design.atom freeLabel ⬝ᵥ planeProbe) ^ 2) - planeProbe ⬝ᵥ planeProbe) := by
  have hcriterion := flatLineComplement_posDef_iff_planeSchur design {0, 1, 2}
    ⟨0, by decide⟩ normalVec hnormalNe horthogonal
  rwa [show ({0, 1, 2} : Finset (Fin 6))ᶜ = {3, 4, 5} by decide] at hcriterion

/-- The two-meeting-lines stratum, first line: the complement `{3,4,5}`. -/
theorem twoMeetingLines_firstComplement_posDef_iff_planeSchur (design : WeightedDesign 6 3)
    (normalVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0) :
    (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef ↔
      ∀ planeProbe : Fin 3 → ℝ, planeProbe ⬝ᵥ normalVec = 0 → planeProbe ≠ 0 →
        (∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
            (design.atom freeLabel ⬝ᵥ planeProbe)
              * (design.atom freeLabel ⬝ᵥ normalVec)) ^ 2
          < ((∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
                (design.atom freeLabel ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec)
            * ((∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
                (design.atom freeLabel ⬝ᵥ planeProbe) ^ 2) - planeProbe ⬝ᵥ planeProbe) :=
  oneLine_freeTriple_posDef_iff_planeSchur design normalVec hnormalNe horthogonal

/-- The two-meeting-lines stratum, second line: the complement `{1,2,5}`. -/
theorem twoMeetingLines_secondComplement_posDef_iff_planeSchur (design : WeightedDesign 6 3)
    (normalVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0)
    (horthogonal : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0) :
    (subsetSum design ({1, 2, 5} : Finset (Fin 6)) - 1).PosDef ↔
      ∀ planeProbe : Fin 3 → ℝ, planeProbe ⬝ᵥ normalVec = 0 → planeProbe ≠ 0 →
        (∑ freeLabel ∈ ({1, 2, 5} : Finset (Fin 6)),
            (design.atom freeLabel ⬝ᵥ planeProbe)
              * (design.atom freeLabel ⬝ᵥ normalVec)) ^ 2
          < ((∑ freeLabel ∈ ({1, 2, 5} : Finset (Fin 6)),
                (design.atom freeLabel ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec)
            * ((∑ freeLabel ∈ ({1, 2, 5} : Finset (Fin 6)),
                (design.atom freeLabel ⬝ᵥ planeProbe) ^ 2) - planeProbe ⬝ᵥ planeProbe) := by
  have hcriterion := flatLineComplement_posDef_iff_planeSchur design {0, 3, 4}
    ⟨0, by decide⟩ normalVec hnormalNe horthogonal
  rwa [show ({0, 3, 4} : Finset (Fin 6))ᶜ = {1, 2, 5} by decide] at hcriterion

/-! ### The degenerate branch is empty on both strata -/

/-- **One-line: the readings are never proportional.**  At every nonzero in-plane
probe the free triple's normal readings and in-plane readings satisfy STRICT
Cauchy-Schwarz, so the three two-by-two minors never all vanish.  No heaviness,
no dominator, no tightness. -/
theorem oneLine_strict_cauchySchwarz_freeReadings (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (normalVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0)
    (planeProbe : Fin 3 → ℝ) (hplaneOrth : planeProbe ⬝ᵥ normalVec = 0)
    (hplaneNe : planeProbe ≠ 0) :
    (∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
        (design.atom freeLabel ⬝ᵥ planeProbe) * (design.atom freeLabel ⬝ᵥ normalVec)) ^ 2
      < (∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
          (design.atom freeLabel ⬝ᵥ normalVec) ^ 2)
        * ∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
            (design.atom freeLabel ⬝ᵥ planeProbe) ^ 2 := by
  have hcomplement : ({0, 1, 2} : Finset (Fin 6))ᶜ = {3, 4, 5} := by decide
  have hfreeBracket : atomBracket design 3 4 5 ≠ 0 := fun hzero =>
    absurd ((hpattern 3 4 5 (by decide) (by decide) (by decide)).mp hzero) (by decide)
  have hmixedBracket : atomBracket design 0 1 3 ≠ 0 := fun hzero =>
    absurd ((hpattern 0 1 3 (by decide) (by decide) (by decide)).mp hzero) (by decide)
  have hfirstHeight : design.atom 3 ⬝ᵥ normalVec ≠ 0 :=
    atom_normal_dot_ne_zero_of_atomBracket_ne_zero design normalVec hnormalNe 0 1 3
      (horthogonal 0 (by decide)) (horthogonal 1 (by decide)) hmixedBracket
  have hstrict := strict_cauchySchwarz_readings_of_flatComplement design {0, 1, 2}
    3 4 5 hcomplement (by decide) (by decide) (by decide) normalVec hnormalNe horthogonal
    hfreeBracket hfirstHeight planeProbe hplaneOrth hplaneNe
  rwa [hcomplement] at hstrict

/-- **Two meeting lines, first normal: the readings are never proportional.** -/
theorem twoMeetingLines_firstStrictCauchySchwarz (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (normalVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0)
    (planeProbe : Fin 3 → ℝ) (hplaneOrth : planeProbe ⬝ᵥ normalVec = 0)
    (hplaneNe : planeProbe ≠ 0) :
    (∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
        (design.atom freeLabel ⬝ᵥ planeProbe) * (design.atom freeLabel ⬝ᵥ normalVec)) ^ 2
      < (∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
          (design.atom freeLabel ⬝ᵥ normalVec) ^ 2)
        * ∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
            (design.atom freeLabel ⬝ᵥ planeProbe) ^ 2 := by
  have hcomplement : ({0, 1, 2} : Finset (Fin 6))ᶜ = {3, 4, 5} := by decide
  have hfreeBracket : atomBracket design 3 4 5 ≠ 0 := fun hzero =>
    absurd ((hpattern 3 4 5 (by decide) (by decide) (by decide)).mp hzero) (by decide)
  have hmixedBracket : atomBracket design 0 1 3 ≠ 0 := fun hzero =>
    absurd ((hpattern 0 1 3 (by decide) (by decide) (by decide)).mp hzero) (by decide)
  have hfirstHeight : design.atom 3 ⬝ᵥ normalVec ≠ 0 :=
    atom_normal_dot_ne_zero_of_atomBracket_ne_zero design normalVec hnormalNe 0 1 3
      (horthogonal 0 (by decide)) (horthogonal 1 (by decide)) hmixedBracket
  have hstrict := strict_cauchySchwarz_readings_of_flatComplement design {0, 1, 2}
    3 4 5 hcomplement (by decide) (by decide) (by decide) normalVec hnormalNe horthogonal
    hfreeBracket hfirstHeight planeProbe hplaneOrth hplaneNe
  rwa [hcomplement] at hstrict

/-- **Two meeting lines, second normal: the readings are never proportional.**
The complement of the second line is `{1,2,5}`, which the twin pattern declares
independent; atom `1` carries a nonzero height because `{0,3,1}` is independent
too. -/
theorem twoMeetingLines_secondStrictCauchySchwarz (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (normalVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0)
    (horthogonal : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0)
    (planeProbe : Fin 3 → ℝ) (hplaneOrth : planeProbe ⬝ᵥ normalVec = 0)
    (hplaneNe : planeProbe ≠ 0) :
    (∑ freeLabel ∈ ({1, 2, 5} : Finset (Fin 6)),
        (design.atom freeLabel ⬝ᵥ planeProbe) * (design.atom freeLabel ⬝ᵥ normalVec)) ^ 2
      < (∑ freeLabel ∈ ({1, 2, 5} : Finset (Fin 6)),
          (design.atom freeLabel ⬝ᵥ normalVec) ^ 2)
        * ∑ freeLabel ∈ ({1, 2, 5} : Finset (Fin 6)),
            (design.atom freeLabel ⬝ᵥ planeProbe) ^ 2 := by
  have hcomplement : ({0, 3, 4} : Finset (Fin 6))ᶜ = {1, 2, 5} := by decide
  have hfreeBracket : atomBracket design 1 2 5 ≠ 0 := fun hzero =>
    absurd ((hpattern 1 2 5 (by decide) (by decide) (by decide)).mp hzero) (by decide)
  have hmixedBracket : atomBracket design 0 3 1 ≠ 0 := fun hzero =>
    absurd ((hpattern 0 3 1 (by decide) (by decide) (by decide)).mp hzero) (by decide)
  have hfirstHeight : design.atom 1 ⬝ᵥ normalVec ≠ 0 :=
    atom_normal_dot_ne_zero_of_atomBracket_ne_zero design normalVec hnormalNe 0 3 1
      (horthogonal 0 (by decide)) (horthogonal 3 (by decide)) hmixedBracket
  have hstrict := strict_cauchySchwarz_readings_of_flatComplement design {0, 3, 4}
    1 2 5 hcomplement (by decide) (by decide) (by decide) normalVec hnormalNe horthogonal
    hfreeBracket hfirstHeight planeProbe hplaneOrth hplaneNe
  rwa [hcomplement] at hstrict

/-! ## 6. The residual as one explicit matrix -/

/-- **The normal-Schur residual matrix.**  Scale the gap by its Rayleigh value at
the normal and subtract the rank-one square of the normal's image.  The result
annihilates the normal exactly and reads the Schur complement on the orthogonal
hyperplane. -/
def normalSchurResidual (gapMatrix : Matrix (Fin rank) (Fin rank) ℝ)
    (normalVec : Fin rank → ℝ) : Matrix (Fin rank) (Fin rank) ℝ :=
  (normalVec ⬝ᵥ (gapMatrix *ᵥ normalVec)) • gapMatrix - atomMatrix (gapMatrix *ᵥ normalVec)

/-- The residual matrix is symmetric whenever the gap is. -/
theorem transpose_normalSchurResidual {gapMatrix : Matrix (Fin rank) (Fin rank) ℝ}
    (hsymm : gapMatrixᵀ = gapMatrix) (normalVec : Fin rank → ℝ) :
    (normalSchurResidual gapMatrix normalVec)ᵀ = normalSchurResidual gapMatrix normalVec := by
  rw [normalSchurResidual, Matrix.transpose_sub, Matrix.transpose_smul, hsymm,
    transpose_atomMatrix]

/-- **The residual annihilates the normal.** -/
theorem normalSchurResidual_mulVec_normal_eq_zero
    (gapMatrix : Matrix (Fin rank) (Fin rank) ℝ) (normalVec : Fin rank → ℝ) :
    normalSchurResidual gapMatrix normalVec *ᵥ normalVec = 0 := by
  rw [normalSchurResidual, Matrix.sub_mulVec, Matrix.smul_mulVec,
    atomMatrix_mulVec_eq_dotProduct_smul,
    dotProduct_comm (gapMatrix *ᵥ normalVec) normalVec, sub_self]

/-- The residual's quadratic form IS the Schur discriminant. -/
theorem dotProduct_normalSchurResidual_mulVec
    (gapMatrix : Matrix (Fin rank) (Fin rank) ℝ) (normalVec planeProbe : Fin rank → ℝ) :
    planeProbe ⬝ᵥ (normalSchurResidual gapMatrix normalVec *ᵥ planeProbe)
      = (normalVec ⬝ᵥ (gapMatrix *ᵥ normalVec)) * (planeProbe ⬝ᵥ (gapMatrix *ᵥ planeProbe))
        - (planeProbe ⬝ᵥ (gapMatrix *ᵥ normalVec)) ^ 2 := by
  rw [normalSchurResidual, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec_pair,
    dotProduct_comm (gapMatrix *ᵥ normalVec) planeProbe]
  ring

/-- The residual's cross term against the normal vanishes on the hyperplane. -/
theorem dotProduct_normalSchurResidual_mulVec_normal
    (gapMatrix : Matrix (Fin rank) (Fin rank) ℝ) (normalVec planeProbe : Fin rank → ℝ) :
    planeProbe ⬝ᵥ (normalSchurResidual gapMatrix normalVec *ᵥ normalVec) = 0 := by
  rw [normalSchurResidual_mulVec_normal_eq_zero, dotProduct_zero]

/-- **The residual matrix decides the residual branch.**  Adding the normal's own
rank-one projector fills the kernel; the sum is positive definite exactly when the
Schur discriminant is negative at every nonzero in-plane probe.  Composed with the
substrate's `Gtz.leadingMinors_pos_iff_posDef_fin_three` this turns the quantified
residual into three polynomial sign conditions. -/
theorem posDef_iff_posDef_normalSchurResidual_add_normalSquare
    {gapMatrix : Matrix (Fin rank) (Fin rank) ℝ} (hsymm : gapMatrixᵀ = gapMatrix)
    {normalVec : Fin rank → ℝ} (hnormalNe : normalVec ≠ 0) :
    gapMatrix.PosDef ↔
      (0 < normalVec ⬝ᵥ (gapMatrix *ᵥ normalVec) ∧
        (normalSchurResidual gapMatrix normalVec + atomMatrix normalVec).PosDef) := by
  have hnormPos : 0 < normalVec ⬝ᵥ normalVec := dotProduct_self_pos hnormalNe
  have hfilledSymm : (normalSchurResidual gapMatrix normalVec + atomMatrix normalVec)ᵀ
      = normalSchurResidual gapMatrix normalVec + atomMatrix normalVec := by
    rw [Matrix.transpose_add, transpose_normalSchurResidual hsymm, transpose_atomMatrix]
  have hfilledNormal : normalVec
      ⬝ᵥ ((normalSchurResidual gapMatrix normalVec + atomMatrix normalVec) *ᵥ normalVec)
      = (normalVec ⬝ᵥ normalVec) ^ 2 := by
    rw [Matrix.add_mulVec, dotProduct_add, normalSchurResidual_mulVec_normal_eq_zero,
      dotProduct_zero, zero_add, dotProduct_atomMatrix_mulVec_pair]
    ring
  rw [posDef_iff_normalSchur hsymm hnormalNe,
    posDef_iff_normalSchur hfilledSymm hnormalNe, hfilledNormal]
  constructor
  · rintro ⟨hnormalPos, hschur⟩
    refine ⟨hnormalPos, by positivity, ?_⟩
    intro planeProbe hplaneOrth hplaneNe
    have hcross : planeProbe
        ⬝ᵥ ((normalSchurResidual gapMatrix normalVec + atomMatrix normalVec) *ᵥ normalVec)
        = 0 := by
      rw [Matrix.add_mulVec, dotProduct_add, dotProduct_normalSchurResidual_mulVec_normal,
        zero_add, dotProduct_atomMatrix_mulVec_pair,
        dotProduct_comm normalVec planeProbe, hplaneOrth, zero_mul]
    have hquad : planeProbe
        ⬝ᵥ ((normalSchurResidual gapMatrix normalVec + atomMatrix normalVec) *ᵥ planeProbe)
        = (normalVec ⬝ᵥ (gapMatrix *ᵥ normalVec))
            * (planeProbe ⬝ᵥ (gapMatrix *ᵥ planeProbe))
          - (planeProbe ⬝ᵥ (gapMatrix *ᵥ normalVec)) ^ 2 := by
      rw [Matrix.add_mulVec, dotProduct_add, dotProduct_normalSchurResidual_mulVec,
        dotProduct_atomMatrix_mulVec_pair, dotProduct_comm normalVec planeProbe,
        hplaneOrth, mul_zero, add_zero]
    rw [hcross, hquad]
    have hstrict := hschur planeProbe hplaneOrth hplaneNe
    have hnormSqPos : 0 < (normalVec ⬝ᵥ normalVec) ^ 2 := by positivity
    have hdiscriminantPos : 0 < (normalVec ⬝ᵥ (gapMatrix *ᵥ normalVec))
        * (planeProbe ⬝ᵥ (gapMatrix *ᵥ planeProbe))
        - (planeProbe ⬝ᵥ (gapMatrix *ᵥ normalVec)) ^ 2 := by linarith
    nlinarith [mul_pos hnormSqPos hdiscriminantPos]
  · rintro ⟨hnormalPos, _, hschur⟩
    refine ⟨hnormalPos, ?_⟩
    intro planeProbe hplaneOrth hplaneNe
    have hcross : planeProbe
        ⬝ᵥ ((normalSchurResidual gapMatrix normalVec + atomMatrix normalVec) *ᵥ normalVec)
        = 0 := by
      rw [Matrix.add_mulVec, dotProduct_add, dotProduct_normalSchurResidual_mulVec_normal,
        zero_add, dotProduct_atomMatrix_mulVec_pair,
        dotProduct_comm normalVec planeProbe, hplaneOrth, zero_mul]
    have hquad : planeProbe
        ⬝ᵥ ((normalSchurResidual gapMatrix normalVec + atomMatrix normalVec) *ᵥ planeProbe)
        = (normalVec ⬝ᵥ (gapMatrix *ᵥ normalVec))
            * (planeProbe ⬝ᵥ (gapMatrix *ᵥ planeProbe))
          - (planeProbe ⬝ᵥ (gapMatrix *ᵥ normalVec)) ^ 2 := by
      rw [Matrix.add_mulVec, dotProduct_add, dotProduct_normalSchurResidual_mulVec,
        dotProduct_atomMatrix_mulVec_pair, dotProduct_comm normalVec planeProbe,
        hplaneOrth, mul_zero, add_zero]
    have hstrict := hschur planeProbe hplaneOrth hplaneNe
    rw [hcross, hquad] at hstrict
    have hnormSqPos : 0 < (normalVec ⬝ᵥ normalVec) ^ 2 := by positivity
    norm_num at hstrict
    nlinarith [hstrict, hnormSqPos]

/-- The design instance: one explicit symmetric matrix carries the entire
residual branch of a domination gap. -/
theorem posDef_subsetSum_sub_one_iff_residualMatrix {size : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    {normalVec : Fin rank → ℝ} (hnormalNe : normalVec ≠ 0) :
    (subsetSum design selected - 1).PosDef ↔
      (normalVec ⬝ᵥ normalVec
          < ∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2 ∧
        (normalSchurResidual (subsetSum design selected - 1) normalVec
            + atomMatrix normalVec).PosDef) := by
  rw [posDef_iff_posDef_normalSchurResidual_add_normalSquare
    (transpose_subsetSum_sub_one design selected) hnormalNe, dominationGap_form]
  constructor
  · rintro ⟨hnormalPos, hfilled⟩
    exact ⟨by linarith, hfilled⟩
  · rintro ⟨hovercover, hfilled⟩
    exact ⟨by linarith, hfilled⟩

/-! ## 7. Non-vacuity on the tree's shipped one-line member -/

/-- The vertical direction is nonzero. -/
theorem verticalDirection_ne_zero : (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
  intro hzero
  have hthird := congrFun hzero 2
  simp at hthird

/-- The one-line sample's line lies in the horizontal plane, so the vertical
direction is its line normal. -/
theorem oneLineSample_lineAtoms_orthogonal_to_vertical :
    ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      oneLineSampleDesign.atom lineLabel ⬝ᵥ ![0, 0, 1] = 0 := by
  intro lineLabel hmem
  fin_cases hmem <;>
    simp [oneLineSampleDesign, oneLineSampleAtom, dotProduct, Fin.sum_univ_three]

/-- **The residual criterion fires on the shipped one-line member.**  The sample's
free triple is strictly dominating, so its plane-Schur inequality holds at every
nonzero horizontal probe -- the criterion is not vacuously true. -/
theorem oneLineSample_planeSchur_holds :
    ∀ planeProbe : Fin 3 → ℝ, planeProbe ⬝ᵥ ![0, 0, 1] = 0 → planeProbe ≠ 0 →
      (∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
          (oneLineSampleDesign.atom freeLabel ⬝ᵥ planeProbe)
            * (oneLineSampleDesign.atom freeLabel ⬝ᵥ ![0, 0, 1])) ^ 2
        < ((∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
              (oneLineSampleDesign.atom freeLabel ⬝ᵥ ![0, 0, 1]) ^ 2)
            - (![0, 0, 1] : Fin 3 → ℝ) ⬝ᵥ ![0, 0, 1])
          * ((∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
                (oneLineSampleDesign.atom freeLabel ⬝ᵥ planeProbe) ^ 2)
              - planeProbe ⬝ᵥ planeProbe) :=
  (oneLine_freeTriple_posDef_iff_planeSchur oneLineSampleDesign ![0, 0, 1]
    verticalDirection_ne_zero oneLineSample_lineAtoms_orthogonal_to_vertical).mp
    oneLineSample_freeTripleGap_posDef

/-- The branch closure fires on the shipped member too. -/
theorem oneLineSample_strict_cauchySchwarz (planeProbe : Fin 3 → ℝ)
    (hplaneOrth : planeProbe ⬝ᵥ ![0, 0, 1] = 0) (hplaneNe : planeProbe ≠ 0) :
    (∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
        (oneLineSampleDesign.atom freeLabel ⬝ᵥ planeProbe)
          * (oneLineSampleDesign.atom freeLabel ⬝ᵥ ![0, 0, 1])) ^ 2
      < (∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
          (oneLineSampleDesign.atom freeLabel ⬝ᵥ ![0, 0, 1]) ^ 2)
        * ∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
            (oneLineSampleDesign.atom freeLabel ⬝ᵥ planeProbe) ^ 2 :=
  oneLine_strict_cauchySchwarz_freeReadings oneLineSampleDesign
    oneLineSampleDesign_hasLinePattern ![0, 0, 1] verticalDirection_ne_zero
    oneLineSample_lineAtoms_orthogonal_to_vertical planeProbe hplaneOrth hplaneNe

end Gtz
