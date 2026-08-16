import Gtz.Design.KFourChartClosure
import Gtz.Design.KFourLeverageRefuter

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The K4 chart as a weighted graph: unimodularity, the matrix-tree law, the star
Laplacian, and the refutation of the minimum-threshold designation

The `M(K4)` stratum is the moduli-zero class, and its registry ledger records a
kernel refutation of every designation tried so far: the max-conductance edge,
the dominant mass pair, the max-alpha edge, the max-leverage edge, determinant
argmax and its pair variant, and all four invariant-argmax rules on `D1`, `D2`,
`D3`.  This module refutes one more and then supplies the structure that explains
why the whole family keeps failing.

## The threshold, and why it fails

`Gtz.tripleThreshold` in projection coordinates is `det P_S - det (P_S - diag w)`,
the value the determinantal weight must beat.  Its chart analogue is
`Gtz.kFourChartThreshold`: the determinant of the boosted selected moment minus
the determinant of the chart gap, with the full mass moment in the role of the
weight diagonal.  At the graphic point of `K4` that threshold separates the four
dominating stars from the twelve paths, which suggested the designation "the
spanning tree of minimum threshold hosts a strict tree".

The designation is FALSE.  At `Gtz.bandResidualWitnessPoint`, the canonical
inhabitant of the surviving band, the minimum-threshold tree is the star
`{0, 2, 4}` with threshold `399`, while the hosting star `{1, 2, 5}` has threshold
`29219` — a factor of seventy-three — and the minimiser does not dominate.  At
`Gtz.heavyPairRefuterPoint` the minimum-threshold tree `{1, 2, 5}` has a NEGATIVE
threshold and a strictly positive gap determinant, and still fails to dominate.

The mechanism is visible in the definition.  By
`Gtz.det_directionChartGap_eq_sub_threshold`, lowering the threshold at a fixed
selected determinant RAISES the gap determinant, so the rule is a determinant
reading wearing different clothes, and the ledger already records that determinant
positivity does not imply hosting.  `Gtz.heavyPair_detPos_notHost` exhibits that
collision at the minimiser itself.

## What replaces it

The six K4 edge vectors are totally unimodular.  Three consequences follow, and
they are the mathematics here.

* `Gtz.sq_tripleBracket_kFourDirection_eq_zero_or_one` — every bracket squares to
  `0` or `1`, and off the four triangles it is `1`.  So on this stratum the
  determinantal measure carries NO directional information: by
  `Gtz.det_kFourSelectedMoment_star` the selected determinant is the plain product
  of the three boosts, a product measure over the bases.
* `Gtz.det_kFourMassMoment_eq_treeSum` — the mass moment's determinant is the sum
  over the sixteen spanning trees of the product of that tree's masses.  This is
  Kirchhoff's matrix-tree theorem, and it identifies the campaign's Cauchy-Binet
  mass law with a spanning-tree count on the graphic stratum.  At unit masses it
  returns `16`, Cayley's count for `K4` (`Gtz.det_kFourMassMoment_one`).
* `Gtz.directionChartGap_star_eq` — at the canonical star the chart gap is
  congruent, by an integer matrix of determinant one, to `D - L`, where `D` is the
  diagonal of heavy tree masses `m_c (1 - w_c) / w_c` and `L` is the Laplacian of
  a triangle whose three edge weights are the three off-tree masses.  Exact, and
  for every mass and weight.

That last one turns the star branch of the obligation into a statement with no
frame, no whitener and no square root, and `Gtz.posDef_directionChartGap_star_iff`
makes it an equivalence: **the canonical star dominates exactly when the `3 x 3`
matrix whose off-diagonal entries are the three off-tree masses, and whose
diagonal is each tree edge's heavy mass less the two off-tree masses meeting it,
is positive definite.**  The registry's
`Gtz.obligationKnifeBandRefinedKFour_of_gaugeStarAndPivotAtlasFires` asks for atlas
firing at the canonical gauge star, and this is that star's gap in closed form.
-/

namespace Gtz

open Matrix

/-! ## 1. The selected moment, the mass moment, and the chart threshold -/

/-- The boosted moment of a selection: the first half of the chart gap. -/
noncomputable def kFourSelectedMoment (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ label ∈ selected, (mass label / weight label) • atomMatrix (kFourDirection label)

/-- The full mass moment of the K4 chart: the second half of the chart gap. -/
noncomputable def kFourMassMoment (mass : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ label, mass label • atomMatrix (kFourDirection label)

theorem directionChartGap_kFour_eq (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) :
    directionChartGap kFourDirection mass weight selected
      = kFourSelectedMoment mass weight selected - kFourMassMoment mass := rfl

/-- **The chart threshold.**  The exact analogue of `Gtz.tripleThreshold`, with the
mass moment in place of the weight diagonal: the leading determinant minus the
shifted one. -/
noncomputable def kFourChartThreshold (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) : ℝ :=
  (kFourSelectedMoment mass weight selected).det
    - (directionChartGap kFourDirection mass weight selected).det

/-- **THE THRESHOLD IS A DETERMINANT READING.**  The gap determinant is the
selected determinant minus the threshold, so lowering the threshold at a fixed
selected determinant raises the gap determinant.  Every rule that prefers a small
threshold is therefore a rule that prefers a large gap determinant, and the
registry ledger already refutes that family. -/
theorem det_directionChartGap_eq_sub_threshold (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) :
    (directionChartGap kFourDirection mass weight selected).det
      = (kFourSelectedMoment mass weight selected).det
          - kFourChartThreshold mass weight selected := by
  rw [kFourChartThreshold]; ring

/-! ## 2. The basis congruence, at every stratum

Nothing below this heading is `K4`-specific.  Pick any selection whose three
directions are a basis, express every direction in that basis, and the chart gap
splits into a diagonal of heavy selected masses minus the moment of the
off-selection coordinate vectors.  The congruence needs no inverse in its
statement: it takes the coordinates as given data and checks them forward. -/

/-- Pushing a vector through a matrix conjugates its atom. -/
theorem atomMatrix_mulVec_tree (transform : Matrix (Fin 3) (Fin 3) ℝ) (vecArg : Fin 3 → ℝ) :
    atomMatrix (transform *ᵥ vecArg)
      = transform * atomMatrix vecArg * transformᵀ := by
  ext rowIndex colIndex
  simp [atomMatrix, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three]
  ring

/-- **THE BASIS CONGRUENCE, AT EVERY STRATUM.**  Given coordinates for every
direction in a chosen basis, the chart gap is that basis conjugating the
difference of two moments: the selected labels enter with their HEAVY mass
`m_c / w_c - m_c`, and the unselected ones subtract their plain mass.

At a spanning tree of the graphic stratum the second moment is a graph Laplacian,
which is section 4.  At the line strata the same statement holds with the
coordinate vectors of the lines. -/
theorem directionChartGap_congr_basis {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size)) (basis : Matrix (Fin 3) (Fin 3) ℝ)
    (coord : Fin size → (Fin 3 → ℝ))
    (hcoord : ∀ label, basis *ᵥ coord label = direction label) :
    directionChartGap direction mass weight selected
      = basis *
          ((∑ label ∈ selected,
              (mass label / weight label - mass label) • atomMatrix (coord label))
            - ∑ label ∈ selectedᶜ, mass label • atomMatrix (coord label)) * basisᵀ := by
  have hatom : ∀ label, atomMatrix (direction label)
      = basis * atomMatrix (coord label) * basisᵀ := by
    intro label; rw [← hcoord label, atomMatrix_mulVec_tree]
  have hpush : ∀ (scale : Fin size → ℝ) (part : Finset (Fin size)),
      basis * (∑ label ∈ part, scale label • atomMatrix (coord label)) * basisᵀ
        = ∑ label ∈ part, scale label • atomMatrix (direction label) := by
    intro scale part
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, ← hatom label]
  have hsplit : ∑ label, mass label • atomMatrix (direction label)
      = (∑ label ∈ selected, mass label • atomMatrix (direction label))
        + ∑ label ∈ selectedᶜ, mass label • atomMatrix (direction label) := by
    rw [← Finset.sum_add_sum_compl selected]
  have hdist : ∑ label ∈ selected,
        (mass label / weight label - mass label) • atomMatrix (direction label)
      = (∑ label ∈ selected, (mass label / weight label) • atomMatrix (direction label))
        - ∑ label ∈ selected, mass label • atomMatrix (direction label) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by rw [sub_smul]
  rw [Matrix.mul_sub, Matrix.sub_mul, hpush, hpush, hdist]
  simp only [directionChartGap, hsplit]
  abel

/-- Positive definiteness transports across a congruence by any matrix carrying a
two-sided inverse, in both directions.  No `Matrix.inv` appears: the inverse is
supplied as data and checked forward. -/
theorem posDef_congr_of_inverse {dim : ℕ}
    (basis basisInv form : Matrix (Fin dim) (Fin dim) ℝ)
    (hleft : basisInv * basis = 1) (hright : basis * basisInv = 1) :
    (basis * form * basisᵀ).PosDef ↔ form.PosDef := by
  have hinjBasis : Function.Injective (fun vecArg : Fin dim → ℝ => vecArg ᵥ* basis) := by
    intro leftVec rightVec heq
    have hstep := congrArg (fun u : Fin dim → ℝ => u ᵥ* basisInv) heq
    simpa [Matrix.vecMul_vecMul, hright] using hstep
  have hinjInv : Function.Injective (fun vecArg : Fin dim → ℝ => vecArg ᵥ* basisInv) := by
    intro leftVec rightVec heq
    have hstep := congrArg (fun u : Fin dim → ℝ => u ᵥ* basis) heq
    simpa [Matrix.vecMul_vecMul, hleft] using hstep
  constructor
  · intro hpd
    have hback := hpd.mul_mul_conjTranspose_same (B := basisInv) hinjInv
    have htrans : basisᵀ * basisInvᵀ = 1 := by
      rw [← Matrix.transpose_mul, hleft, Matrix.transpose_one]
    have hid : basisInv * (basis * form * basisᵀ) * basisInvᴴ = form := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial,
        ← Matrix.mul_assoc basisInv (basis * form) basisᵀ,
        ← Matrix.mul_assoc basisInv basis form, hleft, Matrix.one_mul,
        Matrix.mul_assoc form basisᵀ basisInvᵀ, htrans, Matrix.mul_one]
    rwa [hid] at hback
  · intro hpd
    exact hpd.mul_mul_conjTranspose_same (B := basis) hinjBasis

/-- **THE HEAVINESS CONDITION, AT EVERY STRATUM.**  A dominating selection must, in
each coordinate slot of its own basis, carry more heavy mass than the unselected
labels carry plain mass.  Weighted by the squared coordinates, and reading nothing
but masses, weights and coordinates — no bracket, no determinant, no eigenvalue.

This is the stratum-independent form of the K4 star heaviness of section 5, and
it applies verbatim to the line-free, one-line, two-meeting-lines and three-lines
charts once their coordinate vectors are supplied. -/
theorem heaviness_of_posDef_congr {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size)) (basis basisInv : Matrix (Fin 3) (Fin 3) ℝ)
    (coord : Fin size → (Fin 3 → ℝ))
    (hcoord : ∀ label, basis *ᵥ coord label = direction label)
    (hleft : basisInv * basis = 1) (hright : basis * basisInv = 1)
    (hpd : (directionChartGap direction mass weight selected).PosDef)
    (slot : Fin 3) :
    (∑ label ∈ selectedᶜ, mass label * coord label slot ^ 2)
      < ∑ label ∈ selected,
          (mass label / weight label - mass label) * coord label slot ^ 2 := by
  rw [directionChartGap_congr_basis direction mass weight selected basis coord hcoord,
    posDef_congr_of_inverse basis basisInv _ hleft hright] at hpd
  have hdiag := hpd.diag_pos (i := slot)
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul, sub_pos] at hdiag
  have hrw : ∀ (scale : Fin size → ℝ) (part : Finset (Fin size)),
      ∑ label ∈ part, scale label * (coord label slot * coord label slot)
        = ∑ label ∈ part, scale label * coord label slot ^ 2 :=
    fun scale part => Finset.sum_congr rfl fun label _ => by ring
  rw [hrw, hrw] at hdiag
  exact hdiag

/-! ## 3. Total unimodularity of the K4 edge family -/

/-- **TOTAL UNIMODULARITY.**  Every bracket of three K4 edge vectors squares to
`0` or `1`: each basis has determinant one in absolute value and each circuit has
determinant zero. -/
theorem sq_tripleBracket_kFourDirection_eq_zero_or_one (labelA labelB labelC : Fin 6) :
    (tripleBracket (kFourDirection labelA) (kFourDirection labelB)
        (kFourDirection labelC)) ^ 2 = 0 ∨
      (tripleBracket (kFourDirection labelA) (kFourDirection labelB)
        (kFourDirection labelC)) ^ 2 = 1 := by
  fin_cases labelA <;> fin_cases labelB <;> fin_cases labelC <;>
    norm_num [tripleBracket, kFourDirection, Matrix.det_fin_three,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- On a spanning tree — three distinct labels off the four triangles — the squared
bracket is exactly one.  The zero classification is the landed
`Gtz.tripleBracket_kFourDirection_eq_zero_iff`. -/
theorem sq_tripleBracket_kFourDirection_eq_one (labelA labelB labelC : Fin 6)
    (hab : labelA ≠ labelB) (hac : labelA ≠ labelC) (hbc : labelB ≠ labelC)
    (hspan : ¬ lineFamilyPattern graphicKFourFamily labelA labelB labelC) :
    (tripleBracket (kFourDirection labelA) (kFourDirection labelB)
      (kFourDirection labelC)) ^ 2 = 1 := by
  rcases sq_tripleBracket_kFourDirection_eq_zero_or_one labelA labelB labelC with hzero | hone
  · exact absurd ((tripleBracket_kFourDirection_eq_zero_iff labelA labelB labelC
      hab hac hbc).mp (by nlinarith [hzero])) hspan
  · exact hone

/-! ## 3. The star basis, its Laplacian, and the exact congruence

Write the canonical star at vertex `a` as the tree `{0, 1, 3}` — edges `ab`, `ac`,
`ad` in the corpus labelling, where `{0,1,2}` is `abc`, `{0,3,4}` is `abd`,
`{1,3,5}` is `acd` and `{2,4,5}` is `bcd`.  Its three off-tree edges are `2 = bc`,
`4 = bd`, `5 = cd`, and the fundamental cycles are `v 2 = v 1 - v 0`,
`v 4 = v 3 - v 0`, `v 5 = v 3 - v 1`.  In the tree basis those cycle vectors are
differences of standard basis vectors, so the off-tree part of the mass moment is
the Laplacian of a triangle whose edge weights are the off-tree masses. -/

/-- The tree basis of the canonical star, with the three tree edge vectors as
columns.  It is an integer matrix of determinant one. -/
def kFourStarBasis : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![![1, 1, 1], ![-1, 0, 0], ![0, -1, 0]]

theorem det_kFourStarBasis : kFourStarBasis.det = 1 := by
  simp [kFourStarBasis, Matrix.det_fin_three]

/-- **The star's gap in tree coordinates.**  The off-diagonal entries are exactly
the three off-tree masses, and each diagonal entry is that tree edge's heavy mass
less the two off-tree masses whose fundamental cycles meet it.  This is
`D - L` with `L` the triangle Laplacian. -/
noncomputable def kFourStarGap (mass weight : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of
    ![![mass 0 * (1 - weight 0) / weight 0 - mass 2 - mass 4, mass 2, mass 4],
      ![mass 2, mass 1 * (1 - weight 1) / weight 1 - mass 2 - mass 5, mass 5],
      ![mass 4, mass 5, mass 3 * (1 - weight 3) / weight 3 - mass 4 - mass 5]]

/-- The mass moment in the same tree coordinates: the tree masses on the diagonal
plus the very same triangle Laplacian. -/
noncomputable def kFourStarMass (mass : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of
    ![![mass 0 + mass 2 + mass 4, -mass 2, -mass 4],
      ![-mass 2, mass 1 + mass 2 + mass 5, -mass 5],
      ![-mass 4, -mass 5, mass 3 + mass 4 + mass 5]]

/-- **THE STAR CONGRUENCE.**  The chart gap of the canonical star is its
tree-coordinate gap conjugated by an integer matrix of determinant one, for EVERY
mass and weight with the three tree weights nonzero.  No frame, no whitener, no
square root. -/
theorem directionChartGap_star_eq (mass weight : Fin 6 → ℝ)
    (h0 : weight 0 ≠ 0) (h1 : weight 1 ≠ 0) (h3 : weight 3 ≠ 0) :
    directionChartGap kFourDirection mass weight {0, 1, 3}
      = kFourStarBasis * kFourStarGap mass weight * kFourStarBasisᵀ := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourStarBasis, kFourStarGap, kFourDirection, atomMatrix,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.sub_apply] <;>
    field_simp <;> ring

/-- **THE MASS MOMENT IN TREE COORDINATES.**  The same congruence carries the full
mass moment to the tree masses plus the triangle Laplacian. -/
theorem kFourMassMoment_star_eq (mass : Fin 6 → ℝ) :
    kFourMassMoment mass = kFourStarBasis * kFourStarMass mass * kFourStarBasisᵀ := by
  simp only [kFourMassMoment]
  rw [Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourStarBasis, kFourStarMass, kFourDirection, atomMatrix,
      Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- The explicit integer inverse of the star basis: the cycle-space reading. -/
def kFourStarBasisInv : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![![0, -1, 0], ![0, 0, -1], ![1, 1, 1]]

theorem kFourStarBasis_mul_inv : kFourStarBasis * kFourStarBasisInv = 1 := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourStarBasis, kFourStarBasisInv, Matrix.mul_apply, Fin.sum_univ_three]

theorem kFourStarBasisInv_mul : kFourStarBasisInv * kFourStarBasis = 1 := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourStarBasis, kFourStarBasisInv, Matrix.mul_apply, Fin.sum_univ_three]

/-- Positive definiteness transports across the unimodular star congruence in both
directions. -/
theorem posDef_star_congr_iff (form : Matrix (Fin 3) (Fin 3) ℝ) :
    (kFourStarBasis * form * kFourStarBasisᵀ).PosDef ↔ form.PosDef :=
  posDef_congr_of_inverse kFourStarBasis kFourStarBasisInv form
    kFourStarBasisInv_mul kFourStarBasis_mul_inv

/-- **THE CANONICAL STAR DOMINATES EXACTLY WHEN ITS TRIANGLE MATRIX IS POSITIVE
DEFINITE.**  The star branch of the K4 obligation is a statement about one
explicit `3 x 3` matrix built from three tree masses, three tree weights, and the
three off-tree masses — nothing else. -/
theorem posDef_directionChartGap_star_iff (mass weight : Fin 6 → ℝ)
    (h0 : weight 0 ≠ 0) (h1 : weight 1 ≠ 0) (h3 : weight 3 ≠ 0) :
    (directionChartGap kFourDirection mass weight {0, 1, 3}).PosDef
      ↔ (kFourStarGap mass weight).PosDef := by
  rw [directionChartGap_star_eq mass weight h0 h1 h3, posDef_star_congr_iff]

/-- The star gap determinant equals the chart gap determinant: the congruence is
unimodular. -/
theorem det_directionChartGap_star (mass weight : Fin 6 → ℝ)
    (h0 : weight 0 ≠ 0) (h1 : weight 1 ≠ 0) (h3 : weight 3 ≠ 0) :
    (directionChartGap kFourDirection mass weight {0, 1, 3}).det
      = (kFourStarGap mass weight).det := by
  rw [directionChartGap_star_eq mass weight h0 h1 h3, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, det_kFourStarBasis]
  ring

theorem det_kFourMassMoment_star (mass : Fin 6 → ℝ) :
    (kFourMassMoment mass).det = (kFourStarMass mass).det := by
  rw [kFourMassMoment_star_eq mass, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, det_kFourStarBasis]
  ring

/-- **THE STAR HEAVINESS CONDITION.**  A dominating canonical star has, at each of
its three edges, heavy mass strictly greater than the sum of the two off-tree
masses whose fundamental cycles meet that edge.  Immediate from the congruence and
the positivity of a positive-definite diagonal, and it reads only masses and
weights — no bracket, no determinant, no eigenvalue. -/
theorem starHeaviness_of_posDef (mass weight : Fin 6 → ℝ)
    (h0 : weight 0 ≠ 0) (h1 : weight 1 ≠ 0) (h3 : weight 3 ≠ 0)
    (hpd : (directionChartGap kFourDirection mass weight {0, 1, 3}).PosDef) :
    mass 2 + mass 4 < mass 0 * (1 - weight 0) / weight 0 ∧
      mass 2 + mass 5 < mass 1 * (1 - weight 1) / weight 1 ∧
        mass 4 + mass 5 < mass 3 * (1 - weight 3) / weight 3 := by
  have hstar := (posDef_directionChartGap_star_iff mass weight h0 h1 h3).mp hpd
  refine ⟨?_, ?_, ?_⟩
  · have := hstar.diag_pos (i := (0 : Fin 3)); simp [kFourStarGap] at this; linarith
  · have := hstar.diag_pos (i := (1 : Fin 3)); simp [kFourStarGap] at this; linarith
  · have := hstar.diag_pos (i := (2 : Fin 3)); simp [kFourStarGap] at this; linarith

/-! ## 3b. The star is an instance of the general congruence

The tree edges carry the standard basis vectors, and each off-tree edge carries its
FUNDAMENTAL CYCLE with respect to the star: `v 2 = v 1 - v 0`, `v 4 = v 3 - v 0`,
`v 5 = v 3 - v 1`.  Those three cycle vectors are differences of standard basis
vectors, which is exactly why the off-tree moment is a graph Laplacian. -/

/-- Coordinates of every K4 edge in the canonical star's basis: standard vectors on
the tree, fundamental cycles off it. -/
def kFourStarCoord : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![-1, 1, 0]
  | 3 => ![0, 0, 1]
  | 4 => ![-1, 0, 1]
  | 5 => ![0, -1, 1]

/-- **THE FUNDAMENTAL-CYCLE CHECK.**  Every K4 edge is its coordinate vector pushed
through the star basis, so the general congruence applies at this stratum. -/
theorem kFourStarBasis_mulVec_coord (label : Fin 6) :
    kFourStarBasis *ᵥ kFourStarCoord label = kFourDirection label := by
  fin_cases label <;>
    · ext slot
      fin_cases slot <;>
        simp [kFourStarBasis, kFourStarCoord, kFourDirection, Matrix.mulVec,
          dotProduct, Fin.sum_univ_three]

/-- **THE GENERAL CONGRUENCE SPECIALIZES TO THE STAR.**  Independent confirmation
that `Gtz.directionChartGap_congr_basis` reproduces the hand-computed
`Gtz.directionChartGap_star_eq`, and hence that the general machinery is live at
the moduli-zero stratum. -/
theorem directionChartGap_star_eq_of_congr (mass weight : Fin 6 → ℝ) :
    directionChartGap kFourDirection mass weight {0, 1, 3}
      = kFourStarBasis *
          ((∑ label ∈ ({0, 1, 3} : Finset (Fin 6)),
              (mass label / weight label - mass label) • atomMatrix (kFourStarCoord label))
            - ∑ label ∈ ({0, 1, 3} : Finset (Fin 6))ᶜ,
                mass label • atomMatrix (kFourStarCoord label)) * kFourStarBasisᵀ :=
  directionChartGap_congr_basis kFourDirection mass weight {0, 1, 3} kFourStarBasis
    kFourStarCoord kFourStarBasis_mulVec_coord

/-- **THE HEAVINESS CONDITION AT THE STAR, VIA THE GENERAL ROUTE.**  The same three
inequalities as `Gtz.starHeaviness_of_posDef`, obtained from the stratum-independent
`Gtz.heaviness_of_posDef_congr` rather than from the hand congruence.  Two
independent derivations of the same fact. -/
theorem starHeaviness_of_posDef_congr (mass weight : Fin 6 → ℝ)
    (hpd : (directionChartGap kFourDirection mass weight {0, 1, 3}).PosDef)
    (slot : Fin 3) :
    (∑ label ∈ ({0, 1, 3} : Finset (Fin 6))ᶜ,
        mass label * kFourStarCoord label slot ^ 2)
      < ∑ label ∈ ({0, 1, 3} : Finset (Fin 6)),
          (mass label / weight label - mass label) * kFourStarCoord label slot ^ 2 :=
  heaviness_of_posDef_congr kFourDirection mass weight {0, 1, 3} kFourStarBasis
    kFourStarBasisInv kFourStarCoord kFourStarBasis_mulVec_coord
    kFourStarBasisInv_mul kFourStarBasis_mul_inv hpd slot

/-! ## 4. The matrix-tree law -/

/-- **THE MATRIX-TREE LAW AT THE K4 CHART.**  The determinant of the mass moment is
the sum over the sixteen spanning trees of the product of that tree's masses.
This is Kirchhoff's theorem, and it identifies the campaign's Cauchy-Binet mass law
with a spanning-tree count on the graphic stratum. -/
theorem det_kFourMassMoment_eq_treeSum (mass : Fin 6 → ℝ) :
    (kFourMassMoment mass).det
      = mass 0 * mass 1 * mass 3 + mass 0 * mass 1 * mass 4 + mass 0 * mass 1 * mass 5
        + mass 0 * mass 2 * mass 3 + mass 0 * mass 2 * mass 4 + mass 0 * mass 2 * mass 5
        + mass 0 * mass 3 * mass 5 + mass 0 * mass 4 * mass 5
        + mass 1 * mass 2 * mass 3 + mass 1 * mass 2 * mass 4 + mass 1 * mass 2 * mass 5
        + mass 1 * mass 3 * mass 4 + mass 1 * mass 4 * mass 5
        + mass 2 * mass 3 * mass 4 + mass 2 * mass 3 * mass 5
        + mass 3 * mass 4 * mass 5 := by
  rw [det_kFourMassMoment_star, kFourStarMass, Matrix.det_fin_three]
  simp [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **CAYLEY'S COUNT.**  At unit masses the mass moment's determinant is sixteen,
the number of spanning trees of `K4`. -/
theorem det_kFourMassMoment_one : (kFourMassMoment (fun _ => (1 : ℝ))).det = 16 := by
  rw [det_kFourMassMoment_eq_treeSum]; norm_num

/-- **THE DETERMINANTAL MEASURE IS A PRODUCT MEASURE ON THIS STRATUM.**  The star's
selected determinant is the plain product of its three boosts, because the bracket
contributes exactly one.  So no reading of the selected determinant can see the
directions. -/
theorem det_kFourSelectedMoment_star (mass weight : Fin 6 → ℝ) :
    (kFourSelectedMoment mass weight {0, 1, 3}).det
      = (mass 0 / weight 0) * (mass 1 / weight 1) * (mass 3 / weight 3) := by
  simp only [kFourSelectedMoment]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Matrix.det_fin_three]
  simp [kFourDirection, atomMatrix, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-! ## 5. The refutation at `Gtz.bandResidualWitnessPoint`

The canonical inhabitant of the surviving band.  Its minimum-threshold spanning
tree is the star `{0, 2, 4}` at vertex `b`, with threshold `399`, and it does not
dominate: the gap's leading diagonal entry is `-14` even though its determinant
`601` is positive. -/

theorem band_gap_zeroTwoFour_det :
    (directionChartGap kFourDirection bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight {0, 2, 4}).det = 601 := by
  simp only [directionChartGap, bandResidualWitnessPoint_mass_eq,
    bandResidualWitnessPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [bandResidualWitnessMass, bandResidualWitnessWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem band_selected_zeroTwoFour_det :
    (kFourSelectedMoment bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight {0, 2, 4}).det = 1000 := by
  simp only [kFourSelectedMoment, bandResidualWitnessPoint_mass_eq,
    bandResidualWitnessPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num [bandResidualWitnessMass, bandResidualWitnessWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem band_threshold_zeroTwoFour :
    kFourChartThreshold bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight {0, 2, 4} = 399 := by
  rw [kFourChartThreshold, band_selected_zeroTwoFour_det, band_gap_zeroTwoFour_det]
  norm_num

theorem band_gap_zeroTwoFour_diag :
    (directionChartGap kFourDirection bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight {0, 2, 4}) 0 0 = -14 := by
  simp only [directionChartGap, bandResidualWitnessPoint_mass_eq,
    bandResidualWitnessPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [bandResidualWitnessMass, bandResidualWitnessWeight, kFourDirection,
    atomMatrix]

/-- **THE MINIMUM-THRESHOLD TREE DOES NOT HOST AT THE BAND.** -/
theorem band_not_posDef_zeroTwoFour :
    ¬ (directionChartGap kFourDirection bandResidualWitnessPoint.mass
        bandResidualWitnessPoint.weight {0, 2, 4}).PosDef := by
  intro hpd
  have hdiag := hpd.diag_pos (i := (0 : Fin 3))
  rw [band_gap_zeroTwoFour_diag] at hdiag
  norm_num at hdiag

/-- Even at the band the minimiser has a POSITIVE gap determinant, so the failure
is invisible to every determinant reading. -/
theorem band_zeroTwoFour_detPos_notHost :
    0 < (directionChartGap kFourDirection bandResidualWitnessPoint.mass
        bandResidualWitnessPoint.weight {0, 2, 4}).det
      ∧ ¬ (directionChartGap kFourDirection bandResidualWitnessPoint.mass
        bandResidualWitnessPoint.weight {0, 2, 4}).PosDef := by
  refine ⟨?_, band_not_posDef_zeroTwoFour⟩
  rw [band_gap_zeroTwoFour_det]; norm_num

theorem band_gap_oneTwoFive_det :
    (directionChartGap kFourDirection bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight {1, 2, 5}).det = 2781 := by
  simp only [directionChartGap, bandResidualWitnessPoint_mass_eq,
    bandResidualWitnessPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [bandResidualWitnessMass, bandResidualWitnessWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem band_selected_oneTwoFive_det :
    (kFourSelectedMoment bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight {1, 2, 5}).det = 32000 := by
  simp only [kFourSelectedMoment, bandResidualWitnessPoint_mass_eq,
    bandResidualWitnessPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num [bandResidualWitnessMass, bandResidualWitnessWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem band_threshold_oneTwoFive :
    kFourChartThreshold bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight {1, 2, 5} = 29219 := by
  rw [kFourChartThreshold, band_selected_oneTwoFive_det, band_gap_oneTwoFive_det]
  norm_num

/-- The competitor: the star `{1, 2, 5}` dominates at the band, by Sylvester on the
three leading minors. -/
theorem band_posDef_oneTwoFive :
    (directionChartGap kFourDirection bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight {1, 2, 5}).PosDef := by
  rw [posDef_finThree_iff_leadingMinors _ (directionChartGap_transpose _ _ _ _)]
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [directionChartGap, bandResidualWitnessPoint_mass_eq,
        bandResidualWitnessPoint_weight_eq]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton, Fin.sum_univ_six]
      norm_num [bandResidualWitnessMass, bandResidualWitnessWeight, kFourDirection,
        atomMatrix, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-! ## 6. The refutation at `Gtz.heavyPairRefuterPoint`, and the mechanism

Here the minimum-threshold tree is `{1, 2, 5}` and its threshold is NEGATIVE, so
"beat the threshold" is vacuous there, while the tree still fails to dominate. -/

theorem heavyPair_gap_oneTwoFive_det :
    (directionChartGap kFourDirection heavyPairRefuterPoint.mass
      heavyPairRefuterPoint.weight {1, 2, 5}).det = 1070375699 / 216000 := by
  simp only [directionChartGap, heavyPairRefuterPoint_mass_eq,
    heavyPairRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [heavyPairRefuterMass, maxEdgeRefuterWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem heavyPair_selected_oneTwoFive_det :
    (kFourSelectedMoment heavyPairRefuterPoint.mass
      heavyPairRefuterPoint.weight {1, 2, 5}).det = 1 := by
  simp only [kFourSelectedMoment, heavyPairRefuterPoint_mass_eq,
    heavyPairRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num [heavyPairRefuterMass, maxEdgeRefuterWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem heavyPair_threshold_oneTwoFive :
    kFourChartThreshold heavyPairRefuterPoint.mass
      heavyPairRefuterPoint.weight {1, 2, 5} = -1070159699 / 216000 := by
  rw [kFourChartThreshold, heavyPair_selected_oneTwoFive_det,
    heavyPair_gap_oneTwoFive_det]
  norm_num

/-- **THE THRESHOLD GOES NEGATIVE AT A NON-HOST.** -/
theorem heavyPair_threshold_oneTwoFive_neg :
    kFourChartThreshold heavyPairRefuterPoint.mass
      heavyPairRefuterPoint.weight {1, 2, 5} < 0 := by
  rw [heavyPair_threshold_oneTwoFive]; norm_num

theorem heavyPair_gap_oneTwoFive_diag :
    (directionChartGap kFourDirection heavyPairRefuterPoint.mass
      heavyPairRefuterPoint.weight {1, 2, 5}) 0 0 = -3181 / 60 := by
  simp only [directionChartGap, heavyPairRefuterPoint_mass_eq,
    heavyPairRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [heavyPairRefuterMass, maxEdgeRefuterWeight, kFourDirection, atomMatrix]

theorem heavyPair_not_posDef_oneTwoFive :
    ¬ (directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight {1, 2, 5}).PosDef := by
  intro hpd
  have hdiag := hpd.diag_pos (i := (0 : Fin 3))
  rw [heavyPair_gap_oneTwoFive_diag] at hdiag
  norm_num at hdiag

/-- **THE MECHANISM.**  At the heavy-pair refuter the minimum-threshold tree has a
strictly POSITIVE gap determinant and still fails to dominate, so the threshold
rule selects a determinant-positive non-host — exactly the failure mode the
registry ledger already records for determinant readings. -/
theorem heavyPair_detPos_notHost :
    0 < (directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight {1, 2, 5}).det
      ∧ ¬ (directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight {1, 2, 5}).PosDef := by
  refine ⟨?_, heavyPair_not_posDef_oneTwoFive⟩
  rw [heavyPair_gap_oneTwoFive_det]; norm_num

/-! ## 7. The designation, refuted -/

/-- The designation this module tests: a spanning tree whose threshold is at most
another's inherits that other's domination.  Any rule of the form "prefer the
smaller threshold" implies it. -/
def KFourMinThresholdHostsStrictTree : Prop :=
  ∀ point : DirectionChartPoint 6, ∀ treeLow treeHigh : Finset (Fin 6),
    kFourChartThreshold point.mass point.weight treeLow
        ≤ kFourChartThreshold point.mass point.weight treeHigh →
      (directionChartGap kFourDirection point.mass point.weight treeHigh).PosDef →
        (directionChartGap kFourDirection point.mass point.weight treeLow).PosDef

/-- **THE MINIMUM-THRESHOLD DESIGNATION IS REFUTED.**  At the canonical band
inhabitant the star `{0, 2, 4}` has threshold `399`, strictly below the hosting
star `{1, 2, 5}` at `29219`, and it does not dominate. -/
theorem kFourMinThresholdHostsStrictTree_refuted :
    ¬ KFourMinThresholdHostsStrictTree := by
  intro hrule
  refine band_not_posDef_zeroTwoFour ?_
  refine hrule bandResidualWitnessPoint {0, 2, 4} {1, 2, 5} ?_ band_posDef_oneTwoFive
  rw [band_threshold_zeroTwoFour, band_threshold_oneTwoFive]
  norm_num

end Gtz
