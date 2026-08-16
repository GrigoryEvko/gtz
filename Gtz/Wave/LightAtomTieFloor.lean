/-
# The deflation gap floor, the leverage floor of a tie, and the two hinge producers

`Gtz.dominating_of_light_atom` (Gtz/Reduction/Deflation.lean:83) takes an atom of
leverage at most one, deflates onto one fewer atom, applies weighted GTZ one size
down, and pulls a WEAKLY dominating subset back.  Its conclusion is
`Gtz.Dominates`, and `Gtz.IsTie` already asserts a weakly dominating subset, so
that theorem cannot refute a tie.  This file supplies what it discards.

## The master floor

The landed proof passes through the congruence summand `(1 - t_d) * S_C - P`,
with `P = 1 - t_d * A_d`, and then dissolves it into a bare nonnegativity.  That
summand is exactly

  `(1 - t_d) * (S_C - 1) - t_d * (1 - A_d)`,

so keeping it gives `Gtz.exists_deflationGapFloor`: at EVERY label whose share is
below one, weighted GTZ one size down supplies a rank-sized subset AVOIDING that
label whose gap, scaled by `1 - t_d`, beats `t_d` times the rank-one defect
`1 - A_d`.  Division free, no leverage hypothesis, no square root.

The subtracted matrix is `1 - A_d`, whose spectrum is `1 - leverageOf` on the
atom's own axis and `1` on the orthogonal complement.  So the floor is a rank-one
DEFECT rather than a scalar: the gap beats a fixed positive multiple of the
identity on a hyperplane, and only the atom's own axis is unconstrained.

Three consequences, none of which the corpus carries.

## 1.  The strict engine

`1 - A_d` is positive definite exactly when `leverageOf (D.atom d) < 1`, so a
STRICTLY light atom yields a STRICTLY dominating subset,
`Gtz.exists_posDef_subsetSum_of_light_atom`.  The landed theorem gives the
non-strict form at `leverageOf <= 1` and is cited, not restated.

## 2.  The leverage floor of a tie

A strict dominator contradicts the second clause of `Gtz.IsTie`.  So under the
predecessor every label of a tie carries `1 <= leverageOf`,
`Gtz.one_le_leverage_of_isTie`.  **At `(6,3)` the predecessor is the landed
theorem `Gtz.gtzWeighted_of_le_five`, so the leverage floor of a tie is
UNCONDITIONAL there** — `Gtz.one_le_leverage_of_isTie_sixThree`.  Heaviness is
not a hypothesis on that cell.  It is a property of every tie.

## 3.  The cone law

A tie's dominating subset has a singular gap.  Read against the floor, a
direction on which the gap does not exceed zero obeys
`probe ⬝ᵥ probe <= (g_d ⬝ᵥ probe) ^ 2`, and Cauchy-Schwarz caps the same square
by `leverageOf g_d * (probe ⬝ᵥ probe)`.  So the tight directions of that subset
lie in the cone of half-angle `arccos (1 / sqrt (leverageOf g_d))` about the
atom, `Gtz.tight_cone_of_floor`, and the leverage floor is the same inequality
read without the direction.

## The consumers

Both off-path registry axioms conclude `IsTie design -> HasParallelPair design`
and both take the predecessor cell as a hypothesis.  Every producer landed before
this file ignored the predecessor and asked for excess dominance, whose
hypothesis is refuted at `(6,3)` by
`Gtz.not_forall_excessDominates_sixThree_unconditional` and at rank four on the
complete graph less an edge.  The producers here spend the predecessor instead,
and what they ask for is a decision on the ALL-HEAVY stratum alone, which the
leverage floor proves is the only stratum a tie can inhabit.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.Design.MarginTransfer
import Gtz.Reduction.Deflation
import Gtz.Reduction.Reductions
import Gtz.Reduction.SplitTransfer
import Gtz.Certificates.ResidueDissolution

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ### 1.  The rank-one defect `1 - A_g` -/

/-- The defect is positive semidefinite exactly when the atom is not heavy: the
landed rank-one Schur reading at `N = 1`, isolated for reuse. -/
theorem posSemidef_one_sub_atomMatrix {atomVector : Fin k → ℝ}
    (hlight : leverageOf atomVector ≤ 1) :
    ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix atomVector).PosSemidef :=
  (posSemidef_sub_vecMulVec_iff 1 Matrix.PosDef.one atomVector).mpr
    (by rw [inv_one, Matrix.one_mulVec, dotProduct_self_eq_sum_sq]; exact hlight)

/-- **The defect is positive DEFINITE below unit leverage.**  This is the single
strengthening the file turns on, and it is where the strictness of the final
domination comes from. -/
theorem posDef_one_sub_atomMatrix {atomVector : Fin k → ℝ}
    (hlight : leverageOf atomVector < 1) :
    ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix atomVector).PosDef := by
  have hshare : (1 : ℝ) * leverageOf atomVector < 1 := by rw [one_mul]; exact hlight
  have hpd := posDef_one_sub_smul_atomMatrix_of_share_lt_one (k := k)
    (weight := 1) (atomVector := atomVector) one_pos hshare
  rwa [one_smul] at hpd

/-- A positive multiple of a positive definite matrix is positive definite. -/
theorem posDef_smul_of_pos {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.PosDef)
    {scale : ℝ} (hscale : 0 < scale) : (scale • A).PosDef := by
  obtain ⟨hherm, hform⟩ := Matrix.posDef_iff_dotProduct_mulVec.mp hA
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hprobe => ?_⟩
  · exact isHermitian_of_transpose_eq
      (by rw [Matrix.transpose_smul, transpose_eq_of_isHermitian hherm])
  · have hpos := hform hprobe
    rw [star_trivial] at hpos ⊢
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_pos hscale hpos

/-- The quadratic form of a rank-one atom is the squared correlation.  Stated
here in the shape the floor's expansion needs. -/
theorem atomMatrix_quadratic (atomVector probe : Fin k → ℝ) :
    probe ⬝ᵥ (atomMatrix atomVector *ᵥ probe) = (atomVector ⬝ᵥ probe) ^ 2 := by
  rw [atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
    dotProduct_comm probe atomVector]
  ring

/-! ### 2.  The master floor -/

/-- **THE DEFLATION GAP FLOOR.**  Weighted GTZ one size down supplies, at EVERY
label whose share is below one, a rank-sized subset AVOIDING that label with

  `(1 - t_d) * (S_C - 1)  -  t_d * (1 - A_d)`  positive semidefinite.

No leverage hypothesis enters, and the statement carries no division.  The share
condition is exactly what deflation needs, and it is automatic at
`leverageOf <= 1` because a design of at least two labels has every weight below
one.

The corpus keeps only the corollary at `leverageOf <= 1`, where the defect is
merely nonnegative and the floor collapses into `Gtz.Dominates`. -/
theorem exists_deflationGapFloor (D : WeightedDesign (m + 1) k)
    (hm : 1 ≤ m) (hrec : GtzWeighted m k) (d : Fin (m + 1))
    (hshare : D.weight d * leverageOf (D.atom d) < 1) :
    ∃ C : Finset (Fin (m + 1)), C.card = k ∧ d ∉ C ∧
      (((1 : ℝ) - D.weight d) • (subsetSum D C - 1)
        - D.weight d
            • ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom d))).PosSemidef := by
  have htd : D.weight d < 1 := weight_lt_one D (by omega) d
  have htdpos := D.weight_pos d
  have hs : (0 : ℝ) < 1 - D.weight d := by linarith
  have hPsymm : ((1 : Matrix (Fin k) (Fin k) ℝ)
        - D.weight d • atomMatrix (D.atom d))ᵀ
      = 1 - D.weight d • atomMatrix (D.atom d) := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom d)).1]
  have hPpd : ((1 : Matrix (Fin k) (Fin k) ℝ)
      - D.weight d • atomMatrix (D.atom d)).PosDef :=
    posDef_one_sub_smul_atomMatrix_of_share_lt_one htdpos hshare
  obtain ⟨R, hRdet, hRPR⟩ := exists_congruence_to_one hPpd
  obtain ⟨Cdef, hCdefcard, hCdefdom⟩ := hrec (deflatedDesign D d R hs hRPR)
  have hembinj : Function.Injective d.succAbove := Fin.succAbove_right_injective
  refine ⟨Cdef.image d.succAbove, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hembinj, hCdefcard]
  · simp only [Finset.mem_image, not_exists, not_and]
    exact fun i _ hi => (Fin.succAbove_ne d i) hi
  · have hdom : ((∑ i ∈ Cdef, atomMatrix (Real.sqrt (1 - D.weight d)
        • (Rᵀ *ᵥ D.atom (d.succAbove i)))) - 1).PosSemidef := hCdefdom
    have hSdef : ∑ i ∈ Cdef, atomMatrix (Real.sqrt (1 - D.weight d)
          • (Rᵀ *ᵥ D.atom (d.succAbove i)))
        = Rᵀ * (((1 : ℝ) - D.weight d)
            • subsetSum D (Cdef.image d.succAbove)) * R := by
      rw [subsetSum, Finset.sum_image fun a _ b _ hab => hembinj hab,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul,
        Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [atomMatrix_smul, Real.sq_sqrt hs.le, transpose_mul_atomMatrix_mul]
    have hXsym : ((((1 : ℝ) - D.weight d)
          • subsetSum D (Cdef.image d.succAbove))
          - (1 - D.weight d • atomMatrix (D.atom d)))ᵀ
        = (((1 : ℝ) - D.weight d) • subsetSum D (Cdef.image d.succAbove))
          - (1 - D.weight d • atomMatrix (D.atom d)) := by
      rw [Matrix.transpose_sub, Matrix.transpose_smul, subsetSum_transpose,
        hPsymm]
    have hkey : ((((1 : ℝ) - D.weight d)
        • subsetSum D (Cdef.image d.succAbove))
        - (1 - D.weight d • atomMatrix (D.atom d))).PosSemidef := by
      refine (posSemidef_congr_right hXsym hRdet).mpr ?_
      have hexpand : Rᵀ * ((((1 : ℝ) - D.weight d)
            • subsetSum D (Cdef.image d.succAbove))
            - (1 - D.weight d • atomMatrix (D.atom d))) * R
          = (∑ i ∈ Cdef, atomMatrix (Real.sqrt (1 - D.weight d)
              • (Rᵀ *ᵥ D.atom (d.succAbove i)))) - 1 := by
        rw [Matrix.mul_sub, Matrix.sub_mul, hRPR, ← hSdef]
      rw [hexpand]
      exact hdom
    have hrewrite : ((1 : ℝ) - D.weight d)
          • (subsetSum D (Cdef.image d.succAbove) - 1)
          - D.weight d
              • ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom d))
        = (((1 : ℝ) - D.weight d) • subsetSum D (Cdef.image d.succAbove))
          - (1 - D.weight d • atomMatrix (D.atom d)) := by
      module
    rw [hrewrite]
    exact hkey

/-! ### 3.  The strict engine and the leverage floor of a tie -/

/-- **A STRICTLY LIGHT ATOM YIELDS A STRICTLY DOMINATING SUBSET.**  The landed
`Gtz.dominating_of_light_atom` gives the non-strict form at `leverageOf <= 1`.
This is the strict form, and it is the version a tie cannot survive. -/
theorem exists_posDef_subsetSum_of_light_atom (D : WeightedDesign (m + 1) k)
    (hm : 1 ≤ m) (hrec : GtzWeighted m k) (d : Fin (m + 1))
    (hlight : leverageOf (D.atom d) < 1) :
    ∃ C : Finset (Fin (m + 1)), C.card = k ∧ (subsetSum D C - 1).PosDef := by
  have htd : D.weight d < 1 := weight_lt_one D (by omega) d
  have htdpos := D.weight_pos d
  have hs : (0 : ℝ) < 1 - D.weight d := by linarith
  have hlevNonneg : 0 ≤ leverageOf (D.atom d) := by
    rw [leverageOf]; positivity
  have hshare : D.weight d * leverageOf (D.atom d) < 1 := by nlinarith
  obtain ⟨C, hcard, -, hfloor⟩ := exists_deflationGapFloor D hm hrec d hshare
  refine ⟨C, hcard, ?_⟩
  have hdefect : (D.weight d
      • ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom d))).PosDef :=
    posDef_smul_of_pos (posDef_one_sub_atomMatrix hlight) htdpos
  have hscaled : (((1 : ℝ) - D.weight d) • (subsetSum D C - 1)).PosDef := by
    have hsplit : ((1 : ℝ) - D.weight d) • (subsetSum D C - 1)
        = (((1 : ℝ) - D.weight d) • (subsetSum D C - 1)
            - D.weight d
                • ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom d)))
          + D.weight d
              • ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom d)) := by
      module
    rw [hsplit]
    exact Matrix.PosDef.posSemidef_add hfloor hdefect
  have hunscale : subsetSum D C - 1
      = ((1 : ℝ) - D.weight d)⁻¹ • (((1 : ℝ) - D.weight d) • (subsetSum D C - 1)) :=
    (inv_smul_smul₀ hs.ne' _).symm
  rw [hunscale]
  exact posDef_smul_of_pos hscaled (inv_pos.mpr hs)

/-- **EVERY LABEL OF A TIE IS HEAVY.**  Under weighted GTZ one size down a tie
admits no label of leverage below one, because such a label hands back a strictly
dominating subset and the second clause of `Gtz.IsTie` forbids one.

The predecessor is exactly the hypothesis both off-path registry axioms already
carry, so this costs nothing on either of their cells. -/
theorem one_le_leverage_of_isTie {size rank : ℕ} (hsize : 2 ≤ size)
    (hrec : GtzWeighted (size - 1) rank)
    (D : WeightedDesign size rank) (htie : IsTie D) (label : Fin size) :
    1 ≤ leverageOf (D.atom label) := by
  obtain ⟨n, rfl⟩ : ∃ n, size = n + 1 := ⟨size - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hrec
  by_contra hlt
  push Not at hlt
  obtain ⟨C, hcard, hpd⟩ :=
    exists_posDef_subsetSum_of_light_atom D (by omega) hrec label hlt
  exact htie.2 C hcard hpd

/-- The contrapositive, in the form a producer consumes. -/
theorem not_isTie_of_light_atom {size rank : ℕ} (hsize : 2 ≤ size)
    (hrec : GtzWeighted (size - 1) rank)
    (D : WeightedDesign size rank) (label : Fin size)
    (hlight : leverageOf (D.atom label) < 1) : ¬ IsTie D := fun htie =>
  absurd (one_le_leverage_of_isTie hsize hrec D htie label) (not_le.mpr hlight)

/-- The whole-design form, which is the bridge to the corpus's all-heavy
stratum. -/
theorem forall_one_le_leverage_of_isTie {size rank : ℕ} (hsize : 2 ≤ size)
    (hrec : GtzWeighted (size - 1) rank)
    (D : WeightedDesign size rank) (htie : IsTie D) :
    ∀ label : Fin size, 1 ≤ leverageOf (D.atom label) :=
  fun label => one_le_leverage_of_isTie hsize hrec D htie label

/-! ### 4.  The rank-three instance, with no hypothesis -/

/-- **THE LEVERAGE FLOOR OF A TIE AT `(6,3)`, UNCONDITIONALLY.**  The predecessor
cell of the rank-three threshold cell is `(5,3)`, and weighted GTZ there is the
landed theorem `Gtz.gtzWeighted_of_le_five`.  So at the cell the whole rank-three
campaign is about, heaviness is not an assumption on a design.  It is a property
of every tie. -/
theorem one_le_leverage_of_isTie_sixThree (D : WeightedDesign 6 3)
    (htie : IsTie D) (label : Fin 6) : 1 ≤ leverageOf (D.atom label) :=
  one_le_leverage_of_isTie (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) D htie label

/-- Every cell at or below the rank-three threshold, since
`Gtz.gtzWeighted_of_le_five` covers every predecessor there. -/
theorem one_le_leverage_of_isTie_of_size_le_six {size rank : ℕ}
    (hsize : 2 ≤ size) (hsmall : size ≤ 6) (hrank : 1 ≤ rank)
    (D : WeightedDesign size rank) (htie : IsTie D) (label : Fin size) :
    1 ≤ leverageOf (D.atom label) :=
  one_le_leverage_of_isTie hsize
    (gtzWeighted_of_le_five (size - 1) rank hrank (by omega)) D htie label

/-- A light label at `(6,3)` produces a STRICT dominator with no hypothesis at
all.  This is the currency the five on-path obligations consume. -/
theorem exists_posDef_subsetSum_sixThree_of_light (D : WeightedDesign 6 3)
    (label : Fin 6) (hlight : leverageOf (D.atom label) < 1) :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ (subsetSum D C - 1).PosDef :=
  exists_posDef_subsetSum_of_light_atom (m := 5) D (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) label hlight

/-- The deflation floor at `(6,3)`, hypothesis-free beyond the share bound. -/
theorem exists_deflationGapFloor_sixThree (D : WeightedDesign 6 3)
    (label : Fin 6) (hshare : D.weight label * leverageOf (D.atom label) < 1) :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ label ∉ C ∧
      (((1 : ℝ) - D.weight label) • (subsetSum D C - 1)
        - D.weight label
            • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
                - atomMatrix (D.atom label))).PosSemidef :=
  exists_deflationGapFloor (m := 5) D (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) label hshare

/-! ### 5.  The cone law -/

/-- **THE TIGHT DIRECTIONS SIT IN A CONE ABOUT THE ATOM.**  A direction on which
the deflation subset's gap does not exceed zero has squared correlation with the
atom at least its own squared length.  With Cauchy-Schwarz on the other side this
pins the angle, and the leverage floor is the same statement read without the
direction. -/
theorem tight_cone_of_floor {D : WeightedDesign (m + 1) k} {d : Fin (m + 1)}
    {C : Finset (Fin (m + 1))} {probe : Fin k → ℝ}
    (hfloor : (((1 : ℝ) - D.weight d) • (subsetSum D C - 1)
      - D.weight d
          • ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom d))).PosSemidef)
    (htdpos : 0 < D.weight d) (hs : 0 < (1 : ℝ) - D.weight d)
    (htight : probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe) ≤ 0) :
    probe ⬝ᵥ probe ≤ (D.atom d ⬝ᵥ probe) ^ 2 := by
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hfloor).2 probe
  rw [star_trivial] at hform
  have hinner : probe ⬝ᵥ (((1 : Matrix (Fin k) (Fin k) ℝ)
        - atomMatrix (D.atom d)) *ᵥ probe)
      = probe ⬝ᵥ probe - (D.atom d ⬝ᵥ probe) ^ 2 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, atomMatrix_quadratic]
  have hexpand : probe ⬝ᵥ (((((1 : ℝ) - D.weight d) • (subsetSum D C - 1)
        - D.weight d
            • ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom d)))) *ᵥ probe)
      = ((1 : ℝ) - D.weight d) * (probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe))
        - D.weight d * (probe ⬝ᵥ probe - (D.atom d ⬝ᵥ probe) ^ 2) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hinner]
  rw [hexpand] at hform
  have hstill : ((1 : ℝ) - D.weight d)
      * (probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs.le htight
  nlinarith [hform, hstill, htdpos]

/-- Cauchy-Schwarz on the other side of the cone, so the two bounds compose into
the leverage floor read at a direction. -/
theorem leverage_ge_one_of_tight_cone {atomVector probe : Fin k → ℝ}
    (hprobe : probe ≠ 0)
    (hcone : probe ⬝ᵥ probe ≤ (atomVector ⬝ᵥ probe) ^ 2) :
    1 ≤ leverageOf atomVector := by
  have hcap := atom_form_le_leverage atomVector probe
  rw [atomMatrix_quadratic] at hcap
  have hpos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobe
  nlinarith [hcap, hpos, hcone]

/-! ### 6.  The two off-path hinge producers

Both axioms conclude `IsTie design -> HasParallelPair design`, and both hand over
the predecessor cell.  The leverage floor turns their antecedent into an
all-heavy antecedent for free, so a producer only has to decide the ALL-HEAVY
stratum.  That is strictly weaker than what every landed producer asked for, and
it does not refute the antecedent. -/

/-- **A PRODUCER FOR THE THRESHOLD-CELL HINGE, SPENDING THE PREDECESSOR.**  Its
hypothesis asks only that a tie whose every label is heavy carries a parallel
pair.  The registry's own predecessor hypothesis discharges the heaviness, so
nothing is assumed about designs carrying a light label. -/
theorem obligationThresholdCellHingeRankFourAndUp_of_heavyTie
    (hheavy : ∀ rank : ℕ, 4 ≤ rank →
      ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
        (∀ label, 1 ≤ leverageOf (design.atom label)) →
          IsTie design → HasParallelPair design) :
    ∀ rank : ℕ, 4 ≤ rank →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  intro rank hrank hrec design htie
  have hsize : 2 ≤ rank * (rank + 1) / 2 := by
    have hmono : 4 * 5 / 2 ≤ rank * (rank + 1) / 2 :=
      Nat.div_le_div_right (Nat.mul_le_mul hrank (by omega))
    omega
  exact hheavy rank hrank design
    (forall_one_le_leverage_of_isTie hsize hrec design htie) htie

/-- **A PRODUCER FOR THE SUB-THRESHOLD BAND HINGE, SPENDING THE PREDECESSOR.**
Same shape on the band's cells.  The band's own lower bound `2 * rank <= size`
supplies the two labels the leverage floor needs. -/
theorem obligationSubThresholdBandHinge_of_heavyTie
    (hheavy : ∀ rank : ℕ, 3 ≤ rank → ∀ size : ℕ, 2 * rank ≤ size →
      size < rank * (rank + 1) / 2 → ∀ design : WeightedDesign size rank,
        (∀ label, 1 ≤ leverageOf (design.atom label)) →
          IsTie design → HasParallelPair design) :
    ∀ rank : ℕ, 3 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank,
            IsTie design → HasParallelPair design := by
  intro rank hrank size hlow hhigh hrec design htie
  have hsize : 2 ≤ size := by omega
  exact hheavy rank hrank size hlow hhigh design
    (forall_one_le_leverage_of_isTie hsize hrec design htie) htie

/-- **AT `(6,3)` A DECISION ON THE ALL-HEAVY STRATUM CLOSES THE HINGE
OUTRIGHT.**  No predecessor hypothesis appears, because
`Gtz.gtzWeighted_of_le_five` supplies it. -/
theorem hingeConclusion_sixThree_of_heavyTie
    (hheavy : ∀ design : WeightedDesign 6 3,
      (∀ label, 1 ≤ leverageOf (design.atom label)) →
        IsTie design → HasParallelPair design) :
    ∀ design : WeightedDesign 6 3, IsTie design → HasParallelPair design :=
  fun design htie =>
    hheavy design
      (fun label => one_le_leverage_of_isTie_sixThree design htie label) htie

end Gtz
