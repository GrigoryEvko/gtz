import Gtz.Design.PlaneBranchWindowBridge
import Gtz.Design.LineBranchFreePairAggregateBalance
import Gtz.Design.TightLineBranchLivePairBridge
import Gtz.Design.LineBranchUnitAxisNormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12000000

namespace Gtz

open Matrix

def lineBranchAxisZero : Fin 3 -> ℝ := ![1, 0, 0]
def lineBranchAxisOne : Fin 3 -> ℝ := ![0, 1, 0]
def lineBranchAxisTwo : Fin 3 -> ℝ := ![0, 0, 1]

def unitAxisFrameHiddenForm
    (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate)
    - freeWeight 0 • atomMatrix (freeAtom 0)
    - freeWeight 1 • atomMatrix (freeAtom 1)
    - freeWeight 2 • atomMatrix (freeAtom 2)

def unitAxisFrameFreePairGap
    (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (first second : Fin 3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  unitAxisFrameHiddenForm baseWeight freeWeight freeAtom
    + atomMatrix (freeAtom first) + atomMatrix (freeAtom second) - 1

/-- Exact Cauchy--Binet ledger for the weighted three-free-pair determinant
aggregate in unit-axis coordinates.  The nine coordinate-bracket squares are
the only terms with a negative coefficient. -/
theorem weighted_freePairGap_det_sum_eq_bracketLedger
    (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) :
    -((freeWeight 0 + freeWeight 1)
          * (unitAxisFrameFreePairGap baseWeight freeWeight freeAtom 0 1).det
      + (freeWeight 0 + freeWeight 2)
          * (unitAxisFrameFreePairGap baseWeight freeWeight freeAtom 0 2).det
      + (freeWeight 1 + freeWeight 2)
          * (unitAxisFrameFreePairGap baseWeight freeWeight freeAtom 1 2).det)
      =
        2 * (freeWeight 0 + freeWeight 1 + freeWeight 2)
            * baseWeight 0 * baseWeight 1 * baseWeight 2
        - (freeWeight 0 + freeWeight 1 + freeWeight 2
              - freeWeight 0
                  * (2 * (freeWeight 0 + freeWeight 1 + freeWeight 2) - 1))
            * (baseWeight 0 * baseWeight 1
                  * tripleBracket lineBranchAxisZero lineBranchAxisOne (freeAtom 0) ^ 2
              + baseWeight 0 * baseWeight 2
                  * tripleBracket lineBranchAxisZero lineBranchAxisTwo (freeAtom 0) ^ 2
              + baseWeight 1 * baseWeight 2
                  * tripleBracket lineBranchAxisOne lineBranchAxisTwo (freeAtom 0) ^ 2)
        - (freeWeight 0 + freeWeight 1 + freeWeight 2
              - freeWeight 1
                  * (2 * (freeWeight 0 + freeWeight 1 + freeWeight 2) - 1))
            * (baseWeight 0 * baseWeight 1
                  * tripleBracket lineBranchAxisZero lineBranchAxisOne (freeAtom 1) ^ 2
              + baseWeight 0 * baseWeight 2
                  * tripleBracket lineBranchAxisZero lineBranchAxisTwo (freeAtom 1) ^ 2
              + baseWeight 1 * baseWeight 2
                  * tripleBracket lineBranchAxisOne lineBranchAxisTwo (freeAtom 1) ^ 2)
        - (freeWeight 0 + freeWeight 1 + freeWeight 2
              - freeWeight 2
                  * (2 * (freeWeight 0 + freeWeight 1 + freeWeight 2) - 1))
            * (baseWeight 0 * baseWeight 1
                  * tripleBracket lineBranchAxisZero lineBranchAxisOne (freeAtom 2) ^ 2
              + baseWeight 0 * baseWeight 2
                  * tripleBracket lineBranchAxisZero lineBranchAxisTwo (freeAtom 2) ^ 2
              + baseWeight 1 * baseWeight 2
                  * tripleBracket lineBranchAxisOne lineBranchAxisTwo (freeAtom 2) ^ 2)
        + baseWeight 0
            * (1 - (freeWeight 0 + freeWeight 1 + freeWeight 2))
            * ((freeWeight 0 + freeWeight 1
                  - 2 * freeWeight 0 * freeWeight 1)
                * tripleBracket lineBranchAxisZero (freeAtom 0) (freeAtom 1) ^ 2
              + (freeWeight 0 + freeWeight 2
                  - 2 * freeWeight 0 * freeWeight 2)
                * tripleBracket lineBranchAxisZero (freeAtom 0) (freeAtom 2) ^ 2
              + (freeWeight 1 + freeWeight 2
                  - 2 * freeWeight 1 * freeWeight 2)
                * tripleBracket lineBranchAxisZero (freeAtom 1) (freeAtom 2) ^ 2)
        + baseWeight 1
            * (1 - (freeWeight 0 + freeWeight 1 + freeWeight 2))
            * ((freeWeight 0 + freeWeight 1
                  - 2 * freeWeight 0 * freeWeight 1)
                * tripleBracket lineBranchAxisOne (freeAtom 0) (freeAtom 1) ^ 2
              + (freeWeight 0 + freeWeight 2
                  - 2 * freeWeight 0 * freeWeight 2)
                * tripleBracket lineBranchAxisOne (freeAtom 0) (freeAtom 2) ^ 2
              + (freeWeight 1 + freeWeight 2
                  - 2 * freeWeight 1 * freeWeight 2)
                * tripleBracket lineBranchAxisOne (freeAtom 1) (freeAtom 2) ^ 2)
        + baseWeight 2
            * (1 - (freeWeight 0 + freeWeight 1 + freeWeight 2))
            * ((freeWeight 0 + freeWeight 1
                  - 2 * freeWeight 0 * freeWeight 1)
                * tripleBracket lineBranchAxisTwo (freeAtom 0) (freeAtom 1) ^ 2
              + (freeWeight 0 + freeWeight 2
                  - 2 * freeWeight 0 * freeWeight 2)
                * tripleBracket lineBranchAxisTwo (freeAtom 0) (freeAtom 2) ^ 2
              + (freeWeight 1 + freeWeight 2
                  - 2 * freeWeight 1 * freeWeight 2)
                * tripleBracket lineBranchAxisTwo (freeAtom 1) (freeAtom 2) ^ 2)
        + ((2 - (freeWeight 0 + freeWeight 1 + freeWeight 2))
              * (freeWeight 0 * freeWeight 1
                + freeWeight 0 * freeWeight 2
                + freeWeight 1 * freeWeight 2)
            - (3 - 2 * (freeWeight 0 + freeWeight 1 + freeWeight 2))
                * freeWeight 0 * freeWeight 1 * freeWeight 2)
            * tripleBracket (freeAtom 0) (freeAtom 1) (freeAtom 2) ^ 2 := by
  simp [unitAxisFrameFreePairGap, unitAxisFrameHiddenForm,
    Matrix.det_fin_three, Matrix.diagonal, atomMatrix, Matrix.vecMulVec_apply,
    tripleBracket_eq, lineBranchAxisZero, lineBranchAxisOne, lineBranchAxisTwo]
  ring

/-- The abstract hidden form reconstructed from the design's transported
Parseval identity is the actual unit-axis hidden form. -/
theorem unitAxisFrameHiddenForm_eq_unitAxisHiddenForm
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    unitAxisFrameHiddenForm (unitAxisBaseWeight design)
        (unitAxisFreeWeight design) (unitAxisFreeAtom design)
      = unitAxisHiddenForm design := by
  have hframe := unitAxisFiveVectorIdentity design hlineFree
  unfold unitAxisFrameHiddenForm unitAxisBaseWeight unitAxisFreeWeight
  rw [← hframe]
  simp [freeThreeLabel]
  abel

/-- A free-pair gap in the abstract ledger is exactly the original pair gap
transported by the unit-axis congruence. -/
theorem unitAxisFrameFreePairGap_eq_congrPairGap
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (first second : Fin 3) (hdistinct : first ≠ second) :
    unitAxisFrameFreePairGap (unitAxisBaseWeight design)
        (unitAxisFreeWeight design) (unitAxisFreeAtom design) first second
      = (unitAxisBaseNormalizer design)ᵀ
          * (subsetSum design
              {freeThreeLabel first, freeThreeLabel second} - 1)
          * unitAxisBaseNormalizer design := by
  let normalizer := unitAxisBaseNormalizer design
  have hlabelDistinct : freeThreeLabel first ≠ freeThreeLabel second :=
    fun heq => hdistinct (freeThreeLabel_injective heq)
  rw [unitAxisFrameFreePairGap,
    unitAxisFrameHiddenForm_eq_unitAxisHiddenForm design hlineFree]
  calc
    unitAxisHiddenForm design
          + atomMatrix (unitAxisFreeAtom design first)
          + atomMatrix (unitAxisFreeAtom design second) - 1
        = atomMatrix (normalizerᵀ *ᵥ design.atom (freeThreeLabel first))
            + atomMatrix (normalizerᵀ *ᵥ design.atom (freeThreeLabel second))
            - normalizerᵀ * normalizer := by
              rw [unitAxisBaseNormalizer_metric_eq_one_sub_hiddenForm]
              simp only [normalizer, unitAxisFreeAtom]
              abel
    _ = normalizerᵀ
          * (subsetSum design
              {freeThreeLabel first, freeThreeLabel second} - 1)
          * normalizer := by
      rw [subsetSum, Finset.sum_pair hlabelDistinct,
        atomMatrix_conj, atomMatrix_conj, Matrix.transpose_transpose]
      noncomm_ring

/-- The determinant of the transported pair gap is the metric determinant
times minus the original pair minor. -/
theorem unitAxisFrameFreePairGap_det_eq_neg_metricDet_mul_pairGapExcessOf
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (first second : Fin 3) (hdistinct : first ≠ second) :
    (unitAxisFrameFreePairGap (unitAxisBaseWeight design)
        (unitAxisFreeWeight design) (unitAxisFreeAtom design) first second).det
      = -(1 - unitAxisHiddenForm design).det
          * pairGapExcessOf design
              (freeThreeLabel first) (freeThreeLabel second) := by
  have hgap := congrArg Matrix.det
    (unitAxisFrameFreePairGap_eq_congrPairGap design hlineFree
      first second hdistinct)
  have hmetric := congrArg Matrix.det
    (unitAxisBaseNormalizer_metric_eq_one_sub_hiddenForm design)
  have hlabelDistinct : freeThreeLabel first ≠ freeThreeLabel second :=
    fun heq => hdistinct (freeThreeLabel_injective heq)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    det_pairGap_eq_neg_pairGapExcessOf design hlabelDistinct] at hgap
  rw [Matrix.det_mul, Matrix.det_transpose] at hmetric
  calc
    _ = (unitAxisBaseNormalizer design).det
          * -pairGapExcessOf design (freeThreeLabel first) (freeThreeLabel second)
          * (unitAxisBaseNormalizer design).det := hgap
    _ = -((unitAxisBaseNormalizer design).det
          * (unitAxisBaseNormalizer design).det)
          * pairGapExcessOf design (freeThreeLabel first) (freeThreeLabel second) := by
            ring
    _ = _ := by rw [hmetric]

/-- The free-pair row aggregate is exactly the abstract determinant ledger,
up to the positive determinant of the transported identity metric. -/
theorem unitAxisMetricDet_mul_freePairRowAggregate_eq_neg_detSum
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    (1 - unitAxisHiddenForm design).det * freePairRowAggregate design
      = -((unitAxisFreeWeight design 0 + unitAxisFreeWeight design 1)
            * (unitAxisFrameFreePairGap (unitAxisBaseWeight design)
                (unitAxisFreeWeight design) (unitAxisFreeAtom design) 0 1).det
        + (unitAxisFreeWeight design 0 + unitAxisFreeWeight design 2)
            * (unitAxisFrameFreePairGap (unitAxisBaseWeight design)
                (unitAxisFreeWeight design) (unitAxisFreeAtom design) 0 2).det
        + (unitAxisFreeWeight design 1 + unitAxisFreeWeight design 2)
            * (unitAxisFrameFreePairGap (unitAxisBaseWeight design)
                (unitAxisFreeWeight design) (unitAxisFreeAtom design) 1 2).det) := by
  have hzero := unitAxisFrameFreePairGap_det_eq_neg_metricDet_mul_pairGapExcessOf
    design hlineFree 0 1 (by decide)
  have hone := unitAxisFrameFreePairGap_det_eq_neg_metricDet_mul_pairGapExcessOf
    design hlineFree 0 2 (by decide)
  have htwo := unitAxisFrameFreePairGap_det_eq_neg_metricDet_mul_pairGapExcessOf
    design hlineFree 1 2 (by decide)
  rw [freePairRowAggregate_eq_threePairs,
    hzero, hone, htwo]
  simp [unitAxisFreeWeight, freeThreeLabel]
  ring

end Gtz
