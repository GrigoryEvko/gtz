import Gtz.Wave.CycleIndependentClosure
import Gtz.Wave.KFourEdgeCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The cycle seam reduction — the independent cycle closes on one certificate

The labeled cycle carries two doubled pairs and two singles.  The landed
double-trace kill closes the branch where the two pairs are independent.
This module reduces the full closure to one polynomial certificate on
the seam branch: one pair independent, the other pair parallel.

## The reduction chain

1. **The share calculus.**  The Gram entry of a slot pair reads the
   share set: two products on a doubled share, one product on a single
   share, zero on an empty share.
2. **The corner trace.**  An independent doubled pair prices the corner
   trace of the coefficient matrix through the left eigen pair.
3. **The parallel pin.**  A parallel doubled pair forces equal weights
   at its two atoms.  The pin is division-free.
4. **The pattern transport.**  The slot quadruple relabels the
   coefficient index.  The submatrix along the quadruple keeps products,
   idempotency, and the trace.
5. **The seam certificate.**  `CycleSeamCertificate` states the seam
   kill in pattern coordinates: the carried reads, idempotency, the
   trace, the weight sum, the unit norms, the Gamma exchange symmetry,
   the Gamma diagonal reads, the parallel equation, and the
   independence hypothesis give `False` at a negative value.
6. **The discharge.**  The certificate closes
   `RankFourCycleIndependentClosed`: the disjunction resolves by the
   symmetric re-application, the double-independent branch dies on the
   trace budget, and the seam branch feeds the certificate.

## Key results

* `Gtz.basisGram_zero_of_share_empty`,
  `Gtz.basisGram_double_of_share_pair` — the share calculus.
* `Gtz.corner_trace_of_cross_det` — **THE CORNER TRACE.**
* `Gtz.pair_weight_eq_of_parallel` — **THE PARALLEL PIN.**
* `Gtz.submatrix_four_mul` — **THE PATTERN TRANSPORT.**
* `Gtz.CycleSeamCertificate` — **THE SEAM CERTIFICATE.**
* `Gtz.rankFourCycleIndependentClosed_of_seam_certificate` — **THE
  DISCHARGE.**  The certificate implies closure four.

## Vacuity

The crux statements are vacuous if `Gtz.GtzWeighted 6 3` holds.  The
share calculus and the certificate reduction are unconditional.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## Layer 1 — the share calculus of the Gram entries -/

/-- A nonzero coordinate product puts the atom in the share set. -/
theorem mem_shareSet_of_coordinate_product
    {basisLabel : Fin basisCount → activeIndex}
    {slotI slotJ : Fin basisCount} {atomIndex : Fin size}
    (hne : tightDir (basisLabel slotI) atomIndex
      * tightDir (basisLabel slotJ) atomIndex ≠ 0) :
    atomIndex ∈ shareSet tightDir basisLabel slotI slotJ := by
  rw [shareSet, Finset.mem_filter]
  exact ⟨Finset.mem_univ atomIndex,
    mem_datumTightSupport.mpr (left_ne_zero_of_mul hne),
    mem_datumTightSupport.mpr (right_ne_zero_of_mul hne)⟩

/-- **THE EMPTY SHARE.**  Two slots with an empty share set have a zero
Gram entry. -/
theorem basisGram_zero_of_share_empty
    (basisLabel : Fin basisCount → activeIndex)
    {slotI slotJ : Fin basisCount}
    (hshare : shareSet tightDir basisLabel slotI slotJ = ∅) :
    basisGram tightDir basisLabel slotI slotJ = 0 := by
  rw [basisGram_apply_sum]
  refine Finset.sum_eq_zero fun atomIndex _ => ?_
  by_contra hne
  have hmem := mem_shareSet_of_coordinate_product (basisLabel := basisLabel)
    (slotI := slotI) (slotJ := slotJ) hne
  rw [hshare] at hmem
  exact absurd hmem (Finset.notMem_empty atomIndex)

/-- **THE DOUBLED SHARE.**  Two slots with a two-atom share set read the
two coordinate products. -/
theorem basisGram_double_of_share_pair
    (basisLabel : Fin basisCount → activeIndex)
    {slotI slotJ : Fin basisCount} {atomA atomB : Fin size}
    (hne : atomA ≠ atomB)
    (hshare : shareSet tightDir basisLabel slotI slotJ = {atomA, atomB}) :
    basisGram tightDir basisLabel slotI slotJ
      = tightDir (basisLabel slotI) atomA * tightDir (basisLabel slotJ) atomA
        + tightDir (basisLabel slotI) atomB
          * tightDir (basisLabel slotJ) atomB := by
  rw [basisGram_apply_sum]
  rw [← Finset.sum_subset
    (Finset.subset_univ ({atomA, atomB} : Finset (Fin size)))
    (fun atomIndex _ hnot => by
      by_contra hcontra
      have hmem := mem_shareSet_of_coordinate_product (basisLabel := basisLabel)
        (slotI := slotI) (slotJ := slotJ) hcontra
      rw [hshare] at hmem
      exact hnot hmem)]
  rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]

/-- A support equality forces the coordinates off the support to zero. -/
theorem coordinate_zero_of_support_eq
    {label : activeIndex} {support : Finset (Fin size)}
    (hsupp : datumTightSupport tightDir label = support)
    {atomIndex : Fin size} (hnot : atomIndex ∉ support) :
    tightDir label atomIndex = 0 := by
  by_contra hne
  exact hnot (hsupp ▸ mem_datumTightSupport.mpr hne)

/-! ## Layer 2 — the corner trace of an independent pair -/

/-- **THE CORNER TRACE.**  A doubled pair with a nonzero cross
determinant prices the two corner diagonals: the left eigen pair
exhausts the corner spectrum. -/
theorem corner_trace_of_cross_det
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {slotA slotB : Fin basisCount} (hne : slotA ≠ slotB)
    (hmemA : basisLabel slotA ∈ activeSet)
    (hmemB : basisLabel slotB ∈ activeSet)
    {atomA atomB : Fin size}
    (hatomAA : atomA ∈ activeSubset (basisLabel slotA))
    (hatomAB : atomA ∈ activeSubset (basisLabel slotB))
    (hatomBA : atomB ∈ activeSubset (basisLabel slotA))
    (hatomBB : atomB ∈ activeSubset (basisLabel slotB))
    (hvanishA : ∀ columnIndex, columnIndex ≠ slotA → columnIndex ≠ slotB →
      tightDir (basisLabel columnIndex) atomA = 0)
    (hvanishB : ∀ columnIndex, columnIndex ≠ slotA → columnIndex ≠ slotB →
      tightDir (basisLabel columnIndex) atomB = 0)
    (hdet : tightDir (basisLabel slotA) atomA * tightDir (basisLabel slotB) atomB
        - tightDir (basisLabel slotA) atomB * tightDir (basisLabel slotB) atomA
      ≠ 0) :
    M slotA slotA + M slotB slotB
      = 2 * value + weight atomA + weight atomB := by
  have hAA := two_carrier_row_reading hdata basisLabel hrepresentation hne
    hmemA hatomAA hvanishA
  have hAB := two_carrier_row_reading hdata basisLabel hrepresentation hne
    hmemB hatomAB hvanishA
  have hBA := two_carrier_row_reading hdata basisLabel hrepresentation hne
    hmemA hatomBA hvanishB
  have hBB := two_carrier_row_reading hdata basisLabel hrepresentation hne
    hmemB hatomBB hvanishB
  have hv : (!![M slotA slotA, M slotB slotA;
        M slotA slotB, M slotB slotB] : Matrix (Fin 2) (Fin 2) ℝ)
      *ᵥ ![tightDir (basisLabel slotA) atomA, tightDir (basisLabel slotB) atomA]
      = (value + weight atomA)
        • ![tightDir (basisLabel slotA) atomA,
            tightDir (basisLabel slotB) atomA] := by
    funext rowIndex
    fin_cases rowIndex
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination hAA
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination hAB
  have hw : (!![M slotA slotA, M slotB slotA;
        M slotA slotB, M slotB slotB] : Matrix (Fin 2) (Fin 2) ℝ)
      *ᵥ ![tightDir (basisLabel slotA) atomB, tightDir (basisLabel slotB) atomB]
      = (value + weight atomB)
        • ![tightDir (basisLabel slotA) atomB,
            tightDir (basisLabel slotB) atomB] := by
    funext rowIndex
    fin_cases rowIndex
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination hBA
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination hBB
  have hdetPair : (![tightDir (basisLabel slotA) atomA,
        tightDir (basisLabel slotB) atomA] : Fin 2 → ℝ) 0
        * (![tightDir (basisLabel slotA) atomB,
            tightDir (basisLabel slotB) atomB] : Fin 2 → ℝ) 1
      - (![tightDir (basisLabel slotA) atomA,
          tightDir (basisLabel slotB) atomA] : Fin 2 → ℝ) 1
        * (![tightDir (basisLabel slotA) atomB,
            tightDir (basisLabel slotB) atomB] : Fin 2 → ℝ) 0 ≠ 0 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    intro hzero
    exact hdet (by linear_combination hzero)
  have htracePair := trace_eq_add_of_eigen_pair hv hw hdetPair
  rw [Matrix.trace_fin_two] at htracePair
  have hentry00 : (!![M slotA slotA, M slotB slotA;
      M slotA slotB, M slotB slotB] : Matrix (Fin 2) (Fin 2) ℝ) 0 0
      = M slotA slotA := rfl
  have hentry11 : (!![M slotA slotA, M slotB slotA;
      M slotA slotB, M slotB slotB] : Matrix (Fin 2) (Fin 2) ℝ) 1 1
      = M slotB slotB := rfl
  rw [hentry00, hentry11] at htracePair
  linarith

/-! ## Layer 3 — the parallel pin -/

/-- **THE PARALLEL PIN.**  A doubled pair with a zero cross determinant
and nonvanishing first-carrier coordinates has equal weights at its two
atoms.  The pin is division-free. -/
theorem pair_weight_eq_of_parallel
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {slotA slotB : Fin basisCount} (hne : slotA ≠ slotB)
    (hmemA : basisLabel slotA ∈ activeSet)
    {atomA atomB : Fin size}
    (hatomAA : atomA ∈ activeSubset (basisLabel slotA))
    (hatomBA : atomB ∈ activeSubset (basisLabel slotA))
    (hvanishA : ∀ columnIndex, columnIndex ≠ slotA → columnIndex ≠ slotB →
      tightDir (basisLabel columnIndex) atomA = 0)
    (hvanishB : ∀ columnIndex, columnIndex ≠ slotA → columnIndex ≠ slotB →
      tightDir (basisLabel columnIndex) atomB = 0)
    (hqA : tightDir (basisLabel slotA) atomA ≠ 0)
    (hqB : tightDir (basisLabel slotA) atomB ≠ 0)
    (hpar : tightDir (basisLabel slotA) atomA * tightDir (basisLabel slotB) atomB
        - tightDir (basisLabel slotA) atomB * tightDir (basisLabel slotB) atomA
      = 0) :
    weight atomA = weight atomB := by
  have hA := two_carrier_row_reading hdata basisLabel hrepresentation hne
    hmemA hatomAA hvanishA
  have hB := two_carrier_row_reading hdata basisLabel hrepresentation hne
    hmemA hatomBA hvanishB
  have hprod : (value + weight atomA)
        * (tightDir (basisLabel slotA) atomA
          * tightDir (basisLabel slotA) atomB)
      = (value + weight atomB)
        * (tightDir (basisLabel slotA) atomA
          * tightDir (basisLabel slotA) atomB) := by
    linear_combination (- tightDir (basisLabel slotA) atomB) * hA
      + tightDir (basisLabel slotA) atomA * hB - M slotB slotA * hpar
  have hcancel := mul_right_cancel₀ (mul_ne_zero hqA hqB) hprod
  linarith

/-! ## Layer 4 — the enumerations and the pattern transport -/

/-- Six distinct atoms enumerate the six-atom universe. -/
theorem six_atoms_eq_univ {a0 a1 a2 a3 a4 a5 : Fin 6}
    (h01 : a0 ≠ a1) (h02 : a0 ≠ a2) (h03 : a0 ≠ a3) (h04 : a0 ≠ a4)
    (h05 : a0 ≠ a5) (h12 : a1 ≠ a2) (h13 : a1 ≠ a3) (h14 : a1 ≠ a4)
    (h15 : a1 ≠ a5) (h23 : a2 ≠ a3) (h24 : a2 ≠ a4) (h25 : a2 ≠ a5)
    (h34 : a3 ≠ a4) (h35 : a3 ≠ a5) (h45 : a4 ≠ a5) :
    ({a0, a1, a2, a3, a4, a5} : Finset (Fin 6)) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_insert_of_notMem (by simp [h01, h02, h03, h04, h05]),
    Finset.card_insert_of_notMem (by simp [h12, h13, h14, h15]),
    Finset.card_insert_of_notMem (by simp [h23, h24, h25]),
    Finset.card_insert_of_notMem (by simp [h34, h35]),
    Finset.card_insert_of_notMem (by simp [h45]),
    Finset.card_singleton]
  rfl

/-- The sum over the six-atom universe at six distinct atoms. -/
theorem sum_six_atoms (f : Fin 6 → ℝ) {a0 a1 a2 a3 a4 a5 : Fin 6}
    (h01 : a0 ≠ a1) (h02 : a0 ≠ a2) (h03 : a0 ≠ a3) (h04 : a0 ≠ a4)
    (h05 : a0 ≠ a5) (h12 : a1 ≠ a2) (h13 : a1 ≠ a3) (h14 : a1 ≠ a4)
    (h15 : a1 ≠ a5) (h23 : a2 ≠ a3) (h24 : a2 ≠ a4) (h25 : a2 ≠ a5)
    (h34 : a3 ≠ a4) (h35 : a3 ≠ a5) (h45 : a4 ≠ a5) :
    ∑ atomIndex : Fin 6, f atomIndex
      = f a0 + f a1 + f a2 + f a3 + f a4 + f a5 := by
  rw [← six_atoms_eq_univ h01 h02 h03 h04 h05 h12 h13 h14 h15 h23 h24 h25
    h34 h35 h45]
  rw [Finset.sum_insert (by simp [h01, h02, h03, h04, h05]),
    Finset.sum_insert (by simp [h12, h13, h14, h15]),
    Finset.sum_insert (by simp [h23, h24, h25]),
    Finset.sum_insert (by simp [h34, h35]),
    Finset.sum_insert (by simp [h45]),
    Finset.sum_singleton]
  ring

/-- The sum over the four-slot universe at four distinct slots. -/
theorem sum_four_slots (f : Fin 4 → ℝ) {s0 s1 s2 s3 : Fin 4}
    (h01 : s0 ≠ s1) (h02 : s0 ≠ s2) (h03 : s0 ≠ s3)
    (h12 : s1 ≠ s2) (h13 : s1 ≠ s3) (h23 : s2 ≠ s3) :
    ∑ slotIndex : Fin 4, f slotIndex = f s0 + f s1 + f s2 + f s3 := by
  rw [← slot_quadruple_eq_univ h01 h02 h03 h12 h13 h23]
  rw [Finset.sum_insert (by simp [h01, h02, h03]),
    Finset.sum_insert (by simp [h12, h13]),
    Finset.sum_insert (by simp [h23]),
    Finset.sum_singleton]
  ring

/-- **THE PATTERN TRANSPORT.**  The submatrix along four distinct slots
multiplies like the ambient matrices. -/
theorem submatrix_four_mul (A B : Matrix (Fin 4) (Fin 4) ℝ)
    {s0 s1 s2 s3 : Fin 4}
    (h01 : s0 ≠ s1) (h02 : s0 ≠ s2) (h03 : s0 ≠ s3)
    (h12 : s1 ≠ s2) (h13 : s1 ≠ s3) (h23 : s2 ≠ s3) :
    A.submatrix ![s0, s1, s2, s3] ![s0, s1, s2, s3]
        * B.submatrix ![s0, s1, s2, s3] ![s0, s1, s2, s3]
      = (A * B).submatrix ![s0, s1, s2, s3] ![s0, s1, s2, s3] := by
  ext rowIndex colIndex
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [Fin.sum_univ_four,
    sum_four_slots (fun columnIndex =>
      A (![s0, s1, s2, s3] rowIndex) columnIndex
        * B columnIndex (![s0, s1, s2, s3] colIndex)) h01 h02 h03 h12 h13 h23]
  simp

/-! ## Layer 5 — the seam certificate -/

/-- **THE SEAM CERTIFICATE.**  The polynomial kill of the seam branch in
pattern coordinates.  The pattern puts the independent pair on slots
zero and one with atom weights `w0`, `w1`, the parallel pair on slots
two and three with the equal weight `wc`, and the two singles at the
weights `w4`, `w5`.  The hypotheses are the carried reads, idempotency,
the trace, the weight sum, the unit norms, the Gamma matrix, the Gamma
exchange symmetry, the Gamma diagonal reads, the parallel equation, and
the independence hypothesis.  The conclusion is `False` at a negative
value. -/
def CycleSeamCertificate : Prop :=
  ∀ (value w0 w1 wc w4 w5 : ℝ)
    (qK0 qK1 qK4 qL0 qL1 qL5 qM2 qM3 qM4 qN2 qN3 qN5 : ℝ)
    (M Γ : Matrix (Fin 4) (Fin 4) ℝ),
    value < 0 →
    0 < w0 → 0 < w1 → 0 < wc → 0 < w4 → 0 < w5 →
    w0 + w1 + 2 * wc + w4 + w5 = 1 →
    M * M = M →
    M 0 0 + M 1 1 + M 2 2 + M 3 3 = 2 →
    qK0 * M 0 0 + qL0 * M 1 0 = (value + w0) * qK0 →
    qK0 * M 0 1 + qL0 * M 1 1 = (value + w0) * qL0 →
    qK1 * M 0 0 + qL1 * M 1 0 = (value + w1) * qK1 →
    qK1 * M 0 1 + qL1 * M 1 1 = (value + w1) * qL1 →
    qM2 * M 2 2 + qN2 * M 3 2 = (value + wc) * qM2 →
    qM2 * M 2 3 + qN2 * M 3 3 = (value + wc) * qN2 →
    qM3 * M 2 2 + qN3 * M 3 2 = (value + wc) * qM3 →
    qM3 * M 2 3 + qN3 * M 3 3 = (value + wc) * qN3 →
    qK4 * M 0 0 + qM4 * M 2 0 = (value + w4) * qK4 →
    qK4 * M 0 2 + qM4 * M 2 2 = (value + w4) * qM4 →
    qL5 * M 1 1 + qN5 * M 3 1 = (value + w5) * qL5 →
    qL5 * M 1 3 + qN5 * M 3 3 = (value + w5) * qN5 →
    qK0 ^ 2 + qK1 ^ 2 + qK4 ^ 2 = 1 →
    qL0 ^ 2 + qL1 ^ 2 + qL5 ^ 2 = 1 →
    qM2 ^ 2 + qM3 ^ 2 + qM4 ^ 2 = 1 →
    qN2 ^ 2 + qN3 ^ 2 + qN5 ^ 2 = 1 →
    Γ = !![1, qK0 * qL0 + qK1 * qL1, qK4 * qM4, 0;
           qK0 * qL0 + qK1 * qL1, 1, 0, qL5 * qN5;
           qK4 * qM4, 0, 1, qM2 * qN2 + qM3 * qN3;
           0, qL5 * qN5, qM2 * qN2 + qM3 * qN3, 1] →
    (Γ * M)ᵀ = Γ * M →
    (Γ * M) 0 0 = value + w0 * qK0 ^ 2 + w1 * qK1 ^ 2 + w4 * qK4 ^ 2 →
    (Γ * M) 1 1 = value + w0 * qL0 ^ 2 + w1 * qL1 ^ 2 + w5 * qL5 ^ 2 →
    (Γ * M) 2 2 = value + wc * qM2 ^ 2 + wc * qM3 ^ 2 + w4 * qM4 ^ 2 →
    (Γ * M) 3 3 = value + wc * qN2 ^ 2 + wc * qN3 ^ 2 + w5 * qN5 ^ 2 →
    qM2 * qN3 - qM3 * qN2 = 0 →
    qK0 * qL1 - qK1 * qL0 ≠ 0 →
    qK0 ≠ 0 → qK1 ≠ 0 → qK4 ≠ 0 → qL0 ≠ 0 → qL1 ≠ 0 → qL5 ≠ 0 →
    qM2 ≠ 0 → qM3 ≠ 0 → qM4 ≠ 0 → qN2 ≠ 0 → qN3 ≠ 0 → qN5 ≠ 0 →
    False

/-! ## Layer 6 — the seam application -/

set_option maxHeartbeats 1600000 in
/-- **THE SEAM APPLICATION.**  At a cycle pattern with the first pair
independent, the certificate and the landed kills give `False`.  The
second pair is unconstrained: the independent case dies on the trace
budget, and the parallel case feeds the certificate. -/
theorem RankFourFrame.false_of_cycle_first_independent
    (hcert : CycleSeamCertificate)
    {crux : SixThreeCrux} (frame : RankFourFrame crux)
    (slotK slotL slotM slotN : Fin 4)
    (pairAtomOne pairAtomTwo coAtomOne coAtomTwo singleKM singleLN : Fin 6)
    (hmult : ∀ atomIndex, basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex = 2)
    (hKL : slotK ≠ slotL) (hMN : slotM ≠ slotN) (hKM : slotK ≠ slotM)
    (hKN : slotK ≠ slotN) (hLM : slotL ≠ slotM) (hLN : slotL ≠ slotN)
    (hpair : pairAtomOne ≠ pairAtomTwo) (hco : coAtomOne ≠ coAtomTwo)
    (hshareKL : shareSet frame.tightDir frame.basisLabel slotK slotL
      = {pairAtomOne, pairAtomTwo})
    (hshareMN : shareSet frame.tightDir frame.basisLabel slotM slotN
      = {coAtomOne, coAtomTwo})
    (hshareKM : shareSet frame.tightDir frame.basisLabel slotK slotM
      = {singleKM})
    (hshareLN : shareSet frame.tightDir frame.basisLabel slotL slotN
      = {singleLN})
    (hsuppK : datumTightSupport frame.tightDir (frame.basisLabel slotK)
      = {pairAtomOne, pairAtomTwo, singleKM})
    (hsuppL : datumTightSupport frame.tightDir (frame.basisLabel slotL)
      = {pairAtomOne, pairAtomTwo, singleLN})
    (hsuppM : datumTightSupport frame.tightDir (frame.basisLabel slotM)
      = {coAtomOne, coAtomTwo, singleKM})
    (hsuppN : datumTightSupport frame.tightDir (frame.basisLabel slotN)
      = {coAtomOne, coAtomTwo, singleLN})
    (hdetKL : frame.tightDir (frame.basisLabel slotK) pairAtomOne
        * frame.tightDir (frame.basisLabel slotL) pairAtomTwo
      - frame.tightDir (frame.basisLabel slotK) pairAtomTwo
        * frame.tightDir (frame.basisLabel slotL) pairAtomOne ≠ 0) :
    False := by
  classical
  -- the pattern memberships
  have hmemP1K : pairAtomOne ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotK) := by rw [hsuppK]; simp
  have hmemP1L : pairAtomOne ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotL) := by rw [hsuppL]; simp
  have hmemP2K : pairAtomTwo ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotK) := by rw [hsuppK]; simp
  have hmemP2L : pairAtomTwo ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotL) := by rw [hsuppL]; simp
  have hmemC1M : coAtomOne ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotM) := by rw [hsuppM]; simp
  have hmemC1N : coAtomOne ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotN) := by rw [hsuppN]; simp
  have hmemC2M : coAtomTwo ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotM) := by rw [hsuppM]; simp
  have hmemC2N : coAtomTwo ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotN) := by rw [hsuppN]; simp
  have hmemS4K : singleKM ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotK) := by rw [hsuppK]; simp
  have hmemS4M : singleKM ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotM) := by rw [hsuppM]; simp
  have hmemS5L : singleLN ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotL) := by rw [hsuppL]; simp
  have hmemS5N : singleLN ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotN) := by rw [hsuppN]; simp
  -- the atom distinctions beyond the two given pairs
  have hP1C1 : pairAtomOne ≠ coAtomOne :=
    atom_ne_of_exclusive_carriers hmult hKL hKM.symm hLM.symm
      hmemP1K hmemP1L hmemC1M
  have hP1C2 : pairAtomOne ≠ coAtomTwo :=
    atom_ne_of_exclusive_carriers hmult hKL hKM.symm hLM.symm
      hmemP1K hmemP1L hmemC2M
  have hP2C1 : pairAtomTwo ≠ coAtomOne :=
    atom_ne_of_exclusive_carriers hmult hKL hKM.symm hLM.symm
      hmemP2K hmemP2L hmemC1M
  have hP2C2 : pairAtomTwo ≠ coAtomTwo :=
    atom_ne_of_exclusive_carriers hmult hKL hKM.symm hLM.symm
      hmemP2K hmemP2L hmemC2M
  have hP1S4 : pairAtomOne ≠ singleKM :=
    atom_ne_of_exclusive_carriers hmult hKL hKM.symm hLM.symm
      hmemP1K hmemP1L hmemS4M
  have hP2S4 : pairAtomTwo ≠ singleKM :=
    atom_ne_of_exclusive_carriers hmult hKL hKM.symm hLM.symm
      hmemP2K hmemP2L hmemS4M
  have hP1S5 : pairAtomOne ≠ singleLN :=
    atom_ne_of_exclusive_carriers hmult hKL hKN.symm hLN.symm
      hmemP1K hmemP1L hmemS5N
  have hP2S5 : pairAtomTwo ≠ singleLN :=
    atom_ne_of_exclusive_carriers hmult hKL hKN.symm hLN.symm
      hmemP2K hmemP2L hmemS5N
  have hC1S4 : coAtomOne ≠ singleKM :=
    atom_ne_of_exclusive_carriers hmult hMN hKM hKN
      hmemC1M hmemC1N hmemS4K
  have hC2S4 : coAtomTwo ≠ singleKM :=
    atom_ne_of_exclusive_carriers hmult hMN hKM hKN
      hmemC2M hmemC2N hmemS4K
  have hC1S5 : coAtomOne ≠ singleLN :=
    atom_ne_of_exclusive_carriers hmult hMN hLM hLN
      hmemC1M hmemC1N hmemS5L
  have hC2S5 : coAtomTwo ≠ singleLN :=
    atom_ne_of_exclusive_carriers hmult hMN hLM hLN
      hmemC2M hmemC2N hmemS5L
  have hS4S5 : singleKM ≠ singleLN :=
    atom_ne_of_exclusive_carriers hmult hKM hKN.symm hMN.symm
      hmemS4K hmemS4M hmemS5N
  -- the active-subset memberships
  have hsubK := datumTightSupport_subset frame.hdata (frame.hmemAll slotK)
  have hsubL := datumTightSupport_subset frame.hdata (frame.hmemAll slotL)
  have hsubM := datumTightSupport_subset frame.hdata (frame.hmemAll slotM)
  have hsubN := datumTightSupport_subset frame.hdata (frame.hmemAll slotN)
  -- the off-carrier vanish laws per atom
  have hvanP1 : ∀ columnIndex, columnIndex ≠ slotK → columnIndex ≠ slotL →
      frame.tightDir (frame.basisLabel columnIndex) pairAtomOne = 0 :=
    fun columnIndex hcK hcL => tightDir_vanish_of_multiplicity_two
      frame.basisLabel hmult hKL (Ne.symm hcK) (Ne.symm hcL) hmemP1K hmemP1L
  have hvanP2 : ∀ columnIndex, columnIndex ≠ slotK → columnIndex ≠ slotL →
      frame.tightDir (frame.basisLabel columnIndex) pairAtomTwo = 0 :=
    fun columnIndex hcK hcL => tightDir_vanish_of_multiplicity_two
      frame.basisLabel hmult hKL (Ne.symm hcK) (Ne.symm hcL) hmemP2K hmemP2L
  have hvanC1 : ∀ columnIndex, columnIndex ≠ slotM → columnIndex ≠ slotN →
      frame.tightDir (frame.basisLabel columnIndex) coAtomOne = 0 :=
    fun columnIndex hcM hcN => tightDir_vanish_of_multiplicity_two
      frame.basisLabel hmult hMN (Ne.symm hcM) (Ne.symm hcN) hmemC1M hmemC1N
  have hvanC2 : ∀ columnIndex, columnIndex ≠ slotM → columnIndex ≠ slotN →
      frame.tightDir (frame.basisLabel columnIndex) coAtomTwo = 0 :=
    fun columnIndex hcM hcN => tightDir_vanish_of_multiplicity_two
      frame.basisLabel hmult hMN (Ne.symm hcM) (Ne.symm hcN) hmemC2M hmemC2N
  have hvanS4 : ∀ columnIndex, columnIndex ≠ slotK → columnIndex ≠ slotM →
      frame.tightDir (frame.basisLabel columnIndex) singleKM = 0 :=
    fun columnIndex hcK hcM => tightDir_vanish_of_multiplicity_two
      frame.basisLabel hmult hKM (Ne.symm hcK) (Ne.symm hcM) hmemS4K hmemS4M
  have hvanS5 : ∀ columnIndex, columnIndex ≠ slotL → columnIndex ≠ slotN →
      frame.tightDir (frame.basisLabel columnIndex) singleLN = 0 :=
    fun columnIndex hcL hcN => tightDir_vanish_of_multiplicity_two
      frame.basisLabel hmult hLN (Ne.symm hcL) (Ne.symm hcN) hmemS5L hmemS5N
  -- the branch split on the second cross determinant
  by_cases hdetMN : frame.tightDir (frame.basisLabel slotM) coAtomOne
      * frame.tightDir (frame.basisLabel slotN) coAtomTwo
    - frame.tightDir (frame.basisLabel slotM) coAtomTwo
      * frame.tightDir (frame.basisLabel slotN) coAtomOne = 0
  · -- the seam branch: the second pair is parallel
    have hwcEq : (chartPointOfDesign crux.design).weight coAtomOne
        = (chartPointOfDesign crux.design).weight coAtomTwo :=
      pair_weight_eq_of_parallel frame.hdata frame.basisLabel
        frame.hrepresentation hMN (frame.hmemAll slotM)
        (hsubM hmemC1M) (hsubM hmemC2M) hvanC1 hvanC2
        (mem_datumTightSupport.mp hmemC1M) (mem_datumTightSupport.mp hmemC2M)
        hdetMN
    -- the pattern objects
    set sv : Fin 4 → Fin 4 := ![slotK, slotL, slotM, slotN] with hsv
    set Mpat : Matrix (Fin 4) (Fin 4) ℝ := frame.coeff.submatrix sv sv
      with hMpat
    set Γpat : Matrix (Fin 4) (Fin 4) ℝ :=
      (basisGram frame.tightDir frame.basisLabel).submatrix sv sv with hΓpat
    have hsv0 : sv 0 = slotK := rfl
    have hsv1 : sv 1 = slotL := rfl
    have hsv2 : sv 2 = slotM := rfl
    have hsv3 : sv 3 = slotN := rfl
    -- idempotency and the trace transport
    have hidemPat : Mpat * Mpat = Mpat := by
      rw [hMpat, submatrix_four_mul _ _ hKL hKM hKN hLM hLN hMN,
        frame.hidempotent]
    have htracePat : Mpat 0 0 + Mpat 1 1 + Mpat 2 2 + Mpat 3 3 = 2 := by
      have htr := frame.htrace
      rw [trace_eq_four_diag hKL hKM hKN hLM hLN hMN] at htr
      exact htr
    -- the product transport
    have hmulPat : Γpat * Mpat
        = (basisGram frame.tightDir frame.basisLabel * frame.coeff).submatrix
          sv sv := by
      rw [hΓpat, hMpat, submatrix_four_mul _ _ hKL hKM hKN hLM hLN hMN]
    -- the exchange symmetry transport
    have hsymPat : (Γpat * Mpat)ᵀ = Γpat * Mpat := by
      rw [hmulPat, Matrix.transpose_submatrix,
        gram_exchange_transpose frame.basisLabel frame.hdata.isSymmetric
          frame.hdata.isIdempotent frame.hrepresentation]
    -- the coordinate names
    set qK0 := frame.tightDir (frame.basisLabel slotK) pairAtomOne
    set qK1 := frame.tightDir (frame.basisLabel slotK) pairAtomTwo
    set qK4 := frame.tightDir (frame.basisLabel slotK) singleKM
    set qL0 := frame.tightDir (frame.basisLabel slotL) pairAtomOne
    set qL1 := frame.tightDir (frame.basisLabel slotL) pairAtomTwo
    set qL5 := frame.tightDir (frame.basisLabel slotL) singleLN
    set qM2 := frame.tightDir (frame.basisLabel slotM) coAtomOne
    set qM3 := frame.tightDir (frame.basisLabel slotM) coAtomTwo
    set qM4 := frame.tightDir (frame.basisLabel slotM) singleKM
    set qN2 := frame.tightDir (frame.basisLabel slotN) coAtomOne
    set qN3 := frame.tightDir (frame.basisLabel slotN) coAtomTwo
    set qN5 := frame.tightDir (frame.basisLabel slotN) singleLN
    -- the coordinate vanishing off each support
    have hqKc1 : frame.tightDir (frame.basisLabel slotK) coAtomOne = 0 :=
      coordinate_zero_of_support_eq hsuppK
        (by simp [Ne.symm hP1C1, Ne.symm hP2C1, hC1S4])
    have hqKc2 : frame.tightDir (frame.basisLabel slotK) coAtomTwo = 0 :=
      coordinate_zero_of_support_eq hsuppK
        (by simp [Ne.symm hP1C2, Ne.symm hP2C2, hC2S4])
    have hqKs5 : frame.tightDir (frame.basisLabel slotK) singleLN = 0 :=
      coordinate_zero_of_support_eq hsuppK
        (by simp [Ne.symm hP1S5, Ne.symm hP2S5, Ne.symm hS4S5])
    have hqLc1 : frame.tightDir (frame.basisLabel slotL) coAtomOne = 0 :=
      coordinate_zero_of_support_eq hsuppL
        (by simp [Ne.symm hP1C1, Ne.symm hP2C1, hC1S5])
    have hqLc2 : frame.tightDir (frame.basisLabel slotL) coAtomTwo = 0 :=
      coordinate_zero_of_support_eq hsuppL
        (by simp [Ne.symm hP1C2, Ne.symm hP2C2, hC2S5])
    have hqLs4 : frame.tightDir (frame.basisLabel slotL) singleKM = 0 :=
      coordinate_zero_of_support_eq hsuppL
        (by simp [Ne.symm hP1S4, Ne.symm hP2S4, hS4S5])
    have hqMp1 : frame.tightDir (frame.basisLabel slotM) pairAtomOne = 0 :=
      coordinate_zero_of_support_eq hsuppM
        (by simp [hP1C1, hP1C2, hP1S4])
    have hqMp2 : frame.tightDir (frame.basisLabel slotM) pairAtomTwo = 0 :=
      coordinate_zero_of_support_eq hsuppM
        (by simp [hP2C1, hP2C2, hP2S4])
    have hqMs5 : frame.tightDir (frame.basisLabel slotM) singleLN = 0 :=
      coordinate_zero_of_support_eq hsuppM
        (by simp [Ne.symm hC1S5, Ne.symm hC2S5, Ne.symm hS4S5])
    have hqNp1 : frame.tightDir (frame.basisLabel slotN) pairAtomOne = 0 :=
      coordinate_zero_of_support_eq hsuppN
        (by simp [hP1C1, hP1C2, hP1S5])
    have hqNp2 : frame.tightDir (frame.basisLabel slotN) pairAtomTwo = 0 :=
      coordinate_zero_of_support_eq hsuppN
        (by simp [hP2C1, hP2C2, hP2S5])
    have hqNs4 : frame.tightDir (frame.basisLabel slotN) singleKM = 0 :=
      coordinate_zero_of_support_eq hsuppN
        (by simp [Ne.symm hC1S4, Ne.symm hC2S4, hS4S5])
    -- the Gamma entries in pattern position
    have hshareKN : shareSet frame.tightDir frame.basisLabel slotK slotN
        = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro atomIndex hmemShare
      rw [shareSet, Finset.mem_filter] at hmemShare
      obtain ⟨-, hmemAK, hmemAN⟩ := hmemShare
      rw [hsuppK] at hmemAK
      rw [hsuppN] at hmemAN
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmemAK hmemAN
      rcases hmemAK with rfl | rfl | rfl <;>
        rcases hmemAN with rfl | rfl | rfl <;> simp_all
    have hshareLM : shareSet frame.tightDir frame.basisLabel slotL slotM
        = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro atomIndex hmemShare
      rw [shareSet, Finset.mem_filter] at hmemShare
      obtain ⟨-, hmemAL, hmemAM⟩ := hmemShare
      rw [hsuppL] at hmemAL
      rw [hsuppM] at hmemAM
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmemAL hmemAM
      rcases hmemAL with rfl | rfl | rfl <;>
        rcases hmemAM with rfl | rfl | rfl <;> simp_all
    have hgramKL : basisGram frame.tightDir frame.basisLabel slotK slotL
        = qK0 * qL0 + qK1 * qL1 :=
      basisGram_double_of_share_pair frame.basisLabel hpair hshareKL
    have hgramMN : basisGram frame.tightDir frame.basisLabel slotM slotN
        = qM2 * qN2 + qM3 * qN3 :=
      basisGram_double_of_share_pair frame.basisLabel hco hshareMN
    have hgramKM : basisGram frame.tightDir frame.basisLabel slotK slotM
        = qK4 * qM4 :=
      kfour_gram_offdiag frame.basisLabel hshareKM
    have hgramLN : basisGram frame.tightDir frame.basisLabel slotL slotN
        = qL5 * qN5 :=
      kfour_gram_offdiag frame.basisLabel hshareLN
    have hgramKN : basisGram frame.tightDir frame.basisLabel slotK slotN
        = 0 :=
      basisGram_zero_of_share_empty frame.basisLabel hshareKN
    have hgramLM : basisGram frame.tightDir frame.basisLabel slotL slotM
        = 0 :=
      basisGram_zero_of_share_empty frame.basisLabel hshareLM
    have hgramSymm : ∀ slotA slotB : Fin 4,
        basisGram frame.tightDir frame.basisLabel slotA slotB
          = basisGram frame.tightDir frame.basisLabel slotB slotA := by
      intro slotA slotB
      rw [basisGram_apply, basisGram_apply, dotProduct_comm]
    have hΓlit : Γpat
        = !![1, qK0 * qL0 + qK1 * qL1, qK4 * qM4, 0;
             qK0 * qL0 + qK1 * qL1, 1, 0, qL5 * qN5;
             qK4 * qM4, 0, 1, qM2 * qN2 + qM3 * qN3;
             0, qL5 * qN5, qM2 * qN2 + qM3 * qN3, 1] := by
      ext rowIndex colIndex
      fin_cases rowIndex <;> fin_cases colIndex <;>
        simp [hΓpat, hsv]
      · exact basisGram_diagonal_of_mem frame.hdata frame.basisLabel
          (frame.hmemAll slotK)
      · exact hgramKL
      · exact hgramKM
      · exact hgramKN
      · rw [hgramSymm slotL slotK]; exact hgramKL
      · exact basisGram_diagonal_of_mem frame.hdata frame.basisLabel
          (frame.hmemAll slotL)
      · exact hgramLM
      · exact hgramLN
      · rw [hgramSymm slotM slotK]; exact hgramKM
      · rw [hgramSymm slotM slotL]; exact hgramLM
      · exact basisGram_diagonal_of_mem frame.hdata frame.basisLabel
          (frame.hmemAll slotM)
      · exact hgramMN
      · rw [hgramSymm slotN slotK]; exact hgramKN
      · rw [hgramSymm slotN slotL]; exact hgramLN
      · rw [hgramSymm slotN slotM]; exact hgramMN
      · exact basisGram_diagonal_of_mem frame.hdata frame.basisLabel
          (frame.hmemAll slotN)
    -- the diagonal reads in pattern position
    have hdiagK : (Γpat * Mpat) 0 0
        = chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight pairAtomOne * qK0 ^ 2
          + (chartPointOfDesign crux.design).weight pairAtomTwo * qK1 ^ 2
          + (chartPointOfDesign crux.design).weight singleKM * qK4 ^ 2 := by
      rw [hmulPat]
      have hread := gram_exchange_diag_read frame.hdata frame.basisLabel
        frame.hrepresentation (frame.hmemAll slotK)
      rw [sum_six_atoms (fun atomIndex =>
          (chartPointOfDesign crux.design).weight atomIndex
            * frame.tightDir (frame.basisLabel slotK) atomIndex ^ 2)
        hpair hP1C1 hP1C2 hP1S4 hP1S5 hP2C1 hP2C2 hP2S4 hP2S5 hco hC1S4
        hC1S5 hC2S4 hC2S5 hS4S5] at hread
      rw [hqKc1, hqKc2, hqKs5] at hread
      simp only [Matrix.submatrix_apply, hsv0]
      rw [hread]
      ring
    have hdiagL : (Γpat * Mpat) 1 1
        = chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight pairAtomOne * qL0 ^ 2
          + (chartPointOfDesign crux.design).weight pairAtomTwo * qL1 ^ 2
          + (chartPointOfDesign crux.design).weight singleLN * qL5 ^ 2 := by
      rw [hmulPat]
      have hread := gram_exchange_diag_read frame.hdata frame.basisLabel
        frame.hrepresentation (frame.hmemAll slotL)
      rw [sum_six_atoms (fun atomIndex =>
          (chartPointOfDesign crux.design).weight atomIndex
            * frame.tightDir (frame.basisLabel slotL) atomIndex ^ 2)
        hpair hP1C1 hP1C2 hP1S4 hP1S5 hP2C1 hP2C2 hP2S4 hP2S5 hco hC1S4
        hC1S5 hC2S4 hC2S5 hS4S5] at hread
      rw [hqLc1, hqLc2, hqLs4] at hread
      simp only [Matrix.submatrix_apply, hsv1]
      rw [hread]
      ring
    have hdiagM : (Γpat * Mpat) 2 2
        = chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight coAtomOne * qM2 ^ 2
          + (chartPointOfDesign crux.design).weight coAtomOne * qM3 ^ 2
          + (chartPointOfDesign crux.design).weight singleKM * qM4 ^ 2 := by
      rw [hmulPat]
      have hread := gram_exchange_diag_read frame.hdata frame.basisLabel
        frame.hrepresentation (frame.hmemAll slotM)
      rw [sum_six_atoms (fun atomIndex =>
          (chartPointOfDesign crux.design).weight atomIndex
            * frame.tightDir (frame.basisLabel slotM) atomIndex ^ 2)
        hpair hP1C1 hP1C2 hP1S4 hP1S5 hP2C1 hP2C2 hP2S4 hP2S5 hco hC1S4
        hC1S5 hC2S4 hC2S5 hS4S5] at hread
      rw [hqMp1, hqMp2, hqMs5, ← hwcEq] at hread
      simp only [Matrix.submatrix_apply, hsv2]
      rw [hread]
      ring
    have hdiagN : (Γpat * Mpat) 3 3
        = chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight coAtomOne * qN2 ^ 2
          + (chartPointOfDesign crux.design).weight coAtomOne * qN3 ^ 2
          + (chartPointOfDesign crux.design).weight singleLN * qN5 ^ 2 := by
      rw [hmulPat]
      have hread := gram_exchange_diag_read frame.hdata frame.basisLabel
        frame.hrepresentation (frame.hmemAll slotN)
      rw [sum_six_atoms (fun atomIndex =>
          (chartPointOfDesign crux.design).weight atomIndex
            * frame.tightDir (frame.basisLabel slotN) atomIndex ^ 2)
        hpair hP1C1 hP1C2 hP1S4 hP1S5 hP2C1 hP2C2 hP2S4 hP2S5 hco hC1S4
        hC1S5 hC2S4 hC2S5 hS4S5] at hread
      rw [hqNp1, hqNp2, hqNs4, ← hwcEq] at hread
      simp only [Matrix.submatrix_apply, hsv3]
      rw [hread]
      ring
    -- the weight sum in pattern order
    have hwsum : (chartPointOfDesign crux.design).weight pairAtomOne
        + (chartPointOfDesign crux.design).weight pairAtomTwo
        + 2 * (chartPointOfDesign crux.design).weight coAtomOne
        + (chartPointOfDesign crux.design).weight singleKM
        + (chartPointOfDesign crux.design).weight singleLN = 1 := by
      have hsum := frame.hdata.weight_sum_one
      rw [sum_six_atoms (chartPointOfDesign crux.design).weight
        hpair hP1C1 hP1C2 hP1S4 hP1S5 hP2C1 hP2C2 hP2S4 hP2S5 hco hC1S4
        hC1S5 hC2S4 hC2S5 hS4S5] at hsum
      rw [← hwcEq] at hsum
      linarith
    -- the unit norms in pattern coordinates
    have hnormK : qK0 ^ 2 + qK1 ^ 2 + qK4 ^ 2 = 1 :=
      kfour_unit_norm_expand frame.hdata frame.basisLabel
        (frame.hmemAll slotK) hsuppK hpair hP1S4 hP2S4
    have hnormL : qL0 ^ 2 + qL1 ^ 2 + qL5 ^ 2 = 1 :=
      kfour_unit_norm_expand frame.hdata frame.basisLabel
        (frame.hmemAll slotL) hsuppL hpair hP1S5 hP2S5
    have hnormM : qM2 ^ 2 + qM3 ^ 2 + qM4 ^ 2 = 1 :=
      kfour_unit_norm_expand frame.hdata frame.basisLabel
        (frame.hmemAll slotM) hsuppM hco hC1S4 hC2S4
    have hnormN : qN2 ^ 2 + qN3 ^ 2 + qN5 ^ 2 = 1 :=
      kfour_unit_norm_expand frame.hdata frame.basisLabel
        (frame.hmemAll slotN) hsuppN hco hC1S5 hC2S5
    -- the twelve carried reads in pattern position
    have hreadP1K := two_carrier_row_reading frame.hdata frame.basisLabel
      frame.hrepresentation hKL (frame.hmemAll slotK) (hsubK hmemP1K) hvanP1
    have hreadP1L := two_carrier_row_reading frame.hdata frame.basisLabel
      frame.hrepresentation hKL (frame.hmemAll slotL) (hsubL hmemP1L) hvanP1
    have hreadP2K := two_carrier_row_reading frame.hdata frame.basisLabel
      frame.hrepresentation hKL (frame.hmemAll slotK) (hsubK hmemP2K) hvanP2
    have hreadP2L := two_carrier_row_reading frame.hdata frame.basisLabel
      frame.hrepresentation hKL (frame.hmemAll slotL) (hsubL hmemP2L) hvanP2
    have hreadC1M := two_carrier_row_reading frame.hdata frame.basisLabel
      frame.hrepresentation hMN (frame.hmemAll slotM) (hsubM hmemC1M) hvanC1
    have hreadC1N := two_carrier_row_reading frame.hdata frame.basisLabel
      frame.hrepresentation hMN (frame.hmemAll slotN) (hsubN hmemC1N) hvanC1
    have hreadC2M := two_carrier_row_reading frame.hdata frame.basisLabel
      frame.hrepresentation hMN (frame.hmemAll slotM) (hsubM hmemC2M) hvanC2
    have hreadC2N := two_carrier_row_reading frame.hdata frame.basisLabel
      frame.hrepresentation hMN (frame.hmemAll slotN) (hsubN hmemC2N) hvanC2
    have hreadS4K := two_carrier_row_reading frame.hdata frame.basisLabel
      frame.hrepresentation hKM (frame.hmemAll slotK) (hsubK hmemS4K) hvanS4
    have hreadS4M := two_carrier_row_reading frame.hdata frame.basisLabel
      frame.hrepresentation hKM (frame.hmemAll slotM) (hsubM hmemS4M) hvanS4
    have hreadS5L := two_carrier_row_reading frame.hdata frame.basisLabel
      frame.hrepresentation hLN (frame.hmemAll slotL) (hsubL hmemS5L) hvanS5
    have hreadS5N := two_carrier_row_reading frame.hdata frame.basisLabel
      frame.hrepresentation hLN (frame.hmemAll slotN) (hsubN hmemS5N) hvanS5
    -- the co-pair weight rewrite on the four co reads
    rw [← hwcEq] at hreadC2M hreadC2N
    -- feed the certificate
    exact hcert (chartObjective (chartPointOfDesign crux.design))
      ((chartPointOfDesign crux.design).weight pairAtomOne)
      ((chartPointOfDesign crux.design).weight pairAtomTwo)
      ((chartPointOfDesign crux.design).weight coAtomOne)
      ((chartPointOfDesign crux.design).weight singleKM)
      ((chartPointOfDesign crux.design).weight singleLN)
      qK0 qK1 qK4 qL0 qL1 qL5 qM2 qM3 qM4 qN2 qN3 qN5 Mpat Γpat
      frame.hvalueNeg
      (frame.hdata.weight_pos pairAtomOne)
      (frame.hdata.weight_pos pairAtomTwo)
      (frame.hdata.weight_pos coAtomOne)
      (frame.hdata.weight_pos singleKM)
      (frame.hdata.weight_pos singleLN)
      hwsum hidemPat htracePat
      hreadP1K hreadP1L hreadP2K hreadP2L
      hreadC1M hreadC1N hreadC2M hreadC2N
      hreadS4K hreadS4M hreadS5L hreadS5N
      hnormK hnormL hnormM hnormN
      hΓlit hsymPat hdiagK hdiagL hdiagM hdiagN
      hdetMN hdetKL
      (mem_datumTightSupport.mp hmemP1K) (mem_datumTightSupport.mp hmemP2K)
      (mem_datumTightSupport.mp hmemS4K) (mem_datumTightSupport.mp hmemP1L)
      (mem_datumTightSupport.mp hmemP2L) (mem_datumTightSupport.mp hmemS5L)
      (mem_datumTightSupport.mp hmemC1M) (mem_datumTightSupport.mp hmemC2M)
      (mem_datumTightSupport.mp hmemS4M) (mem_datumTightSupport.mp hmemC1N)
      (mem_datumTightSupport.mp hmemC2N) (mem_datumTightSupport.mp hmemS5N)
  · -- the double-independent branch dies on the trace budget
    have htraceKL := corner_trace_of_cross_det frame.hdata frame.basisLabel
      frame.hrepresentation hKL (frame.hmemAll slotK) (frame.hmemAll slotL)
      (hsubK hmemP1K) (hsubL hmemP1L) (hsubK hmemP2K) (hsubL hmemP2L)
      hvanP1 hvanP2 hdetKL
    have htraceMN := corner_trace_of_cross_det frame.hdata frame.basisLabel
      frame.hrepresentation hMN (frame.hmemAll slotM) (frame.hmemAll slotN)
      (hsubM hmemC1M) (hsubN hmemC1N) (hsubM hmemC2M) (hsubN hmemC2N)
      hvanC1 hvanC2 hdetMN
    exact false_of_double_trace_laws frame.hdata frame.hvalueNeg
      frame.htrace hKL hKM hKN hLM hLN hMN hpair hP1C1 hP1C2 hP2C1 hP2C2
      hco htraceKL htraceMN

/-! ## Layer 7 — the discharge -/

/-- **THE DISCHARGE.**  The seam certificate closes the independent
cycle: the disjunction resolves by the symmetric re-application of the
seam application. -/
theorem rankFourCycleIndependentClosed_of_seam_certificate
    (hcert : CycleSeamCertificate) : RankFourCycleIndependentClosed := by
  intro crux frame slotK slotL slotM slotN pairAtomOne pairAtomTwo
    coAtomOne coAtomTwo singleKM singleLN hmult hKL hMN hKM hKN hLM hLN
    hpair hco hshareKL hshareMN hshareKM hshareLN hsuppK hsuppL hsuppM
    hsuppN hdisj
  rcases hdisj with hdetKL | hdetMN
  · exact frame.false_of_cycle_first_independent hcert slotK slotL slotM
      slotN pairAtomOne pairAtomTwo coAtomOne coAtomTwo singleKM singleLN
      hmult hKL hMN hKM hKN hLM hLN hpair hco hshareKL hshareMN hshareKM
      hshareLN hsuppK hsuppL hsuppM hsuppN hdetKL
  · exact frame.false_of_cycle_first_independent hcert slotM slotN slotK
      slotL coAtomOne coAtomTwo pairAtomOne pairAtomTwo singleKM singleLN
      hmult hMN hKL hKM.symm hLM.symm hKN.symm hLN.symm hco hpair hshareMN
      hshareKL
      (by rw [shareSet_comm]; exact hshareKM)
      (by rw [shareSet_comm]; exact hshareLN)
      hsuppM hsuppN hsuppK hsuppL hdetMN

end Gtz
