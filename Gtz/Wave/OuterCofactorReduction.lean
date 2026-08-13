import Gtz.Wave.OuterSharerDualScaffold
import Gtz.Wave.RankSixClosureSupply

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The outer cofactor reduction — the adjugate certificate and the two residues

The outer-sharer kill of the support-two closures is a diagonal Farkas
certificate.  The transfer scan of this session gives the counting law
of that certificate.  The certificate vector is an annihilator of the
squared basis columns.  At rank four the five square columns leave room
for an outside-supported annihilator.  At rank five the six square
columns leave room for one full-support annihilator.  At rank six the
seven square columns fill the space, and no annihilator remains.  The
scan confirms each count on the honest joint manifold: the outside dual
holds at every rank-four witness, the full dual holds at every rank-five
witness, and the rank-six diagonal system admits feasible witnesses.

This file lands the adjugate form of that certificate.  The adjugate row
of a square matrix annihilates every other column and reads the
determinant against a column of ones.  The assembly diagonal turns the
annihilation into a balance: the squared determinant is a weighted sum
of capped terms.  Thus capped extras force the determinant to zero, and
the kill splits into two named residues per rank: the extras cap and the
det-zero stratum kill.  The two bridge compositions consume the residues
and close the rank-four and the rank-five support-two closures.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.adjugate_row_pairing` — the adjugate row against each column.
* `Gtz.adjugate_row_annihilates` — the annihilation at the other columns.
* `Gtz.adjugate_row_margin` — the determinant read at the ones column.
* `Gtz.dual_pairing_balance` — **THE BALANCE.**
* `Gtz.det_eq_zero_of_capped_certificate` — **THE DET COLLAPSE.**
* `Gtz.RankFourOuterData.squareMatrix_ones`, `..._basisColumn`,
  `..._filler` — the rank-four entry reads.
* `Gtz.RankFourOuterData.dualRow_annihilates_basis` — the equality caps.
* `Gtz.RankFourOuterData.dualRow_pair_difference`,
  `..._atomU_eq_zero`, `..._atomV_eq_zero` — **THE OUTSIDE SUPPORT.**
* `Gtz.RankFourOuterData.killed_of_residues` — the rank-four kill
  modulo the two residues.
* `Gtz.rankFourSupportTwoClosed_of_cofactor_residues` — **THE RANK-FOUR
  BRIDGE COMPOSITION.**
* `Gtz.RankFiveOuterData.squareMatrix_ones`, `..._basisColumn`,
  `..._dualRow_annihilates_basis` — the rank-five reads and caps.
* `Gtz.RankFiveOuterData.killed_of_residues` — the rank-five kill
  modulo the two residues.
* `Gtz.rankFiveSupportTwoClosed_of_cofactor_residues` — **THE RANK-FIVE
  BRIDGE COMPOSITION.**

## The transfer verdict

The scan `certA3_scan.c` generalizes the honest joint probe to random
outer-block shapes and to four or five outer columns.  Verdicts: at
three outer columns the outside LP is infeasible at 30 of 30 witnesses.
At four outer columns the outside LP is feasible at some witnesses, but
the full LP is infeasible at 80 of 80.  At five outer columns the full
LP is feasible at some witnesses.  Thus the rank-six kill cannot exit
through the diagonal certificate alone, and this file lands no rank-six
instantiation.

## Vacuity

The closure statements are vacuous if `Gtz.GtzWeighted 6 3` holds: no
crux exists, thus no frame exists.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## Layer 1 — the adjugate certificate calculus -/

/-- The adjugate row against each column: the pairing reads the
determinant times the identity entry. -/
theorem adjugate_row_pairing {n : ℕ} [NeZero n]
    (squareMat : Matrix (Fin n) (Fin n) ℝ) (colIndex : Fin n) :
    ∑ atomIndex : Fin n,
        squareMat.adjugate 0 atomIndex * squareMat atomIndex colIndex
      = squareMat.det * (if (0 : Fin n) = colIndex then 1 else 0) := by
  have hmul := Matrix.adjugate_mul squareMat
  have hentry : (squareMat.adjugate * squareMat) 0 colIndex
      = (squareMat.det • (1 : Matrix (Fin n) (Fin n) ℝ)) 0 colIndex := by
    rw [hmul]
  rw [Matrix.mul_apply] at hentry
  rw [hentry, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]

/-- The annihilation: the adjugate row kills every column other than the
first one. -/
theorem adjugate_row_annihilates {n : ℕ} [NeZero n]
    (squareMat : Matrix (Fin n) (Fin n) ℝ) {colIndex : Fin n}
    (hne : colIndex ≠ 0) :
    ∑ atomIndex : Fin n,
        squareMat.adjugate 0 atomIndex * squareMat atomIndex colIndex = 0 := by
  rw [adjugate_row_pairing squareMat colIndex,
    if_neg fun heq => hne heq.symm, mul_zero]

/-- The margin: against a first column of ones, the adjugate row sums to
the determinant. -/
theorem adjugate_row_margin {n : ℕ} [NeZero n]
    (squareMat : Matrix (Fin n) (Fin n) ℝ)
    (hones : ∀ atomIndex, squareMat atomIndex 0 = 1) :
    ∑ atomIndex : Fin n, squareMat.adjugate 0 atomIndex = squareMat.det := by
  have hpair := adjugate_row_pairing squareMat 0
  rw [if_pos rfl, mul_one] at hpair
  rw [← hpair]
  exact Finset.sum_congr rfl fun atomIndex _ => by rw [hones atomIndex, mul_one]

/-- **THE BALANCE.**  The multiplier-weighted sum of the label caps of
any coefficient vector, scaled by the size, is the coefficient sum.
This is the constant assembly diagonal in dual form. -/
theorem dual_pairing_balance
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (dualCoeff : Fin size → ℝ) :
    (∑ activeLabel ∈ activeSet, activeWeight activeLabel
        * ∑ atomIndex : Fin size,
            dualCoeff atomIndex * tightDir activeLabel atomIndex ^ 2)
      * (size : ℝ)
      = ∑ atomIndex : Fin size, dualCoeff atomIndex := by
  have hswap := dual_pairing_swap dualCoeff activeSet activeWeight tightDir
  have hdiag : ∑ atomIndex : Fin size, dualCoeff atomIndex
        * chartMultiplierAssembly activeSet activeWeight tightDir
            atomIndex atomIndex
      = (∑ atomIndex : Fin size, dualCoeff atomIndex) * ((size : ℝ))⁻¹ := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun atomIndex _ => by
      rw [hdata.assembly_diagonal atomIndex]
  have hsize : (0 : ℝ) < (size : ℝ) :=
    size_cast_pos_of_isChartStationaryData hdata
  rw [← hswap, hdiag]
  exact inv_mul_cancel_right₀ (ne_of_gt hsize) _

/-- **THE DET COLLAPSE.**  A square matrix with a first column of ones,
whose adjugate-row caps are nonpositive against the determinant on every
positively weighted active label, has determinant zero.  The proof
squares the determinant through the balance. -/
theorem det_eq_zero_of_capped_certificate [NeZero size]
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (squareMat : Matrix (Fin size) (Fin size) ℝ)
    (hones : ∀ atomIndex, squareMat atomIndex 0 = 1)
    (hcap : ∀ activeLabel ∈ activeSet, 0 < activeWeight activeLabel →
      (∑ atomIndex : Fin size,
          squareMat.adjugate 0 atomIndex * tightDir activeLabel atomIndex ^ 2)
        * squareMat.det ≤ 0) :
    squareMat.det = 0 := by
  have hbal := dual_pairing_balance hdata (squareMat.adjugate 0)
  have hmargin := adjugate_row_margin squareMat hones
  have hdet : (∑ activeLabel ∈ activeSet, activeWeight activeLabel
        * ∑ atomIndex : Fin size,
            squareMat.adjugate 0 atomIndex * tightDir activeLabel atomIndex ^ 2)
      * (size : ℝ) = squareMat.det := by rw [hbal, hmargin]
  have hassoc : ∑ activeLabel ∈ activeSet, activeWeight activeLabel
        * (∑ atomIndex : Fin size,
            squareMat.adjugate 0 atomIndex * tightDir activeLabel atomIndex ^ 2)
        * squareMat.det
      = ∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * ((∑ atomIndex : Fin size,
              squareMat.adjugate 0 atomIndex
                * tightDir activeLabel atomIndex ^ 2)
            * squareMat.det) :=
    Finset.sum_congr rfl fun activeLabel _ => mul_assoc _ _ _
  have hkey : squareMat.det ^ 2
      = (∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * ((∑ atomIndex : Fin size,
              squareMat.adjugate 0 atomIndex
                * tightDir activeLabel atomIndex ^ 2)
            * squareMat.det)) * (size : ℝ) := by
    calc squareMat.det ^ 2
        = ((∑ activeLabel ∈ activeSet, activeWeight activeLabel
            * ∑ atomIndex : Fin size,
                squareMat.adjugate 0 atomIndex
                  * tightDir activeLabel atomIndex ^ 2)
          * (size : ℝ)) * squareMat.det := by rw [hdet]; ring
      _ = ((∑ activeLabel ∈ activeSet, activeWeight activeLabel
            * ∑ atomIndex : Fin size,
                squareMat.adjugate 0 atomIndex
                  * tightDir activeLabel atomIndex ^ 2)
          * squareMat.det) * (size : ℝ) := by ring
      _ = (∑ activeLabel ∈ activeSet, activeWeight activeLabel
            * (∑ atomIndex : Fin size,
                squareMat.adjugate 0 atomIndex
                  * tightDir activeLabel atomIndex ^ 2)
            * squareMat.det) * (size : ℝ) := by rw [Finset.sum_mul]
      _ = (∑ activeLabel ∈ activeSet, activeWeight activeLabel
            * ((∑ atomIndex : Fin size,
                squareMat.adjugate 0 atomIndex
                  * tightDir activeLabel atomIndex ^ 2)
              * squareMat.det)) * (size : ℝ) := by rw [hassoc]
  have hnonpos : ∑ activeLabel ∈ activeSet, activeWeight activeLabel
      * ((∑ atomIndex : Fin size,
          squareMat.adjugate 0 atomIndex * tightDir activeLabel atomIndex ^ 2)
        * squareMat.det) ≤ 0 := by
    refine Finset.sum_nonpos fun activeLabel hmem => ?_
    rcases (hdata.activeWeight_nonneg activeLabel hmem).lt_or_eq with hw | hw
    · calc activeWeight activeLabel
          * ((∑ atomIndex : Fin size,
              squareMat.adjugate 0 atomIndex
                * tightDir activeLabel atomIndex ^ 2)
            * squareMat.det)
        ≤ activeWeight activeLabel * 0 :=
          mul_le_mul_of_nonneg_left (hcap activeLabel hmem hw) hw.le
      _ = 0 := mul_zero _
    · rw [← hw, zero_mul]
  have hsize : (0 : ℝ) < (size : ℝ) :=
    size_cast_pos_of_isChartStationaryData hdata
  have hle : squareMat.det ^ 2 ≤ 0 := by
    rw [hkey]
    have hprod := mul_le_mul_of_nonneg_right hnonpos hsize.le
    simpa using hprod
  have hzero : squareMat.det ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
  exact pow_eq_zero_iff (by norm_num) |>.mp hzero

/-! ## Layer 2 — the rank-four cofactor reduction -/

/-- **THE RANK-FOUR OUTER DATUM.**  The reified killOuter tuple of the
rank-four bridge: the frame, the support-two pair column, and the outer
sharer with its alive atom outside the pair. -/
structure RankFourOuterData (crux : SixThreeCrux) where
  /-- The rank-four frame. -/
  frame : RankFourFrame crux
  /-- The pair column index. -/
  columnIndex : Fin 4
  /-- The outer sharer index. -/
  otherIndex : Fin 4
  /-- The left pair atom. -/
  atomU : Fin 6
  /-- The right pair atom. -/
  atomV : Fin 6
  /-- The outside sharer atom. -/
  atomT : Fin 6
  /-- The pair column has support two. -/
  hcard : (datumTightSupport frame.tightDir
    (frame.basisLabel columnIndex)).card = 2
  /-- The pair atoms are distinct. -/
  hUV : atomU ≠ atomV
  /-- The pair column is alive at the left atom. -/
  hneU : frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0
  /-- The pair column is alive at the right atom. -/
  hneV : frame.tightDir (frame.basisLabel columnIndex) atomV ≠ 0
  /-- The pair column vanishes off the pair. -/
  hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
    frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0
  /-- The sharer is a different column. -/
  hneCol : otherIndex ≠ columnIndex
  /-- The sharer atom is not the left pair atom. -/
  hTU : atomT ≠ atomU
  /-- The sharer atom is not the right pair atom. -/
  hTV : atomT ≠ atomV
  /-- The sharer is alive outside the pair. -/
  hneT : frame.tightDir (frame.basisLabel otherIndex) atomT ≠ 0

/-- The rank-four square matrix: the ones column, the four squared basis
columns, and the pair difference filler. -/
def RankFourOuterData.squareMatrix {crux : SixThreeCrux}
    (data : RankFourOuterData crux) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun atomIndex => Fin.cons 1 (Fin.snoc
    (fun colIndex : Fin 4 =>
      data.frame.tightDir (data.frame.basisLabel colIndex) atomIndex ^ 2)
    ((if atomIndex = data.atomU then (1 : ℝ) else 0)
      - (if atomIndex = data.atomV then 1 else 0)))

/-- The rank-four dual row: the adjugate row of the square matrix. -/
def RankFourOuterData.dualRow {crux : SixThreeCrux}
    (data : RankFourOuterData crux) : Fin 6 → ℝ :=
  data.squareMatrix.adjugate 0

/-- The first column of the rank-four square matrix is ones. -/
theorem RankFourOuterData.squareMatrix_ones {crux : SixThreeCrux}
    (data : RankFourOuterData crux) (atomIndex : Fin 6) :
    data.squareMatrix atomIndex 0 = 1 := by
  simp [RankFourOuterData.squareMatrix]

/-- The middle columns of the rank-four square matrix are the squared
basis columns. -/
theorem RankFourOuterData.squareMatrix_basisColumn {crux : SixThreeCrux}
    (data : RankFourOuterData crux) (colIndex : Fin 4) (atomIndex : Fin 6) :
    data.squareMatrix atomIndex (Fin.succ (Fin.castSucc colIndex))
      = data.frame.tightDir (data.frame.basisLabel colIndex) atomIndex ^ 2 := by
  simp [RankFourOuterData.squareMatrix]

/-- The last column of the rank-four square matrix is the pair
difference filler. -/
theorem RankFourOuterData.squareMatrix_filler {crux : SixThreeCrux}
    (data : RankFourOuterData crux) (atomIndex : Fin 6) :
    data.squareMatrix atomIndex (Fin.succ (Fin.last 4))
      = (if atomIndex = data.atomU then (1 : ℝ) else 0)
        - (if atomIndex = data.atomV then 1 else 0) := by
  show (Fin.cons 1 (Fin.snoc
      (fun colIndex : Fin 4 =>
        data.frame.tightDir (data.frame.basisLabel colIndex) atomIndex ^ 2)
      ((if atomIndex = data.atomU then (1 : ℝ) else 0)
        - (if atomIndex = data.atomV then 1 else 0))) : Fin 6 → ℝ)
      (Fin.succ (Fin.last 4)) = _
  rw [Fin.cons_succ, Fin.snoc_last]

/-- **THE EQUALITY CAPS.**  The rank-four dual row annihilates every
squared basis column. -/
theorem RankFourOuterData.dualRow_annihilates_basis {crux : SixThreeCrux}
    (data : RankFourOuterData crux) (colIndex : Fin 4) :
    ∑ atomIndex : Fin 6, data.dualRow atomIndex
        * data.frame.tightDir (data.frame.basisLabel colIndex) atomIndex ^ 2
      = 0 := by
  have hannih := adjugate_row_annihilates data.squareMatrix
    (Fin.succ_ne_zero (Fin.castSucc colIndex))
  calc ∑ atomIndex : Fin 6, data.dualRow atomIndex
        * data.frame.tightDir (data.frame.basisLabel colIndex) atomIndex ^ 2
      = ∑ atomIndex : Fin 6, data.squareMatrix.adjugate 0 atomIndex
          * data.squareMatrix atomIndex (Fin.succ (Fin.castSucc colIndex)) := by
        refine Finset.sum_congr rfl fun atomIndex _ => ?_
        rw [data.squareMatrix_basisColumn colIndex atomIndex]
        rfl
    _ = 0 := hannih

/-- The filler annihilation: the dual row takes equal values at the two
pair atoms. -/
theorem RankFourOuterData.dualRow_pair_difference {crux : SixThreeCrux}
    (data : RankFourOuterData crux) :
    data.dualRow data.atomU = data.dualRow data.atomV := by
  classical
  have hfill := adjugate_row_annihilates data.squareMatrix
    (Fin.succ_ne_zero (Fin.last 4))
  have hread : ∑ atomIndex : Fin 6, data.squareMatrix.adjugate 0 atomIndex
      * data.squareMatrix atomIndex (Fin.succ (Fin.last 4))
      = data.dualRow data.atomU - data.dualRow data.atomV := by
    calc ∑ atomIndex : Fin 6, data.squareMatrix.adjugate 0 atomIndex
        * data.squareMatrix atomIndex (Fin.succ (Fin.last 4))
        = ∑ atomIndex : Fin 6, (data.dualRow atomIndex
            * (if atomIndex = data.atomU then (1 : ℝ) else 0)
          - data.dualRow atomIndex
            * (if atomIndex = data.atomV then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl fun atomIndex _ => ?_
          rw [data.squareMatrix_filler atomIndex]
          show data.dualRow atomIndex
              * ((if atomIndex = data.atomU then (1 : ℝ) else 0)
                - (if atomIndex = data.atomV then 1 else 0)) = _
          ring
      _ = (∑ atomIndex : Fin 6, data.dualRow atomIndex
            * (if atomIndex = data.atomU then (1 : ℝ) else 0))
          - ∑ atomIndex : Fin 6, data.dualRow atomIndex
            * (if atomIndex = data.atomV then (1 : ℝ) else 0) := by
        rw [Finset.sum_sub_distrib]
      _ = data.dualRow data.atomU - data.dualRow data.atomV := by
          simp only [mul_ite, mul_one, mul_zero]
          rw [Finset.sum_ite_eq' Finset.univ data.atomU data.dualRow,
            Finset.sum_ite_eq' Finset.univ data.atomV data.dualRow]
          simp
  have hdiff : data.dualRow data.atomU - data.dualRow data.atomV = 0 := by
    rw [← hread]
    exact hfill
  exact sub_eq_zero.mp hdiff

/-- **THE OUTSIDE SUPPORT, LEFT.**  The rank-four dual row vanishes at
the left pair atom.  Thus the dual is outside-supported, as the scan
verdict demands. -/
theorem RankFourOuterData.dualRow_atomU_eq_zero {crux : SixThreeCrux}
    (data : RankFourOuterData crux) :
    data.dualRow data.atomU = 0 := by
  have hunit := pair_support_unit_read data.frame.hdata
    (data.frame.hmemAll data.columnIndex) data.hUV data.hsupp
  have henergy := pair_support_energy_read data.hUV data.hsupp data.dualRow
  have hannih := data.dualRow_annihilates_basis data.columnIndex
  have hpair : data.dualRow data.atomU
      * data.frame.tightDir (data.frame.basisLabel data.columnIndex)
          data.atomU ^ 2
    + data.dualRow data.atomV
      * data.frame.tightDir (data.frame.basisLabel data.columnIndex)
          data.atomV ^ 2 = 0 := by
    rw [← henergy]
    exact hannih
  have hdiff : data.dualRow data.atomU - data.dualRow data.atomV = 0 :=
    sub_eq_zero.mpr data.dualRow_pair_difference
  linear_combination hpair
    + data.frame.tightDir (data.frame.basisLabel data.columnIndex)
        data.atomV ^ 2 * hdiff
    - data.dualRow data.atomU * hunit

/-- **THE OUTSIDE SUPPORT, RIGHT.**  The rank-four dual row vanishes at
the right pair atom. -/
theorem RankFourOuterData.dualRow_atomV_eq_zero {crux : SixThreeCrux}
    (data : RankFourOuterData crux) :
    data.dualRow data.atomV = 0 := by
  have hunit := pair_support_unit_read data.frame.hdata
    (data.frame.hmemAll data.columnIndex) data.hUV data.hsupp
  have henergy := pair_support_energy_read data.hUV data.hsupp data.dualRow
  have hannih := data.dualRow_annihilates_basis data.columnIndex
  have hpair : data.dualRow data.atomU
      * data.frame.tightDir (data.frame.basisLabel data.columnIndex)
          data.atomU ^ 2
    + data.dualRow data.atomV
      * data.frame.tightDir (data.frame.basisLabel data.columnIndex)
          data.atomV ^ 2 = 0 := by
    rw [← henergy]
    exact hannih
  have hdiff : data.dualRow data.atomU - data.dualRow data.atomV = 0 :=
    sub_eq_zero.mpr data.dualRow_pair_difference
  linear_combination hpair
    - data.frame.tightDir (data.frame.basisLabel data.columnIndex)
        data.atomU ^ 2 * hdiff
    - data.dualRow data.atomV * hunit

/-- **THE RANK-FOUR EXTRAS RESIDUE.**  Every positive active label
outside the basis caps against the dual row, with the sign of the
determinant.  The product form covers the two orientations at once. -/
def RankFourOuterExtrasCapped : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
    (label : data.frame.activeIndex),
    label ∈ data.frame.activeSet →
    0 < data.frame.reducedWeight label →
    (∀ colIndex : Fin 4, label ≠ data.frame.basisLabel colIndex) →
    (∑ atomIndex : Fin 6, data.dualRow atomIndex
        * data.frame.tightDir label atomIndex ^ 2)
      * data.squareMatrix.det ≤ 0

/-- **THE RANK-FOUR STRATUM RESIDUE.**  The det-zero stratum dies.  On
the stratum the cofactor margin degenerates, and the sign obstruction of
the scan takes over. -/
def RankFourOuterStratumKilled : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux),
    data.squareMatrix.det = 0 → False

/-- **THE RANK-FOUR KILL MODULO THE RESIDUES.**  The capped certificate
collapses the determinant to zero, and the stratum residue kills the
collapsed point. -/
theorem RankFourOuterData.killed_of_residues
    (hextras : RankFourOuterExtrasCapped)
    (hstratum : RankFourOuterStratumKilled)
    {crux : SixThreeCrux} (data : RankFourOuterData crux) : False := by
  classical
  apply hstratum crux data
  apply det_eq_zero_of_capped_certificate data.frame.hdata data.squareMatrix
    (fun atomIndex => data.squareMatrix_ones atomIndex)
  intro label hmem hpos
  by_cases hbasis : ∃ colIndex : Fin 4, label = data.frame.basisLabel colIndex
  · obtain ⟨colIndex, rfl⟩ := hbasis
    have hzero := data.dualRow_annihilates_basis colIndex
    show (∑ atomIndex : Fin 6, data.dualRow atomIndex
        * data.frame.tightDir (data.frame.basisLabel colIndex) atomIndex ^ 2)
      * data.squareMatrix.det ≤ 0
    rw [hzero, zero_mul]
  · push Not at hbasis
    exact hextras crux data label hmem hpos hbasis

/-- **THE RANK-FOUR BRIDGE COMPOSITION.**  The two cofactor residues
close the rank-four support-two closure through the landed refined
bridge. -/
theorem rankFourSupportTwoClosed_of_cofactor_residues
    (hextras : RankFourOuterExtrasCapped)
    (hstratum : RankFourOuterStratumKilled) :
    RankFourSupportTwoClosed := by
  refine rankFourSupportTwoClosed_of_outer_shared_kill ?_
  intro crux frame columnIndex otherIndex atomU atomV atomT hcard hUV hneU
    hneV hsupp hneCol hTU hTV hneT
  exact RankFourOuterData.killed_of_residues hextras hstratum
    ⟨frame, columnIndex, otherIndex, atomU, atomV, atomT, hcard, hUV, hneU,
      hneV, hsupp, hneCol, hTU, hTV, hneT⟩

/-! ## Layer 3 — the rank-five cofactor reduction -/

/-- **THE RANK-FIVE OUTER DATUM.**  The reified killOuter tuple of the
rank-five bridge. -/
structure RankFiveOuterData (crux : SixThreeCrux) where
  /-- The rank-five frame. -/
  frame : RankFiveFrame crux
  /-- The pair column index. -/
  columnIndex : Fin 5
  /-- The outer sharer index. -/
  otherIndex : Fin 5
  /-- The left pair atom. -/
  atomU : Fin 6
  /-- The right pair atom. -/
  atomV : Fin 6
  /-- The outside sharer atom. -/
  atomT : Fin 6
  /-- The pair column has support two. -/
  hcard : (datumTightSupport frame.tightDir
    (frame.basisLabel columnIndex)).card = 2
  /-- The pair atoms are distinct. -/
  hUV : atomU ≠ atomV
  /-- The pair column is alive at the left atom. -/
  hneU : frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0
  /-- The pair column is alive at the right atom. -/
  hneV : frame.tightDir (frame.basisLabel columnIndex) atomV ≠ 0
  /-- The pair column vanishes off the pair. -/
  hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
    frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0
  /-- The sharer is a different column. -/
  hneCol : otherIndex ≠ columnIndex
  /-- The sharer atom is not the left pair atom. -/
  hTU : atomT ≠ atomU
  /-- The sharer atom is not the right pair atom. -/
  hTV : atomT ≠ atomV
  /-- The sharer is alive outside the pair. -/
  hneT : frame.tightDir (frame.basisLabel otherIndex) atomT ≠ 0

/-- The rank-five square matrix: the ones column and the five squared
basis columns.  No filler column remains, thus the dual is
full-support, as the scan verdict demands. -/
def RankFiveOuterData.squareMatrix {crux : SixThreeCrux}
    (data : RankFiveOuterData crux) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun atomIndex => Fin.cons 1 fun colIndex : Fin 5 =>
    data.frame.tightDir (data.frame.basisLabel colIndex) atomIndex ^ 2

/-- The rank-five dual row: the adjugate row of the square matrix. -/
def RankFiveOuterData.dualRow {crux : SixThreeCrux}
    (data : RankFiveOuterData crux) : Fin 6 → ℝ :=
  data.squareMatrix.adjugate 0

/-- The first column of the rank-five square matrix is ones. -/
theorem RankFiveOuterData.squareMatrix_ones {crux : SixThreeCrux}
    (data : RankFiveOuterData crux) (atomIndex : Fin 6) :
    data.squareMatrix atomIndex 0 = 1 := by
  simp [RankFiveOuterData.squareMatrix]

/-- The other columns of the rank-five square matrix are the squared
basis columns. -/
theorem RankFiveOuterData.squareMatrix_basisColumn {crux : SixThreeCrux}
    (data : RankFiveOuterData crux) (colIndex : Fin 5) (atomIndex : Fin 6) :
    data.squareMatrix atomIndex (Fin.succ colIndex)
      = data.frame.tightDir (data.frame.basisLabel colIndex) atomIndex ^ 2 := by
  simp [RankFiveOuterData.squareMatrix]

/-- **THE RANK-FIVE EQUALITY CAPS.**  The rank-five dual row annihilates
every squared basis column, the pair column included. -/
theorem RankFiveOuterData.dualRow_annihilates_basis {crux : SixThreeCrux}
    (data : RankFiveOuterData crux) (colIndex : Fin 5) :
    ∑ atomIndex : Fin 6, data.dualRow atomIndex
        * data.frame.tightDir (data.frame.basisLabel colIndex) atomIndex ^ 2
      = 0 := by
  have hannih := adjugate_row_annihilates data.squareMatrix
    (Fin.succ_ne_zero colIndex)
  calc ∑ atomIndex : Fin 6, data.dualRow atomIndex
        * data.frame.tightDir (data.frame.basisLabel colIndex) atomIndex ^ 2
      = ∑ atomIndex : Fin 6, data.squareMatrix.adjugate 0 atomIndex
          * data.squareMatrix atomIndex (Fin.succ colIndex) := by
        refine Finset.sum_congr rfl fun atomIndex _ => ?_
        rw [data.squareMatrix_basisColumn colIndex atomIndex]
        rfl
    _ = 0 := hannih

/-- **THE RANK-FIVE EXTRAS RESIDUE.**  Every positive active label
outside the basis caps against the dual row, with the sign of the
determinant. -/
def RankFiveOuterExtrasCapped : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFiveOuterData crux)
    (label : data.frame.activeIndex),
    label ∈ data.frame.activeSet →
    0 < data.frame.reducedWeight label →
    (∀ colIndex : Fin 5, label ≠ data.frame.basisLabel colIndex) →
    (∑ atomIndex : Fin 6, data.dualRow atomIndex
        * data.frame.tightDir label atomIndex ^ 2)
      * data.squareMatrix.det ≤ 0

/-- **THE RANK-FIVE STRATUM RESIDUE.**  The det-zero stratum dies. -/
def RankFiveOuterStratumKilled : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFiveOuterData crux),
    data.squareMatrix.det = 0 → False

/-- **THE RANK-FIVE KILL MODULO THE RESIDUES.** -/
theorem RankFiveOuterData.killed_of_residues
    (hextras : RankFiveOuterExtrasCapped)
    (hstratum : RankFiveOuterStratumKilled)
    {crux : SixThreeCrux} (data : RankFiveOuterData crux) : False := by
  classical
  apply hstratum crux data
  apply det_eq_zero_of_capped_certificate data.frame.hdata data.squareMatrix
    (fun atomIndex => data.squareMatrix_ones atomIndex)
  intro label hmem hpos
  by_cases hbasis : ∃ colIndex : Fin 5, label = data.frame.basisLabel colIndex
  · obtain ⟨colIndex, rfl⟩ := hbasis
    have hzero := data.dualRow_annihilates_basis colIndex
    show (∑ atomIndex : Fin 6, data.dualRow atomIndex
        * data.frame.tightDir (data.frame.basisLabel colIndex) atomIndex ^ 2)
      * data.squareMatrix.det ≤ 0
    rw [hzero, zero_mul]
  · push Not at hbasis
    exact hextras crux data label hmem hpos hbasis

/-- **THE RANK-FIVE BRIDGE COMPOSITION.**  The two cofactor residues
close the rank-five support-two closure through the landed refined
bridge. -/
theorem rankFiveSupportTwoClosed_of_cofactor_residues
    (hextras : RankFiveOuterExtrasCapped)
    (hstratum : RankFiveOuterStratumKilled) :
    RankFiveSupportTwoClosed := by
  refine rankFiveSupportTwoClosed_of_outer_shared_kill ?_
  intro crux frame columnIndex otherIndex atomU atomV atomT hcard hUV hneU
    hneV hsupp hneCol hTU hTV hneT
  exact RankFiveOuterData.killed_of_residues hextras hstratum
    ⟨frame, columnIndex, otherIndex, atomU, atomV, atomT, hcard, hUV, hneU,
      hneV, hsupp, hneCol, hTU, hTV, hneT⟩

end Gtz
