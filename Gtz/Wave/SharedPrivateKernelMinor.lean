import Gtz.Wave.SharedPrivateKernelGram
import Gtz.Wave.OuterParallelFold

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The kernel-minor budget — the pair minors close the trace-three deficit

The refined budget counts corner traces.  At trace three it leaves a gap
of one plus six times the chart value, and that gap is not a
perturbation of the caps.  This module replaces the corner traces by the
two-by-two minors of the kernel projector, and the gap closes.

The kernel projector.  The complement of the conjugated coefficient
matrix is a symmetric idempotent whose trace is the basis count minus
the coefficient trace.  Its columns are fixed vectors, and its entries
are the products of those columns.  Thus each entry pair carries a
minor, the minor is nonnegative, and the total of the minors is the
trace times the trace minus one.

The corner reading.  A carrier read of the coefficient matrix at the
shifted weight is a carrier read of the kernel projector at one minus
the shifted weight.  The read vector is an eigenvector of the carrier
corner.  At kernel trace two every three-slot corner is singular,
because three fixed vectors with an invertible Gram would count above
the trace.  Thus the characteristic polynomial of the corner has degree
two, and the minor sum of the corner is the read times the corner trace
minus the read.

The budget.  The double count over the atoms multiplies each minor by
the number of atoms that carry the two slots.  When every slot pair
shares an atom, that count is at least one, thus the weighted total is
at least the plain total.  The corner identity prices the same weighted
total by the read defects, and the defect total is the shifted-weight
total.  A negative chart value keeps the shifted-weight total below
one, and the two sides cross.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.kernelMinor` with `Gtz.kernelMinor_nonneg`,
  `Gtz.kernelMinor_row_sum`, `Gtz.kernelMinor_total` — the minor
  calculus of a symmetric idempotent.
* `Gtz.kernelColumn_dot` — the columns of an idempotent read its
  entries.
* `Gtz.det_two_eq_zero_of_kernel`, `Gtz.det_three_eq_zero_of_kernel` —
  the adjugate laws of a small singular system.
* `Gtz.corner_det_eq_zero_of_trace_two` — **THE SINGULAR CORNER.**
* `Gtz.kernelMinor_corner_one`, `Gtz.kernelMinor_corner_two`,
  `Gtz.kernelMinor_corner_three` — **THE CORNER MINOR IDENTITY.**
* `Gtz.false_of_kernelMinor_budget` — **THE KERNEL-MINOR KILL.**
* `Gtz.profileDefect` with `Gtz.fifteen_le_sum_of_deficit` and
  `Gtz.multiplicity_le_three_of_deficit` — the deficit profile: the
  support total is at least fifteen, thus the basis count is five or
  six, and at five every carrier is at most three slots wide.
* `Gtz.SharedPrivateData.false_of_deficit_five` — **THE DEFICIT KILL AT
  BASIS COUNT FIVE.**
* `Gtz.SharedPrivateDeficitSixClosed`,
  `Gtz.SharedPrivateDeficitSplitClosed` — the two deficit residues.
* `Gtz.sharedPrivateDeficitClosed_of_residues` — the deficit dispatch.
* `Gtz.SharedPrivateCircuitClosed` with
  `Gtz.sharedPrivateExtrasClosed_of_circuit` — the extras fold.

## Vacuity

The matrix statements are unconditional.  The data-facing statements
quantify over shared-private data, and no datum exists if
`Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the minor calculus of a symmetric idempotent -/

/-- The two-by-two principal minor of a matrix at a slot pair. -/
def kernelMinor {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (rowSlot colSlot : Fin n) : ℝ :=
  K rowSlot rowSlot * K colSlot colSlot - K rowSlot colSlot ^ 2

/-- The column of a symmetric idempotent at a slot. -/
def kernelColumn {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (colSlot : Fin n) :
    Fin n → ℝ :=
  fun rowIndex => K rowIndex colSlot

/-- A column of an idempotent is a fixed vector. -/
theorem kernelColumn_fixed {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hidem : K * K = K) (colSlot : Fin n) :
    K *ᵥ kernelColumn K colSlot = kernelColumn K colSlot := by
  funext rowIndex
  have h := congrFun (congrFun hidem rowIndex) colSlot
  rw [Matrix.mul_apply] at h
  exact h

/-- **THE COLUMN READING.**  The entries of a symmetric idempotent are
the products of its columns. -/
theorem kernelColumn_dot {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Kᵀ = K) (hidem : K * K = K) (rowSlot colSlot : Fin n) :
    kernelColumn K rowSlot ⬝ᵥ kernelColumn K colSlot = K rowSlot colSlot := by
  have hentry := congrFun (congrFun hidem rowSlot) colSlot
  rw [Matrix.mul_apply] at hentry
  rw [dotProduct, ← hentry]
  refine Finset.sum_congr rfl fun midSlot _ => ?_
  have hs : K midSlot rowSlot = K rowSlot midSlot := by
    have := congrFun (congrFun hsymm rowSlot) midSlot
    rwa [Matrix.transpose_apply] at this
  show K midSlot rowSlot * K midSlot colSlot
    = K rowSlot midSlot * K midSlot colSlot
  rw [hs]

/-- The minor is symmetric in its two slots. -/
theorem kernelMinor_comm {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Kᵀ = K) (rowSlot colSlot : Fin n) :
    kernelMinor K rowSlot colSlot = kernelMinor K colSlot rowSlot := by
  have hs : K colSlot rowSlot = K rowSlot colSlot := by
    have := congrFun (congrFun hsymm rowSlot) colSlot
    rwa [Matrix.transpose_apply] at this
  simp only [kernelMinor, hs]
  ring

/-- The minor at a repeated slot vanishes. -/
theorem kernelMinor_self {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (slot : Fin n) : kernelMinor K slot slot = 0 := by
  simp only [kernelMinor]
  ring

/-- **THE MINOR FLOOR.**  Every two-by-two principal minor of a
symmetric idempotent is nonnegative: the entries are column products,
and the Cauchy-Schwarz inequality caps the cross product. -/
theorem kernelMinor_nonneg {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Kᵀ = K) (hidem : K * K = K) (rowSlot colSlot : Fin n) :
    0 ≤ kernelMinor K rowSlot colSlot := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun midSlot => kernelColumn K rowSlot midSlot)
    (fun midSlot => kernelColumn K colSlot midSlot)
  have hrow : ∑ midSlot, kernelColumn K rowSlot midSlot
      * kernelColumn K rowSlot midSlot = K rowSlot rowSlot :=
    kernelColumn_dot hsymm hidem rowSlot rowSlot
  have hcol : ∑ midSlot, kernelColumn K colSlot midSlot
      * kernelColumn K colSlot midSlot = K colSlot colSlot :=
    kernelColumn_dot hsymm hidem colSlot colSlot
  have hcross : ∑ midSlot, kernelColumn K rowSlot midSlot
      * kernelColumn K colSlot midSlot = K rowSlot colSlot :=
    kernelColumn_dot hsymm hidem rowSlot colSlot
  have hsq : ∀ midSlot : Fin n, kernelColumn K rowSlot midSlot ^ 2
      = kernelColumn K rowSlot midSlot * kernelColumn K rowSlot midSlot :=
    fun _ => sq _
  have hsq' : ∀ midSlot : Fin n, kernelColumn K colSlot midSlot ^ 2
      = kernelColumn K colSlot midSlot * kernelColumn K colSlot midSlot :=
    fun _ => sq _
  rw [hcross, Finset.sum_congr rfl fun midSlot _ => hsq midSlot,
    Finset.sum_congr rfl fun midSlot _ => hsq' midSlot, hrow, hcol] at hcs
  simp only [kernelMinor]
  linarith

/-- **THE ROW TOTAL.**  The minors along one slot total the diagonal
entry times the trace minus one. -/
theorem kernelMinor_row_sum {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Kᵀ = K) (hidem : K * K = K) (rowSlot : Fin n) :
    ∑ colSlot, kernelMinor K rowSlot colSlot
      = K rowSlot rowSlot * (Matrix.trace K - 1) := by
  have hdiag : ∑ colSlot, K rowSlot colSlot ^ 2 = K rowSlot rowSlot := by
    have h := kernelColumn_dot hsymm hidem rowSlot rowSlot
    rw [dotProduct] at h
    rw [← h]
    refine Finset.sum_congr rfl fun midSlot _ => ?_
    have hs : K midSlot rowSlot = K rowSlot midSlot := by
      have := congrFun (congrFun hsymm rowSlot) midSlot
      rwa [Matrix.transpose_apply] at this
    show K rowSlot midSlot ^ 2 = K midSlot rowSlot * K midSlot rowSlot
    rw [hs, sq]
  have htr : Matrix.trace K = ∑ colSlot, K colSlot colSlot := rfl
  simp only [kernelMinor]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hdiag, ← htr]
  ring

/-- **THE MINOR TOTAL.**  The full double total of the minors of a
symmetric idempotent is the trace times the trace minus one. -/
theorem kernelMinor_total {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Kᵀ = K) (hidem : K * K = K) :
    ∑ rowSlot, ∑ colSlot, kernelMinor K rowSlot colSlot
      = Matrix.trace K * (Matrix.trace K - 1) := by
  have htr : Matrix.trace K = ∑ colSlot, K colSlot colSlot := rfl
  rw [Finset.sum_congr rfl fun rowSlot _ => kernelMinor_row_sum hsymm hidem rowSlot,
    ← Finset.sum_mul, ← htr]

/-! ## Layer 2 — the corner reading and the singular corner -/

/-- The kernel read: a carrier read of the coefficient matrix at the
shifted weight is a carrier read of the complement at one minus it. -/
theorem kernel_corner_read {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    {vec : Fin n → ℝ} {readVal : ℝ} {slot : Fin n}
    (hread : (S *ᵥ vec) slot = readVal * vec slot) :
    (((1 : Matrix (Fin n) (Fin n) ℝ) - S) *ᵥ vec) slot
      = (1 - readVal) * vec slot := by
  rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec, hread]
  ring

/-- A two-by-two system with a nonzero solution has a zero
determinant. -/
theorem det_two_eq_zero_of_kernel {entryOneOne entryOneTwo entryTwoOne entryTwoTwo
    coeffOne coeffTwo : ℝ} (hnz : coeffOne ≠ 0 ∨ coeffTwo ≠ 0)
    (hrowOne : entryOneOne * coeffOne + entryOneTwo * coeffTwo = 0)
    (hrowTwo : entryTwoOne * coeffOne + entryTwoTwo * coeffTwo = 0) :
    entryOneOne * entryTwoTwo - entryOneTwo * entryTwoOne = 0 := by
  rcases hnz with hone | htwo
  · refine mul_right_cancel₀ hone ?_
    rw [zero_mul]
    linear_combination entryTwoTwo * hrowOne - entryOneTwo * hrowTwo
  · refine mul_right_cancel₀ htwo ?_
    rw [zero_mul]
    linear_combination entryOneOne * hrowTwo - entryTwoOne * hrowOne

/-- A three-by-three system with a nonzero solution has a zero
determinant.  The adjugate combination of the three rows prices the
determinant against each coordinate. -/
theorem det_three_eq_zero_of_kernel {a11 a12 a13 a21 a22 a23 a31 a32 a33
    coeffOne coeffTwo coeffThree : ℝ}
    (hnz : coeffOne ≠ 0 ∨ coeffTwo ≠ 0 ∨ coeffThree ≠ 0)
    (hrowOne : a11 * coeffOne + a12 * coeffTwo + a13 * coeffThree = 0)
    (hrowTwo : a21 * coeffOne + a22 * coeffTwo + a23 * coeffThree = 0)
    (hrowThree : a31 * coeffOne + a32 * coeffTwo + a33 * coeffThree = 0) :
    a11 * (a22 * a33 - a23 * a32) - a12 * (a21 * a33 - a23 * a31)
      + a13 * (a21 * a32 - a22 * a31) = 0 := by
  rcases hnz with hone | htwo | hthree
  · refine mul_right_cancel₀ hone ?_
    rw [zero_mul]
    linear_combination (a22 * a33 - a23 * a32) * hrowOne
      - (a12 * a33 - a13 * a32) * hrowTwo + (a12 * a23 - a13 * a22) * hrowThree
  · refine mul_right_cancel₀ htwo ?_
    rw [zero_mul]
    linear_combination (-(a21 * a33) + a23 * a31) * hrowOne
      + (a11 * a33 - a13 * a31) * hrowTwo + (-(a11 * a23) + a13 * a21) * hrowThree
  · refine mul_right_cancel₀ hthree ?_
    rw [zero_mul]
    linear_combination (a21 * a32 - a22 * a31) * hrowOne
      + (-(a11 * a32) + a12 * a31) * hrowTwo + (a11 * a22 - a12 * a21) * hrowThree

/-- **THE SINGULAR CORNER.**  At kernel trace two every three-slot
corner of a symmetric idempotent is singular.  Three fixed columns with
an invertible Gram would count above the trace. -/
theorem corner_det_eq_zero_of_trace_two {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Kᵀ = K) (hidem : K * K = K) (htrace : Matrix.trace K = 2)
    (first second third : Fin n) :
    K first first * (K second second * K third third - K second third * K third second)
        - K first second * (K second first * K third third - K second third * K third first)
        + K first third * (K second first * K third second - K second second * K third first)
      = 0 := by
  classical
  set slotOf : Fin 3 → Fin n := ![first, second, third] with hslotOf
  set family : Fin 3 → Fin n → ℝ :=
    fun index => kernelColumn K (slotOf index) with hfamily
  have hfix : ∀ index : Fin 3, K *ᵥ family index = family index :=
    fun index => kernelColumn_fixed hidem _
  set gram : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of fun rowIndex colIndex => family rowIndex ⬝ᵥ family colIndex
    with hgramDef
  have hgramEntry : ∀ rowIndex colIndex : Fin 3,
      gram rowIndex colIndex = K (slotOf rowIndex) (slotOf colIndex) :=
    fun rowIndex colIndex => kernelColumn_dot hsymm hidem _ _
  have hkerFail : ¬ (∀ coeffVec : Fin 3 → ℝ, gram *ᵥ coeffVec = 0 → coeffVec = 0) := by
    intro hkerFree
    have hcount := trace_floor_of_fixed_family hsymm hidem family hfix hkerFree
    rw [htrace] at hcount
    norm_num at hcount
  push Not at hkerFail
  obtain ⟨coeffVec, hzero, hne⟩ := hkerFail
  have hcoord : ∀ rowIndex : Fin 3,
      gram rowIndex 0 * coeffVec 0 + gram rowIndex 1 * coeffVec 1
        + gram rowIndex 2 * coeffVec 2 = 0 := by
    intro rowIndex
    have hentry : (gram *ᵥ coeffVec) rowIndex
        = gram rowIndex 0 * coeffVec 0 + gram rowIndex 1 * coeffVec 1
          + gram rowIndex 2 * coeffVec 2 := by
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [← hentry, hzero]
    rfl
  have hnzCoord : coeffVec 0 ≠ 0 ∨ coeffVec 1 ≠ 0 ∨ coeffVec 2 ≠ 0 := by
    by_contra hall
    push Not at hall
    refine hne (funext fun index => ?_)
    fin_cases index
    · exact hall.1
    · exact hall.2.1
    · exact hall.2.2
  have hslotZero : slotOf 0 = first := rfl
  have hslotOne : slotOf 1 = second := rfl
  have hslotTwo : slotOf 2 = third := rfl
  have hkey := det_three_eq_zero_of_kernel hnzCoord (hcoord 0) (hcoord 1) (hcoord 2)
  simp only [hgramEntry, hslotZero, hslotOne, hslotTwo] at hkey
  exact hkey

/-! ## Layer 3 — the corner minor identity -/

/-- The corner minor total of a one-slot carrier. -/
theorem kernelMinor_corner_one {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    {vec : Fin n → ℝ} {readVal : ℝ} {slot : Fin n}
    (hsupp : ∀ other, other ≠ slot → vec other = 0)
    (hnz : vec slot ≠ 0)
    (hread : (K *ᵥ vec) slot = readVal * vec slot) :
    ∑ rowSlot ∈ ({slot} : Finset (Fin n)),
        ∑ colSlot ∈ ({slot} : Finset (Fin n)), kernelMinor K rowSlot colSlot
      = 2 * readVal
        * ((∑ rowSlot ∈ ({slot} : Finset (Fin n)), K rowSlot rowSlot)
            - readVal) := by
  have hcollapse : (K *ᵥ vec) slot = K slot slot * vec slot := by
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single slot (fun other _ hother => by
      rw [hsupp other hother, mul_zero]) (fun hnot => absurd (Finset.mem_univ _) hnot)]
  have hdiag : K slot slot = readVal := by
    have := hread
    rw [hcollapse] at this
    exact mul_right_cancel₀ hnz this
  rw [Finset.sum_singleton, Finset.sum_singleton, Finset.sum_singleton,
    kernelMinor_self, hdiag]
  ring

/-- The corner minor total of a two-slot carrier: the two-by-two
characteristic polynomial prices it. -/
theorem kernelMinor_corner_two {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Kᵀ = K) {vec : Fin n → ℝ} {readVal : ℝ} {first second : Fin n}
    (hne : first ≠ second)
    (hsupp : ∀ other, other ≠ first → other ≠ second → vec other = 0)
    (hnz : vec first ≠ 0 ∨ vec second ≠ 0)
    (hreadOne : (K *ᵥ vec) first = readVal * vec first)
    (hreadTwo : (K *ᵥ vec) second = readVal * vec second) :
    ∑ rowSlot ∈ ({first, second} : Finset (Fin n)),
        ∑ colSlot ∈ ({first, second} : Finset (Fin n)),
          kernelMinor K rowSlot colSlot
      = 2 * readVal
        * ((∑ rowSlot ∈ ({first, second} : Finset (Fin n)), K rowSlot rowSlot)
            - readVal) := by
  classical
  have hsym : K second first = K first second := by
    have := congrFun (congrFun hsymm first) second
    rwa [Matrix.transpose_apply] at this
  have hcollapse : ∀ rowSlot : Fin n, (K *ᵥ vec) rowSlot
      = K rowSlot first * vec first + K rowSlot second * vec second :=
    fun rowSlot => pair_mulVec_apply K hne hsupp rowSlot
  rw [hcollapse] at hreadOne hreadTwo
  have hdet := det_two_eq_zero_of_kernel (entryOneOne := K first first - readVal)
    (entryOneTwo := K first second) (entryTwoOne := K second first)
    (entryTwoTwo := K second second - readVal) hnz (by linarith) (by linarith)
  rw [hsym] at hdet
  have hpair : ∀ probe : Fin n → ℝ,
      ∑ slot ∈ ({first, second} : Finset (Fin n)), probe slot
        = probe first + probe second := fun probe => Finset.sum_pair hne
  simp only [hpair, kernelMinor, hsym]
  linear_combination (2 : ℝ) * hdet

/-- **THE CORNER MINOR IDENTITY, THREE SLOTS.**  At kernel trace two
the corner is singular, thus the characteristic polynomial has degree
two and the corner minor total is the read times the corner defect. -/
theorem kernelMinor_corner_three {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Kᵀ = K) (hidem : K * K = K) (htrace : Matrix.trace K = 2)
    {vec : Fin n → ℝ} {readVal : ℝ} {first second third : Fin n}
    (hreadPos : readVal ≠ 0)
    (hone : first ≠ second) (htwo : first ≠ third) (hthree : second ≠ third)
    (hsupp : ∀ other, other ≠ first → other ≠ second → other ≠ third →
      vec other = 0)
    (hnz : vec first ≠ 0 ∨ vec second ≠ 0 ∨ vec third ≠ 0)
    (hreadOne : (K *ᵥ vec) first = readVal * vec first)
    (hreadTwo : (K *ᵥ vec) second = readVal * vec second)
    (hreadThree : (K *ᵥ vec) third = readVal * vec third) :
    ∑ rowSlot ∈ ({first, second, third} : Finset (Fin n)),
        ∑ colSlot ∈ ({first, second, third} : Finset (Fin n)),
          kernelMinor K rowSlot colSlot
      = 2 * readVal
        * ((∑ rowSlot ∈ ({first, second, third} : Finset (Fin n)),
              K rowSlot rowSlot) - readVal) := by
  classical
  have hsymOne : K second first = K first second := by
    have := congrFun (congrFun hsymm first) second
    rwa [Matrix.transpose_apply] at this
  have hsymTwo : K third first = K first third := by
    have := congrFun (congrFun hsymm first) third
    rwa [Matrix.transpose_apply] at this
  have hsymThree : K third second = K second third := by
    have := congrFun (congrFun hsymm second) third
    rwa [Matrix.transpose_apply] at this
  -- the read collapses to the three carrier slots
  have hcollapse : ∀ rowSlot : Fin n, (K *ᵥ vec) rowSlot
      = K rowSlot first * vec first + K rowSlot second * vec second
        + K rowSlot third * vec third := by
    intro rowSlot
    rw [Matrix.mulVec, dotProduct]
    have hrestrict : ∑ slot, K rowSlot slot * vec slot
        = ∑ slot ∈ ({first, second, third} : Finset (Fin n)),
            K rowSlot slot * vec slot := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro slot _ hnot
      have h1 : slot ≠ first := fun h => hnot (h ▸ Finset.mem_insert_self _ _)
      have h2 : slot ≠ second := fun h =>
        hnot (h ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have h3 : slot ≠ third := fun h =>
        hnot (h ▸ Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      rw [hsupp slot h1 h2 h3, mul_zero]
    rw [hrestrict, Finset.sum_insert (by simp [hone, htwo]),
      Finset.sum_insert (by simp [hthree]), Finset.sum_singleton]
    ring
  rw [hcollapse] at hreadOne hreadTwo hreadThree
  -- the shifted corner is singular
  have hdetShift := det_three_eq_zero_of_kernel
    (a11 := K first first - readVal) (a12 := K first second) (a13 := K first third)
    (a21 := K second first) (a22 := K second second - readVal)
    (a23 := K second third) (a31 := K third first) (a32 := K third second)
    (a33 := K third third - readVal) hnz (by linarith) (by linarith) (by linarith)
  have hdetPlain := corner_det_eq_zero_of_trace_two hsymm hidem htrace
    first second third
  rw [hsymOne, hsymTwo, hsymThree] at hdetShift hdetPlain
  -- the corner minor total
  have htriple : ∀ probe : Fin n → ℝ,
      ∑ slot ∈ ({first, second, third} : Finset (Fin n)), probe slot
        = probe first + probe second + probe third := by
    intro probe
    rw [Finset.sum_insert (by simp [hone, htwo]), Finset.sum_pair hthree]
    ring
  simp only [htriple, kernelMinor, hsymOne, hsymTwo, hsymThree]
  refine mul_left_cancel₀ hreadPos ?_
  linear_combination (2 : ℝ) * hdetPlain - (2 : ℝ) * hdetShift

/-! ## Layer 4 — the kernel-minor kill -/

/-- **THE KERNEL-MINOR KILL.**  A symmetric idempotent of trace two on
the slots, with six carriers of at most three slots, slot incidence
three, a nonvanishing carrier read at every atom, reads in the unit
window, every slot pair sharing an atom, and a read total above five,
does not exist. -/
theorem false_of_kernelMinor_budget {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Kᵀ = K) (hidem : K * K = K) (htrace : Matrix.trace K = 2)
    (car : Fin 6 → Finset (Fin n)) (readVecs : Fin 6 → Fin n → ℝ)
    (readVal : Fin 6 → ℝ)
    (hcard : ∀ atomIndex, (car atomIndex).card ≤ 3)
    (hinc : ∀ slot : Fin n,
      (Finset.univ.filter fun atomIndex => slot ∈ car atomIndex).card = 3)
    (hsupp : ∀ atomIndex, ∀ slot ∉ car atomIndex, readVecs atomIndex slot = 0)
    (hnz : ∀ atomIndex, ∃ slot ∈ car atomIndex, readVecs atomIndex slot ≠ 0)
    (hread : ∀ atomIndex, ∀ slot ∈ car atomIndex,
      (K *ᵥ readVecs atomIndex) slot = readVal atomIndex * readVecs atomIndex slot)
    (hpos : ∀ atomIndex, 0 < readVal atomIndex)
    (hcap : ∀ atomIndex, readVal atomIndex ≤ 1)
    (hco : ∀ rowSlot colSlot : Fin n, rowSlot ≠ colSlot →
      ∃ atomIndex, rowSlot ∈ car atomIndex ∧ colSlot ∈ car atomIndex)
    (hsum : 5 < ∑ atomIndex, readVal atomIndex) :
    False := by
  classical
  -- the corner identity at every atom
  have hcorner : ∀ atomIndex : Fin 6,
      ∑ rowSlot ∈ car atomIndex, ∑ colSlot ∈ car atomIndex,
          kernelMinor K rowSlot colSlot
        = 2 * readVal atomIndex
          * ((∑ rowSlot ∈ car atomIndex, K rowSlot rowSlot)
              - readVal atomIndex) := by
    intro atomIndex
    obtain ⟨witnessSlot, hwitnessMem, hwitnessNe⟩ := hnz atomIndex
    have hcardPos : 0 < (car atomIndex).card :=
      Finset.card_pos.mpr ⟨witnessSlot, hwitnessMem⟩
    have hcardLe := hcard atomIndex
    have hcases : (car atomIndex).card = 1 ∨ (car atomIndex).card = 2
        ∨ (car atomIndex).card = 3 := by omega
    rcases hcases with hcardVal | hcardVal | hcardVal
    · obtain ⟨slot, hset⟩ := Finset.card_eq_one.mp hcardVal
      have hsuppOne : ∀ other, other ≠ slot → readVecs atomIndex other = 0 := by
        intro other hother
        exact hsupp atomIndex other (by rw [hset]; simpa using hother)
      have hslotMem : slot ∈ car atomIndex := by rw [hset]; exact Finset.mem_singleton_self _
      have hslotNz : readVecs atomIndex slot ≠ 0 := by
        have : witnessSlot = slot := by
          rw [hset] at hwitnessMem
          exact Finset.mem_singleton.mp hwitnessMem
        rwa [this] at hwitnessNe
      rw [hset]
      exact kernelMinor_corner_one hsuppOne hslotNz (hread atomIndex slot hslotMem)
    · obtain ⟨first, second, hne, hset⟩ := Finset.card_eq_two.mp hcardVal
      have hsuppTwo : ∀ other, other ≠ first → other ≠ second →
          readVecs atomIndex other = 0 := by
        intro other honeNe htwoNe
        refine hsupp atomIndex other ?_
        rw [hset]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨honeNe, htwoNe⟩
      have hfirstMem : first ∈ car atomIndex := by
        rw [hset]; exact Finset.mem_insert_self _ _
      have hsecondMem : second ∈ car atomIndex := by
        rw [hset]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hnzTwo : readVecs atomIndex first ≠ 0 ∨ readVecs atomIndex second ≠ 0 := by
        rw [hset] at hwitnessMem
        rcases Finset.mem_insert.mp hwitnessMem with rfl | hmem
        · exact Or.inl hwitnessNe
        · exact Or.inr (by rwa [Finset.mem_singleton.mp hmem] at hwitnessNe)
      rw [hset]
      exact kernelMinor_corner_two hsymm hne hsuppTwo hnzTwo
        (hread atomIndex first hfirstMem) (hread atomIndex second hsecondMem)
    · obtain ⟨first, second, third, hone, htwo, hthree, hset⟩ :=
        Finset.card_eq_three.mp hcardVal
      have hsuppThree : ∀ other, other ≠ first → other ≠ second → other ≠ third →
          readVecs atomIndex other = 0 := by
        intro other honeNe htwoNe hthreeNe
        refine hsupp atomIndex other ?_
        rw [hset]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨honeNe, htwoNe, hthreeNe⟩
      have hfirstMem : first ∈ car atomIndex := by
        rw [hset]; exact Finset.mem_insert_self _ _
      have hsecondMem : second ∈ car atomIndex := by
        rw [hset]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have hthirdMem : third ∈ car atomIndex := by
        rw [hset]
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hnzThree : readVecs atomIndex first ≠ 0 ∨ readVecs atomIndex second ≠ 0
          ∨ readVecs atomIndex third ≠ 0 := by
        rw [hset] at hwitnessMem
        rcases Finset.mem_insert.mp hwitnessMem with rfl | hmem
        · exact Or.inl hwitnessNe
        · rcases Finset.mem_insert.mp hmem with rfl | hlast
          · exact Or.inr (Or.inl hwitnessNe)
          · exact Or.inr (Or.inr (by rwa [Finset.mem_singleton.mp hlast] at hwitnessNe))
      rw [hset]
      exact kernelMinor_corner_three hsymm hidem htrace (hpos atomIndex).ne'
        hone htwo hthree hsuppThree hnzThree (hread atomIndex first hfirstMem)
        (hread atomIndex second hsecondMem) (hread atomIndex third hthirdMem)
  -- the incidence total of the carrier diagonals
  have hexpand : ∀ (atomIndex : Fin 6) (probe : Fin n → ℝ),
      ∑ rowSlot ∈ car atomIndex, probe rowSlot
        = ∑ rowSlot : Fin n, if rowSlot ∈ car atomIndex then probe rowSlot else 0 := by
    intro atomIndex probe
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hdiagTotal : ∑ atomIndex : Fin 6, ∑ rowSlot ∈ car atomIndex, K rowSlot rowSlot
      = 3 * Matrix.trace K := by
    rw [Finset.sum_congr rfl fun atomIndex _ => hexpand atomIndex _, Finset.sum_comm]
    have hcount : ∀ rowSlot : Fin n,
        ∑ atomIndex : Fin 6, (if rowSlot ∈ car atomIndex then K rowSlot rowSlot else 0)
          = 3 * K rowSlot rowSlot := by
      intro rowSlot
      rw [← Finset.sum_filter, Finset.sum_const, hinc rowSlot, nsmul_eq_mul]
      norm_num
    rw [Finset.sum_congr rfl fun rowSlot _ => hcount rowSlot, ← Finset.mul_sum]
    rfl
  -- the weighted minor total dominates the plain minor total
  have hminorTotal : ∑ rowSlot : Fin n, ∑ colSlot : Fin n,
      kernelMinor K rowSlot colSlot = 2 := by
    rw [kernelMinor_total hsymm hidem, htrace]
    norm_num
  have hweight : ∑ rowSlot : Fin n, ∑ colSlot : Fin n,
      kernelMinor K rowSlot colSlot
      ≤ ∑ atomIndex : Fin 6, ∑ rowSlot ∈ car atomIndex,
          ∑ colSlot ∈ car atomIndex, kernelMinor K rowSlot colSlot := by
    set ind : Fin 6 → Fin n → Fin n → ℝ := fun atomIndex rowSlot colSlot =>
      (if rowSlot ∈ car atomIndex then
        (if colSlot ∈ car atomIndex then kernelMinor K rowSlot colSlot else 0)
        else 0) with hind
    have hexpandTwo : ∀ atomIndex : Fin 6,
        ∑ rowSlot ∈ car atomIndex, ∑ colSlot ∈ car atomIndex,
            kernelMinor K rowSlot colSlot
          = ∑ rowSlot : Fin n, ∑ colSlot : Fin n, ind atomIndex rowSlot colSlot := by
      intro atomIndex
      rw [hexpand atomIndex]
      refine Finset.sum_congr rfl fun rowSlot _ => ?_
      by_cases hrow : rowSlot ∈ car atomIndex
      · simp only [hind, hrow, if_true]
        exact hexpand atomIndex _
      · simp [hind, hrow]
    have hswapAll : ∑ atomIndex : Fin 6, ∑ rowSlot : Fin n, ∑ colSlot : Fin n,
          ind atomIndex rowSlot colSlot
        = ∑ rowSlot : Fin n, ∑ colSlot : Fin n, ∑ atomIndex : Fin 6,
            ind atomIndex rowSlot colSlot := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun rowSlot _ => Finset.sum_comm
    have hterm : ∀ (atomIndex : Fin 6) (rowSlot colSlot : Fin n),
        0 ≤ ind atomIndex rowSlot colSlot := by
      intro atomIndex rowSlot colSlot
      by_cases hrow : rowSlot ∈ car atomIndex
      · by_cases hcol : colSlot ∈ car atomIndex
        · simp only [hind, hrow, hcol, if_true]
          exact kernelMinor_nonneg hsymm hidem rowSlot colSlot
        · simp [hind, hrow, hcol]
      · simp [hind, hrow]
    calc ∑ rowSlot : Fin n, ∑ colSlot : Fin n, kernelMinor K rowSlot colSlot
        ≤ ∑ rowSlot : Fin n, ∑ colSlot : Fin n, ∑ atomIndex : Fin 6,
            ind atomIndex rowSlot colSlot := by
          refine Finset.sum_le_sum fun rowSlot _ =>
            Finset.sum_le_sum fun colSlot _ => ?_
          rcases eq_or_ne rowSlot colSlot with rfl | hne
          · rw [kernelMinor_self]
            exact Finset.sum_nonneg fun atomIndex _ => hterm atomIndex rowSlot rowSlot
          · obtain ⟨witness, hrowMem, hcolMem⟩ := hco rowSlot colSlot hne
            have hle := Finset.single_le_sum
              (f := fun atomIndex : Fin 6 => ind atomIndex rowSlot colSlot)
              (fun atomIndex _ => hterm atomIndex rowSlot colSlot)
              (Finset.mem_univ witness)
            have hvalue : ind witness rowSlot colSlot
                = kernelMinor K rowSlot colSlot := by
              simp [hind, hrowMem, hcolMem]
            rwa [hvalue] at hle
      _ = ∑ atomIndex : Fin 6, ∑ rowSlot ∈ car atomIndex,
            ∑ colSlot ∈ car atomIndex, kernelMinor K rowSlot colSlot := by
          rw [← hswapAll]
          exact (Finset.sum_congr rfl fun atomIndex _ => hexpandTwo atomIndex).symm
  -- the defect total is the shifted-weight total
  have hdefect : ∑ atomIndex : Fin 6,
      ((∑ rowSlot ∈ car atomIndex, K rowSlot rowSlot) - readVal atomIndex)
      = 6 - ∑ atomIndex, readVal atomIndex := by
    rw [Finset.sum_sub_distrib, hdiagTotal, htrace]
    norm_num
  have hdefectNonneg : ∀ atomIndex : Fin 6,
      0 ≤ (∑ rowSlot ∈ car atomIndex, K rowSlot rowSlot) - readVal atomIndex := by
    intro atomIndex
    have hminorNonneg : 0 ≤ ∑ rowSlot ∈ car atomIndex,
        ∑ colSlot ∈ car atomIndex, kernelMinor K rowSlot colSlot :=
      Finset.sum_nonneg fun rowSlot _ => Finset.sum_nonneg fun colSlot _ =>
        kernelMinor_nonneg hsymm hidem rowSlot colSlot
    rw [hcorner atomIndex] at hminorNonneg
    nlinarith [hpos atomIndex]
  -- the crossing
  have hupper : ∑ atomIndex : Fin 6, ∑ rowSlot ∈ car atomIndex,
      ∑ colSlot ∈ car atomIndex, kernelMinor K rowSlot colSlot
      ≤ 2 * (6 - ∑ atomIndex, readVal atomIndex) := by
    rw [Finset.sum_congr rfl fun atomIndex _ => hcorner atomIndex]
    have hbound : ∀ atomIndex : Fin 6,
        2 * readVal atomIndex
            * ((∑ rowSlot ∈ car atomIndex, K rowSlot rowSlot) - readVal atomIndex)
          ≤ 2 * ((∑ rowSlot ∈ car atomIndex, K rowSlot rowSlot)
              - readVal atomIndex) := by
      intro atomIndex
      nlinarith [hcap atomIndex, hdefectNonneg atomIndex]
    calc ∑ atomIndex : Fin 6, 2 * readVal atomIndex
          * ((∑ rowSlot ∈ car atomIndex, K rowSlot rowSlot) - readVal atomIndex)
        ≤ ∑ atomIndex : Fin 6, 2 * ((∑ rowSlot ∈ car atomIndex, K rowSlot rowSlot)
            - readVal atomIndex) := Finset.sum_le_sum fun atomIndex _ => hbound atomIndex
      _ = 2 * (6 - ∑ atomIndex, readVal atomIndex) := by
          rw [← Finset.mul_sum, hdefect]
  rw [hminorTotal] at hweight
  linarith [hweight, hupper, hsum]

/-! ## Layer 5 — the deficit profile at basis count five -/

/-- The profile defect of a multiplicity: two units at multiplicity one
and one unit at multiplicity two. -/
def profileDefect (mult : Fin 6 → ℕ) (atomIndex : Fin 6) : ℕ :=
  2 * (if mult atomIndex = 1 then 1 else 0)
    + (if mult atomIndex = 2 then 1 else 0)

/-- The defect total is the profile mass. -/
theorem sum_profileDefect (mult : Fin 6 → ℕ) :
    ∑ atomIndex, profileDefect mult atomIndex
      = 2 * (Finset.univ.filter fun atomIndex => mult atomIndex = 1).card
        + (Finset.univ.filter fun atomIndex => mult atomIndex = 2).card := by
  classical
  simp only [profileDefect]
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_add_distrib,
    Finset.mul_sum]

/-- The multiplicity and its defect total at least three. -/
theorem three_le_add_profileDefect {mult : Fin 6 → ℕ}
    (hpos : ∀ atomIndex, 1 ≤ mult atomIndex) (atomIndex : Fin 6) :
    3 ≤ mult atomIndex + profileDefect mult atomIndex := by
  have hone := hpos atomIndex
  by_cases hcaseOne : mult atomIndex = 1
  · have hval : profileDefect mult atomIndex = 2 := by
      simp [profileDefect, hcaseOne]
    omega
  · by_cases hcaseTwo : mult atomIndex = 2
    · have hval : profileDefect mult atomIndex = 1 := by
        simp [profileDefect, hcaseTwo]
      omega
    · have hval : profileDefect mult atomIndex = 0 := by
        simp [profileDefect, hcaseOne, hcaseTwo]
      omega

/-- **THE DEFICIT SUPPORT FLOOR.**  Six multiplicities, each at least
one, with profile mass at most three, total at least fifteen. -/
theorem fifteen_le_sum_of_deficit {mult : Fin 6 → ℕ}
    (hpos : ∀ atomIndex, 1 ≤ mult atomIndex)
    (hmass : 2 * (Finset.univ.filter fun atomIndex => mult atomIndex = 1).card
        + (Finset.univ.filter fun atomIndex => mult atomIndex = 2).card ≤ 3) :
    15 ≤ ∑ atomIndex, mult atomIndex := by
  classical
  have hle : ∑ _atomIndex : Fin 6, 3
      ≤ ∑ atomIndex, (mult atomIndex + profileDefect mult atomIndex) :=
    Finset.sum_le_sum fun atomIndex _ => three_le_add_profileDefect hpos atomIndex
  rw [Finset.sum_add_distrib, sum_profileDefect, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  omega

/-- **THE DEFICIT PROFILE.**  Six multiplicities that total fifteen,
each at least one, with profile mass at most three, are all at most
three.  The mass counts two units for each multiplicity one and one for
each multiplicity two, and the count is exactly tight. -/
theorem multiplicity_le_three_of_deficit {mult : Fin 6 → ℕ}
    (hpos : ∀ atomIndex, 1 ≤ mult atomIndex)
    (htotal : ∑ atomIndex, mult atomIndex = 15)
    (hmass : 2 * (Finset.univ.filter fun atomIndex => mult atomIndex = 1).card
        + (Finset.univ.filter fun atomIndex => mult atomIndex = 2).card ≤ 3)
    (atomIndex : Fin 6) : mult atomIndex ≤ 3 := by
  classical
  by_contra hbig
  push Not at hbig
  have hstrict : 3 < mult atomIndex + profileDefect mult atomIndex := by
    have hcaseOne : mult atomIndex ≠ 1 := by omega
    have hcaseTwo : mult atomIndex ≠ 2 := by omega
    have hval : profileDefect mult atomIndex = 0 := by
      simp [profileDefect, hcaseOne, hcaseTwo]
    omega
  have hlt : ∑ _probe : Fin 6, 3
      < ∑ probe, (mult probe + profileDefect mult probe) :=
    Finset.sum_lt_sum (fun probe _ => three_le_add_profileDefect hpos probe)
      ⟨atomIndex, Finset.mem_univ _, hstrict⟩
  rw [Finset.sum_add_distrib, htotal, sum_profileDefect, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
  omega

/-- **THE DEFICIT KILL AT BASIS COUNT FIVE.**  A diagonal-Gram
shared-private datum at basis count five, coefficient trace three,
profile mass at most three, and with every slot pair sharing a support
atom, dies.  The kernel projector has trace two, the carriers are at
most three slots wide, and the kernel-minor budget crosses. -/
theorem SharedPrivateData.false_of_deficit_five {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (hfive : data.basisCount = 5)
    (htraceThree : Matrix.trace data.coeff = 3)
    (hmass : 2 * (Finset.univ.filter fun atomIndex =>
          basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 1).card
        + (Finset.univ.filter fun atomIndex =>
          basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 2).card
      ≤ 3)
    (hshare : ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      ∃ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne)
        ∧ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo)) :
    False := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsupp, hread, hnorm, hnz, _⟩ :=
    data.exists_kernel_read_frame hdiag
  set chartValue := chartObjective (chartPointOfDesign crux.design) with hchartValue
  set atomWeight := (chartPointOfDesign crux.design).weight with hatomWeight
  set car : Fin 6 → Finset (Fin data.basisCount) := fun atomIndex =>
    Finset.univ.filter fun slot =>
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)
    with hcarDef
  set kernelProj : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ :=
    1 - S with hkernelProj
  -- the kernel projector
  have hKsymm : kernelProjᵀ = kernelProj := by
    rw [hkernelProj, Matrix.transpose_sub, Matrix.transpose_one, hSsymm]
  have hKidem : kernelProj * kernelProj = kernelProj := by
    rw [hkernelProj, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hSidem]
    abel
  have hKtrace : Matrix.trace kernelProj = 2 := by
    rw [hkernelProj, Matrix.trace_sub, Matrix.trace_one, hStrace, htraceThree,
      Fintype.card_fin, hfive]
    norm_num
  -- the carrier laws
  have hcarMem : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      slot ∈ car atomIndex ↔
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
    intro atomIndex slot
    simp [hcarDef]
  have hcarCard : ∀ atomIndex : Fin 6, (car atomIndex).card
      = basisSupportMultiplicity data.tightDir data.basisLabel atomIndex :=
    fun _ => rfl
  have hmultPos : ∀ atomIndex : Fin 6,
      1 ≤ basisSupportMultiplicity data.tightDir data.basisLabel atomIndex := by
    intro atomIndex
    obtain ⟨slot, hslot⟩ := exists_basisIndex_datumTightSupport data.hdata
      data.basisLabel data.hspan data.leftInv data.hleft atomIndex
    exact Finset.card_pos.mpr
      ⟨slot, Finset.mem_filter.mpr ⟨Finset.mem_univ slot, hslot⟩⟩
  have hmultTotal :
      ∑ atomIndex : Fin 6,
        basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 15 := by
    rw [sum_basisSupportMultiplicity]
    rw [Finset.sum_congr rfl fun slot _ => data.hthree slot, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, hfive]
  have hcard : ∀ atomIndex : Fin 6, (car atomIndex).card ≤ 3 := by
    intro atomIndex
    rw [hcarCard]
    exact multiplicity_le_three_of_deficit hmultPos hmultTotal hmass atomIndex
  have hinc : ∀ slot : Fin data.basisCount,
      (Finset.univ.filter fun atomIndex => slot ∈ car atomIndex).card = 3 := by
    intro slot
    have hpred : (Finset.univ.filter fun atomIndex => slot ∈ car atomIndex)
        = datumTightSupport data.tightDir (data.basisLabel slot) := by
      have hcongr : (Finset.univ.filter fun atomIndex => slot ∈ car atomIndex)
          = Finset.univ.filter fun atomIndex =>
              atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) :=
        Finset.filter_congr fun atomIndex _ => by rw [hcarMem]
      rw [hcongr, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hpred]
    exact data.hthree slot
  -- the reads
  have hsuppCar : ∀ atomIndex : Fin 6, ∀ slot ∉ car atomIndex,
      readVecs atomIndex slot = 0 := by
    intro atomIndex slot hslot
    exact hsupp atomIndex slot fun hmem => hslot ((hcarMem atomIndex slot).mpr hmem)
  have hnzCar : ∀ atomIndex : Fin 6,
      ∃ slot ∈ car atomIndex, readVecs atomIndex slot ≠ 0 := by
    intro atomIndex
    obtain ⟨slot, hslot⟩ := Function.ne_iff.mp (hnz atomIndex)
    refine ⟨slot, ?_, hslot⟩
    by_contra hnotMem
    exact hslot (hsuppCar atomIndex slot hnotMem)
  have hmemActive : ∀ slot : Fin data.basisCount,
      data.basisLabel slot ∈ data.activeSet := by
    intro slot
    have h := data.hmem slot
    simp only [positiveActiveSet, Finset.mem_filter] at h
    exact h.1
  have hreadCar : ∀ atomIndex : Fin 6, ∀ slot ∈ car atomIndex,
      (kernelProj *ᵥ readVecs atomIndex) slot
        = (1 - (chartValue + atomWeight atomIndex)) * readVecs atomIndex slot := by
    intro atomIndex slot hslot
    have hmemSubset : atomIndex ∈ data.activeSubset (data.basisLabel slot) :=
      datumTightSupport_subset data.hdata (hmemActive slot)
        ((hcarMem atomIndex slot).mp hslot)
    exact kernel_corner_read (hread atomIndex slot hmemSubset)
  -- the read window and the read total
  have hvalueNeg : chartValue < 0 := data.hvalueNeg
  have hweightLe : ∀ atomIndex : Fin 6, atomWeight atomIndex ≤ 1 := by
    intro atomIndex
    have hsum := data.hdata.weight_sum_one
    have hle : atomWeight atomIndex ≤ ∑ probe, atomWeight probe :=
      Finset.single_le_sum (f := atomWeight)
        (fun probe _ => (data.hdata.weight_pos probe).le) (Finset.mem_univ atomIndex)
    rwa [hsum] at hle
  have hcapNonneg : ∀ atomIndex : Fin 6,
      0 ≤ chartValue + atomWeight atomIndex := fun atomIndex =>
    capture_diagonal_nonneg_of_isChartStationaryData data.hdata atomIndex
  have hreadPos : ∀ atomIndex : Fin 6,
      0 < 1 - (chartValue + atomWeight atomIndex) := by
    intro atomIndex
    have := hweightLe atomIndex
    linarith
  have hreadCap : ∀ atomIndex : Fin 6,
      1 - (chartValue + atomWeight atomIndex) ≤ 1 := by
    intro atomIndex
    have := hcapNonneg atomIndex
    linarith
  have hreadSum : 5 < ∑ atomIndex : Fin 6,
      (1 - (chartValue + atomWeight atomIndex)) := by
    have hexpand : ∑ atomIndex : Fin 6, (1 - (chartValue + atomWeight atomIndex))
        = 6 - (6 * chartValue + ∑ atomIndex, atomWeight atomIndex) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        nsmul_eq_mul]
      norm_num
    rw [hexpand, data.hdata.weight_sum_one]
    linarith
  -- the slot pairs share atoms
  have hco : ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      ∃ atomIndex, slotOne ∈ car atomIndex ∧ slotTwo ∈ car atomIndex := by
    intro slotOne slotTwo hne
    obtain ⟨atomIndex, hone, htwo⟩ := hshare slotOne slotTwo hne
    exact ⟨atomIndex, (hcarMem atomIndex slotOne).mpr hone,
      (hcarMem atomIndex slotTwo).mpr htwo⟩
  exact false_of_kernelMinor_budget hKsymm hKidem hKtrace car readVecs
    (fun atomIndex => 1 - (chartValue + atomWeight atomIndex)) hcard hinc
    hsuppCar hnzCar hreadCar hreadPos hreadCap hco hreadSum

/-! ## Layer 6 — the deficit residues and the extras fold -/

/-- **THE DEFICIT RESIDUE AT THE OTHER BASIS COUNTS.**  The trace-three
deficit away from basis count five. -/
def SharedPrivateDeficitSixClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (gramDiag : Fin data.basisCount → ℝ),
    data.gram = Matrix.diagonal gramDiag →
    Matrix.trace data.coeff = 3 →
    data.basisCount = 6 →
    2 * (Finset.univ.filter fun atomIndex =>
          basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 1).card
      + (Finset.univ.filter fun atomIndex =>
          basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 2).card
      ≤ 3 →
    False

/-- **THE SPLIT-SUPPORT RESIDUE.**  The trace-three deficit at basis
count five with two basis supports that share no atom.  Two disjoint
supports of three atoms fill the six atoms, thus the split residue is
the complementary-support stratum. -/
def SharedPrivateDeficitSplitClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (gramDiag : Fin data.basisCount → ℝ),
    data.gram = Matrix.diagonal gramDiag →
    Matrix.trace data.coeff = 3 →
    2 * (Finset.univ.filter fun atomIndex =>
          basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 1).card
      + (Finset.univ.filter fun atomIndex =>
          basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 2).card
      ≤ 3 →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      (∀ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) →
        atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slotTwo)) →
      False

/-- **THE DEFICIT DISPATCH.**  The kernel-minor kill leaves two deficit
residues: the other basis counts, and the split supports at basis count
five. -/
theorem sharedPrivateDeficitClosed_of_residues
    (hsix : SharedPrivateDeficitSixClosed)
    (hsplit : SharedPrivateDeficitSplitClosed) :
    SharedPrivateDeficitClosed := by
  classical
  intro crux data gramDiag hdiag htraceThree hmass
  by_cases hfive : data.basisCount = 5
  · by_cases hshare : ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      ∃ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne)
        ∧ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo)
    · exact data.false_of_deficit_five hdiag hfive htraceThree hmass hshare
    · push Not at hshare
      obtain ⟨slotOne, slotTwo, hne, hdisjoint⟩ := hshare
      refine hsplit crux data gramDiag hdiag htraceThree hmass slotOne slotTwo hne
        fun atomIndex hone htwo => ?_
      exact hdisjoint atomIndex hone htwo
  · refine hsix crux data gramDiag hdiag htraceThree ?_ hmass
    have hmultPos : ∀ atomIndex : Fin 6,
        1 ≤ basisSupportMultiplicity data.tightDir data.basisLabel atomIndex := by
      intro atomIndex
      obtain ⟨slot, hslot⟩ := exists_basisIndex_datumTightSupport data.hdata
        data.basisLabel data.hspan data.leftInv data.hleft atomIndex
      exact Finset.card_pos.mpr
        ⟨slot, Finset.mem_filter.mpr ⟨Finset.mem_univ slot, hslot⟩⟩
    have hmultTotal :
        ∑ atomIndex : Fin 6,
          basisSupportMultiplicity data.tightDir data.basisLabel atomIndex
          = 3 * data.basisCount := by
      rw [sum_basisSupportMultiplicity,
        Finset.sum_congr rfl fun slot _ => data.hthree slot, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      ring
    have hfloor := fifteen_le_sum_of_deficit hmultPos hmass
    rw [hmultTotal] at hfloor
    have hupper := data.basisCount_le_six
    omega

/-- **THE SHARED-PRIVATE CIRCUIT RESIDUE.**  A positive label parallel
to no basis column dies at every shared-private datum. -/
def SharedPrivateCircuitClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    (∀ (slot : Fin data.basisCount) (scale : ℝ),
      data.tightDir label ≠ scale • data.tightDir (data.basisLabel slot)) →
    False

/-- **THE EXTRAS FOLD.**  A closed circuit residue makes every positive
label parallel to a basis column, thus the parallel fold gives the
diagonal Gram core and the extras residue is closed. -/
theorem sharedPrivateExtrasClosed_of_circuit
    (hcircuit : SharedPrivateCircuitClosed) : SharedPrivateExtrasClosed := by
  intro crux data hnotDiagonal
  obtain ⟨gramDiag, hg⟩ := exists_diagonal_gram_of_parallel data.hdata data.hleft
    data.hHform fun label hmem hpos => by
      by_contra hnot
      push Not at hnot
      exact hcircuit crux data label hmem hpos hnot
  exact hnotDiagonal gramDiag hg

end Gtz
