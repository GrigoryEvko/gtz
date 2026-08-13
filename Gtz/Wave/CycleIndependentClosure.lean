import Gtz.Wave.RankFourRungAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The cycle independent closure — the doubled cycle against the trace budget

The labeled cycle carries two doubled pairs and two singles.  A nonzero
cross determinant on a doubled pair reads the corner trace exactly, and
two corner traces exhaust the trace budget: `4 * value + (four weights)
= 2` with positive weights forces `value >= 1/4`, against the negative
value.  The dichotomy routes the remaining case to a parallel doubled
pair with equal weights, and the kernel layer turns that pair into a
kernel vector of the assembly.  The projection keeps the kernel, and a
projected kernel vector that vanishes makes the two design atoms
parallel, against the crux.

The layers:

1. The share vocabulary: membership extraction from the share sets, the
   exclusive carriers, and the atom distinctness laws.
2. **The double-trace kill**: two corner trace laws against the trace
   budget and the weight sum.
3. The pair kernel vector: the parallel combination of a doubled pair
   enters the assembly kernel, the constant diagonal and the Gram
   positivity force equal coordinate squares, and commutation makes the
   kernel projection-invariant.
4. **The projected-kernel kill**: a vanishing projected kernel vector
   makes the two design atoms parallel, against `hasNoParallelPair`.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.shareSet_mem_left`, `Gtz.shareSet_mem_right` — the share
  extraction.
* `Gtz.atom_ne_of_exclusive_carriers` — the distinctness law.
* `Gtz.false_of_double_trace_laws` — **THE DOUBLE-TRACE KILL.**
* `Gtz.pairKernelVec` with its value laws and
  `Gtz.assembly_mulVec_pairKernelVec` — **THE KERNEL LAYER.**
* `Gtz.pair_coordinate_squares_eq` — the equal-squares law.
* `Gtz.assembly_mulVec_projection_pairKernelVec` — the invariance.
* `Gtz.SixThreeCrux.false_of_projection_kernel_pair` — **THE
  PROJECTED-KERNEL KILL.**

## Vacuity

The crux statements are vacuous if `Gtz.GtzWeighted 6 3` holds.  The
share and kernel calculus is unconditional.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## Layer 1 — the share vocabulary -/

/-- A named atom of a share set sits in the left support. -/
theorem shareSet_mem_left {basisLabel : Fin basisCount → activeIndex}
    {slotK slotL : Fin basisCount} {atomOne atomTwo : Fin size}
    (hshare : shareSet tightDir basisLabel slotK slotL = {atomOne, atomTwo}) :
    atomOne ∈ datumTightSupport tightDir (basisLabel slotK) := by
  have hmem : atomOne ∈ shareSet tightDir basisLabel slotK slotL := by
    rw [hshare]
    exact Finset.mem_insert_self _ _
  rw [shareSet, Finset.mem_filter] at hmem
  exact hmem.2.1

/-- A named atom of a share set sits in the right support. -/
theorem shareSet_mem_right {basisLabel : Fin basisCount → activeIndex}
    {slotK slotL : Fin basisCount} {atomOne atomTwo : Fin size}
    (hshare : shareSet tightDir basisLabel slotK slotL = {atomOne, atomTwo}) :
    atomOne ∈ datumTightSupport tightDir (basisLabel slotL) := by
  have hmem : atomOne ∈ shareSet tightDir basisLabel slotK slotL := by
    rw [hshare]
    exact Finset.mem_insert_self _ _
  rw [shareSet, Finset.mem_filter] at hmem
  exact hmem.2.2

/-- The second named atom of a share set sits in the left support. -/
theorem shareSet_snd_mem_left {basisLabel : Fin basisCount → activeIndex}
    {slotK slotL : Fin basisCount} {atomOne atomTwo : Fin size}
    (hshare : shareSet tightDir basisLabel slotK slotL = {atomOne, atomTwo}) :
    atomTwo ∈ datumTightSupport tightDir (basisLabel slotK) := by
  have hmem : atomTwo ∈ shareSet tightDir basisLabel slotK slotL := by
    rw [hshare]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [shareSet, Finset.mem_filter] at hmem
  exact hmem.2.1

/-- The second named atom of a share set sits in the right support. -/
theorem shareSet_snd_mem_right {basisLabel : Fin basisCount → activeIndex}
    {slotK slotL : Fin basisCount} {atomOne atomTwo : Fin size}
    (hshare : shareSet tightDir basisLabel slotK slotL = {atomOne, atomTwo}) :
    atomTwo ∈ datumTightSupport tightDir (basisLabel slotL) := by
  have hmem : atomTwo ∈ shareSet tightDir basisLabel slotK slotL := by
    rw [hshare]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [shareSet, Finset.mem_filter] at hmem
  exact hmem.2.2

/-- **THE DISTINCTNESS LAW.**  An atom with exclusive carriers differs
from every atom that a third slot supports. -/
theorem atom_ne_of_exclusive_carriers
    {basisLabel : Fin basisCount → activeIndex}
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    {slotK slotL slotOther : Fin basisCount} (hKL : slotK ≠ slotL)
    (hOK : slotOther ≠ slotK) (hOL : slotOther ≠ slotL)
    {atomIndex otherAtom : Fin size}
    (hmemK : atomIndex ∈ datumTightSupport tightDir (basisLabel slotK))
    (hmemL : atomIndex ∈ datumTightSupport tightDir (basisLabel slotL))
    (hmemOther : otherAtom ∈ datumTightSupport tightDir (basisLabel slotOther)) :
    atomIndex ≠ otherAtom := by
  intro heq
  have hzero := shared_atom_exclusive_carriers basisLabel hmult hKL hmemK hmemL
    hOK hOL
  rw [heq] at hzero
  exact (mem_datumTightSupport.mp hmemOther) hzero

/-! ## Layer 2 — the double-trace kill -/

/-- The quadruple of four distinct slots is the whole slot universe. -/
theorem slot_quadruple_eq_univ {slotK slotL slotM slotN : Fin 4}
    (hKL : slotK ≠ slotL) (hKM : slotK ≠ slotM) (hKN : slotK ≠ slotN)
    (hLM : slotL ≠ slotM) (hLN : slotL ≠ slotN) (hMN : slotM ≠ slotN) :
    ({slotK, slotL, slotM, slotN} : Finset (Fin 4)) = Finset.univ := by
  have hnotK : slotK ∉ ({slotL, slotM, slotN} : Finset (Fin 4)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hKL heq
    · rcases Finset.mem_insert.mp hmem' with heq | hmem''
      · exact hKM heq
      · exact hKN (Finset.mem_singleton.mp hmem'')
  have hnotL : slotL ∉ ({slotM, slotN} : Finset (Fin 4)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hLM heq
    · exact hLN (Finset.mem_singleton.mp hmem')
  have hnotM : slotM ∉ ({slotN} : Finset (Fin 4)) := fun hmem =>
    hMN (Finset.mem_singleton.mp hmem)
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_insert_of_notMem hnotK, Finset.card_insert_of_notMem hnotL,
    Finset.card_insert_of_notMem hnotM, Finset.card_singleton, Finset.card_univ,
    Fintype.card_fin]

/-- The trace over four distinct slots is the sum of the four diagonals. -/
theorem trace_eq_four_diag {M : Matrix (Fin 4) (Fin 4) ℝ}
    {slotK slotL slotM slotN : Fin 4}
    (hKL : slotK ≠ slotL) (hKM : slotK ≠ slotM) (hKN : slotK ≠ slotN)
    (hLM : slotL ≠ slotM) (hLN : slotL ≠ slotN) (hMN : slotM ≠ slotN) :
    Matrix.trace M
      = M slotK slotK + M slotL slotL + M slotM slotM + M slotN slotN := by
  have hnotK : slotK ∉ ({slotL, slotM, slotN} : Finset (Fin 4)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hKL heq
    · rcases Finset.mem_insert.mp hmem' with heq | hmem''
      · exact hKM heq
      · exact hKN (Finset.mem_singleton.mp hmem'')
  have hnotL : slotL ∉ ({slotM, slotN} : Finset (Fin 4)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hLM heq
    · exact hLN (Finset.mem_singleton.mp hmem')
  have hnotM : slotM ∉ ({slotN} : Finset (Fin 4)) := fun hmem =>
    hMN (Finset.mem_singleton.mp hmem)
  have htraceSum : Matrix.trace M
      = ∑ slotIndex ∈ ({slotK, slotL, slotM, slotN} : Finset (Fin 4)),
          M slotIndex slotIndex := by
    rw [slot_quadruple_eq_univ hKL hKM hKN hLM hLN hMN]
    rfl
  rw [htraceSum, Finset.sum_insert hnotK, Finset.sum_insert hnotL,
    Finset.sum_insert hnotM, Finset.sum_singleton]
  ring

/-- The weight sum over four distinct atoms is at most one. -/
theorem four_weight_sum_le_one
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {atomA atomB atomC atomD : Fin size}
    (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC) (hAD : atomA ≠ atomD)
    (hBC : atomB ≠ atomC) (hBD : atomB ≠ atomD) (hCD : atomC ≠ atomD) :
    weight atomA + weight atomB + weight atomC + weight atomD ≤ 1 := by
  have hnotA : atomA ∉ ({atomB, atomC, atomD} : Finset (Fin size)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hAB heq
    · rcases Finset.mem_insert.mp hmem' with heq | hmem''
      · exact hAC heq
      · exact hAD (Finset.mem_singleton.mp hmem'')
  have hnotB : atomB ∉ ({atomC, atomD} : Finset (Fin size)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hBC heq
    · exact hBD (Finset.mem_singleton.mp hmem')
  have hnotC : atomC ∉ ({atomD} : Finset (Fin size)) := fun hmem =>
    hCD (Finset.mem_singleton.mp hmem)
  have hsubset : ∑ atomIndex ∈ ({atomA, atomB, atomC, atomD} : Finset (Fin size)),
      weight atomIndex ≤ ∑ atomIndex : Fin size, weight atomIndex :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun atomIndex _ _ => (hdata.weight_pos atomIndex).le
  rw [hdata.weight_sum_one, Finset.sum_insert hnotA, Finset.sum_insert hnotB,
    Finset.sum_insert hnotC, Finset.sum_singleton] at hsubset
  linarith

/-- **THE DOUBLE-TRACE KILL.**  Two corner trace laws on disjoint slot
pairs with four distinct doubled atoms exhaust the trace budget. -/
theorem false_of_double_trace_laws
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hvalueNeg : value < 0)
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (htrace : Matrix.trace M = 2)
    {slotK slotL slotM slotN : Fin 4}
    (hKL : slotK ≠ slotL) (hKM : slotK ≠ slotM) (hKN : slotK ≠ slotN)
    (hLM : slotL ≠ slotM) (hLN : slotL ≠ slotN) (hMN : slotM ≠ slotN)
    {atomA atomB atomC atomD : Fin size}
    (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC) (hAD : atomA ≠ atomD)
    (hBC : atomB ≠ atomC) (hBD : atomB ≠ atomD) (hCD : atomC ≠ atomD)
    (htraceKL : M slotK slotK + M slotL slotL
      = 2 * value + weight atomA + weight atomB)
    (htraceMN : M slotM slotM + M slotN slotN
      = 2 * value + weight atomC + weight atomD) :
    False := by
  have hfour := trace_eq_four_diag hKL hKM hKN hLM hLN hMN (M := M)
  have hsum := four_weight_sum_le_one hdata hAB hAC hAD hBC hBD hCD
  rw [htrace] at hfour
  linarith

/-! ## Layer 3 — the pair kernel vector -/

/-- The parallel combination of a doubled pair as an ambient vector: the
second coordinate at the first atom, minus the first coordinate at the
second atom. -/
def pairKernelVec (firstCoord secondCoord : ℝ) (atomOne atomTwo : Fin size) :
    Fin size → ℝ :=
  fun atomIndex =>
    if atomIndex = atomOne then secondCoord
      else if atomIndex = atomTwo then -firstCoord else 0

theorem pairKernelVec_apply_one {firstCoord secondCoord : ℝ}
    {atomOne atomTwo : Fin size} :
    pairKernelVec firstCoord secondCoord atomOne atomTwo atomOne = secondCoord := by
  simp [pairKernelVec]

theorem pairKernelVec_apply_two {firstCoord secondCoord : ℝ}
    {atomOne atomTwo : Fin size} (hne : atomOne ≠ atomTwo) :
    pairKernelVec firstCoord secondCoord atomOne atomTwo atomTwo = -firstCoord := by
  simp [pairKernelVec, Ne.symm hne]

theorem pairKernelVec_apply_off {firstCoord secondCoord : ℝ}
    {atomOne atomTwo atomIndex : Fin size} (hone : atomIndex ≠ atomOne)
    (htwo : atomIndex ≠ atomTwo) :
    pairKernelVec firstCoord secondCoord atomOne atomTwo atomIndex = 0 := by
  simp [pairKernelVec, hone, htwo]

/-- The basis columns annihilate the pair kernel vector when every slot
either misses the pair or restricts to it proportionally. -/
theorem basis_transpose_mulVec_pairKernelVec
    {basisLabel : Fin basisCount → activeIndex}
    {atomOne atomTwo : Fin size} (hne : atomOne ≠ atomTwo)
    (firstCoord secondCoord : ℝ)
    (hprop : ∀ columnIndex : Fin basisCount,
      tightDir (basisLabel columnIndex) atomOne * secondCoord
        - tightDir (basisLabel columnIndex) atomTwo * firstCoord = 0) :
    (tightBasisColumns tightDir basisLabel)ᵀ
        *ᵥ pairKernelVec firstCoord secondCoord atomOne atomTwo = 0 := by
  funext columnIndex
  rw [Pi.zero_apply]
  show (∑ atomIndex : Fin size,
      (tightBasisColumns tightDir basisLabel)ᵀ columnIndex atomIndex
        * pairKernelVec firstCoord secondCoord atomOne atomTwo atomIndex) = 0
  have hcollapse : ∀ atomIndex : Fin size, atomIndex ≠ atomOne →
      atomIndex ≠ atomTwo →
      (tightBasisColumns tightDir basisLabel)ᵀ columnIndex atomIndex
        * pairKernelVec firstCoord secondCoord atomOne atomTwo atomIndex = 0 := by
    intro atomIndex hone htwo
    rw [pairKernelVec_apply_off hone htwo, mul_zero]
  have hnotOne : atomOne ∉ ({atomTwo} : Finset (Fin size)) := fun hmem =>
    hne (Finset.mem_singleton.mp hmem)
  have hrestrict : (∑ atomIndex : Fin size,
      (tightBasisColumns tightDir basisLabel)ᵀ columnIndex atomIndex
        * pairKernelVec firstCoord secondCoord atomOne atomTwo atomIndex)
      = ∑ atomIndex ∈ ({atomOne, atomTwo} : Finset (Fin size)),
          (tightBasisColumns tightDir basisLabel)ᵀ columnIndex atomIndex
            * pairKernelVec firstCoord secondCoord atomOne atomTwo atomIndex := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro atomIndex _ hnot
    have hone : atomIndex ≠ atomOne := fun heq =>
      hnot (heq ▸ Finset.mem_insert_self _ _)
    have htwo : atomIndex ≠ atomTwo := fun heq =>
      hnot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    exact hcollapse atomIndex hone htwo
  rw [hrestrict, Finset.sum_insert hnotOne, Finset.sum_singleton,
    pairKernelVec_apply_one, pairKernelVec_apply_two hne]
  have hentry := hprop columnIndex
  show tightDir (basisLabel columnIndex) atomOne * secondCoord
      + tightDir (basisLabel columnIndex) atomTwo * -firstCoord = 0
  linarith

/-- **THE KERNEL LAW.**  The Gram form of the assembly annihilates every
vector that the basis columns annihilate. -/
theorem assembly_mulVec_of_basis_transpose_zero
    {basisLabel : Fin basisCount → activeIndex}
    {H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    {probe : Fin size → ℝ}
    (hzero : (tightBasisColumns tightDir basisLabel)ᵀ *ᵥ probe = 0) :
    chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ probe = 0 := by
  rw [← hHform, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hzero,
    Matrix.mulVec_zero, Matrix.mulVec_zero]

/-- The assembly quadratic form of any probe is nonnegative through the
Gram core. -/
theorem assembly_quadratic_nonneg
    {basisLabel : Fin basisCount → activeIndex}
    {H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    (hpsd : H.PosSemidef) (probe : Fin size → ℝ) :
    0 ≤ probe ⬝ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ probe) := by
  rw [← hHform, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hquad := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2
    ((tightBasisColumns tightDir basisLabel)ᵀ *ᵥ probe)
  have hstar : star ((tightBasisColumns tightDir basisLabel)ᵀ *ᵥ probe)
      = (tightBasisColumns tightDir basisLabel)ᵀ *ᵥ probe := by
    ext atomIndex
    simp
  rw [hstar] at hquad
  have hvec : (tightBasisColumns tightDir basisLabel)ᵀ *ᵥ probe
      = probe ᵥ* tightBasisColumns tightDir basisLabel := by
    rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]
  rw [hvec] at hquad ⊢
  rw [Matrix.dotProduct_mulVec]
  exact hquad

/-! ## Layer 4 — the projected-kernel kill -/

/-- **THE PROJECTED-KERNEL KILL.**  At a crux, a doubled pair whose
kernel vector projects to zero makes the two design atoms parallel. -/
theorem SixThreeCrux.false_of_projection_kernel_pair (crux : SixThreeCrux)
    {atomOne atomTwo : Fin 6} (hne : atomOne ≠ atomTwo)
    {firstCoord secondCoord : ℝ} (hsecond : secondCoord ≠ 0)
    (hproj : (chartPointOfDesign crux.design).chart
        *ᵥ pairKernelVec firstCoord secondCoord atomOne atomTwo = 0) :
    False := by
  have hVt : (scaledAtomRows crux.design)ᵀ
      *ᵥ pairKernelVec firstCoord secondCoord atomOne atomTwo = 0 := by
    have hchain : (scaledAtomRows crux.design)ᵀ
        *ᵥ ((chartPointOfDesign crux.design).chart
          *ᵥ pairKernelVec firstCoord secondCoord atomOne atomTwo)
        = (scaledAtomRows crux.design)ᵀ
          *ᵥ pairKernelVec firstCoord secondCoord atomOne atomTwo := by
      show (scaledAtomRows crux.design)ᵀ
          *ᵥ (projectionOfDesign crux.design
            *ᵥ pairKernelVec firstCoord secondCoord atomOne atomTwo) = _
      rw [projectionOfDesign, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
        transpose_mul_scaledAtomRows, Matrix.one_mul]
    rw [hproj, Matrix.mulVec_zero] at hchain
    exact hchain.symm
  have hrelation : ∀ coord : Fin 3,
      Real.sqrt (crux.design.weight atomOne) * crux.design.atom atomOne coord
          * secondCoord
        - Real.sqrt (crux.design.weight atomTwo) * crux.design.atom atomTwo coord
          * firstCoord = 0 := by
    intro coord
    have hentry := congrFun hVt coord
    rw [Pi.zero_apply] at hentry
    have hexpand : ((scaledAtomRows crux.design)ᵀ
        *ᵥ pairKernelVec firstCoord secondCoord atomOne atomTwo) coord
        = Real.sqrt (crux.design.weight atomOne) * crux.design.atom atomOne coord
            * secondCoord
          + Real.sqrt (crux.design.weight atomTwo)
            * crux.design.atom atomTwo coord * -firstCoord := by
      show (∑ atomIndex : Fin 6,
          (scaledAtomRows crux.design)ᵀ coord atomIndex
            * pairKernelVec firstCoord secondCoord atomOne atomTwo atomIndex) = _
      have hnotOne : atomOne ∉ ({atomTwo} : Finset (Fin 6)) := fun hmem =>
        hne (Finset.mem_singleton.mp hmem)
      have hrestrict : (∑ atomIndex : Fin 6,
          (scaledAtomRows crux.design)ᵀ coord atomIndex
            * pairKernelVec firstCoord secondCoord atomOne atomTwo atomIndex)
          = ∑ atomIndex ∈ ({atomOne, atomTwo} : Finset (Fin 6)),
              (scaledAtomRows crux.design)ᵀ coord atomIndex
                * pairKernelVec firstCoord secondCoord atomOne atomTwo atomIndex := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro atomIndex _ hnot
        have hone : atomIndex ≠ atomOne := fun heq =>
          hnot (heq ▸ Finset.mem_insert_self _ _)
        have htwo : atomIndex ≠ atomTwo := fun heq =>
          hnot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        rw [pairKernelVec_apply_off hone htwo, mul_zero]
      rw [hrestrict, Finset.sum_insert hnotOne, Finset.sum_singleton,
        pairKernelVec_apply_one, pairKernelVec_apply_two hne]
      rfl
    rw [hexpand] at hentry
    linarith
  have hwOne : (0 : ℝ) < Real.sqrt (crux.design.weight atomOne) :=
    Real.sqrt_pos.mpr (crux.design.weight_pos atomOne)
  have hwTwo : (0 : ℝ) < Real.sqrt (crux.design.weight atomTwo) :=
    Real.sqrt_pos.mpr (crux.design.weight_pos atomTwo)
  have hparallel : HasParallelPair crux.design := by
    refine ⟨atomTwo, atomOne,
      (Real.sqrt (crux.design.weight atomTwo) * firstCoord)
        / (Real.sqrt (crux.design.weight atomOne) * secondCoord), hne.symm, ?_⟩
    funext coord
    have hrel := hrelation coord
    rw [Pi.smul_apply, smul_eq_mul]
    have hden : Real.sqrt (crux.design.weight atomOne) * secondCoord ≠ 0 :=
      mul_ne_zero (ne_of_gt hwOne) hsecond
    field_simp
    linarith [hrel]
  exact crux.hasNoParallelPair hparallel


/-- A row of the assembly against the pair kernel vector collapses to the
two pair entries. -/
theorem assembly_row_pairKernelVec
    {form : Matrix (Fin size) (Fin size) ℝ}
    {firstCoord secondCoord : ℝ} {atomOne atomTwo : Fin size}
    (hne : atomOne ≠ atomTwo) (rowIndex : Fin size) :
    (form *ᵥ pairKernelVec firstCoord secondCoord atomOne atomTwo) rowIndex
      = form rowIndex atomOne * secondCoord
        - form rowIndex atomTwo * firstCoord := by
  show (∑ atomIndex : Fin size, form rowIndex atomIndex
      * pairKernelVec firstCoord secondCoord atomOne atomTwo atomIndex) = _
  have hnotOne : atomOne ∉ ({atomTwo} : Finset (Fin size)) := fun hmem =>
    hne (Finset.mem_singleton.mp hmem)
  have hrestrict : (∑ atomIndex : Fin size, form rowIndex atomIndex
      * pairKernelVec firstCoord secondCoord atomOne atomTwo atomIndex)
      = ∑ atomIndex ∈ ({atomOne, atomTwo} : Finset (Fin size)),
          form rowIndex atomIndex
            * pairKernelVec firstCoord secondCoord atomOne atomTwo atomIndex := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro atomIndex _ hnot
    have hone : atomIndex ≠ atomOne := fun heq =>
      hnot (heq ▸ Finset.mem_insert_self _ _)
    have htwo : atomIndex ≠ atomTwo := fun heq =>
      hnot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [pairKernelVec_apply_off hone htwo, mul_zero]
  rw [hrestrict, Finset.sum_insert hnotOne, Finset.sum_singleton,
    pairKernelVec_apply_one, pairKernelVec_apply_two hne]
  ring

/-- The quadratic form of a pair probe collapses to the four pair
entries. -/
theorem pair_quadratic_expand
    {form : Matrix (Fin size) (Fin size) ℝ}
    {firstCoord secondCoord : ℝ} {atomOne atomTwo : Fin size}
    (hne : atomOne ≠ atomTwo) :
    pairKernelVec firstCoord secondCoord atomOne atomTwo
        ⬝ᵥ (form *ᵥ pairKernelVec firstCoord secondCoord atomOne atomTwo)
      = secondCoord * (form atomOne atomOne * secondCoord
            - form atomOne atomTwo * firstCoord)
        - firstCoord * (form atomTwo atomOne * secondCoord
            - form atomTwo atomTwo * firstCoord) := by
  show (∑ atomIndex : Fin size,
      pairKernelVec firstCoord secondCoord atomOne atomTwo atomIndex
        * (form *ᵥ pairKernelVec firstCoord secondCoord atomOne atomTwo) atomIndex)
      = _
  have hnotOne : atomOne ∉ ({atomTwo} : Finset (Fin size)) := fun hmem =>
    hne (Finset.mem_singleton.mp hmem)
  have hrestrict : (∑ atomIndex : Fin size,
      pairKernelVec firstCoord secondCoord atomOne atomTwo atomIndex
        * (form *ᵥ pairKernelVec firstCoord secondCoord atomOne atomTwo) atomIndex)
      = ∑ atomIndex ∈ ({atomOne, atomTwo} : Finset (Fin size)),
          pairKernelVec firstCoord secondCoord atomOne atomTwo atomIndex
            * (form *ᵥ pairKernelVec firstCoord secondCoord atomOne atomTwo)
                atomIndex := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro atomIndex _ hnot
    have hone : atomIndex ≠ atomOne := fun heq =>
      hnot (heq ▸ Finset.mem_insert_self _ _)
    have htwo : atomIndex ≠ atomTwo := fun heq =>
      hnot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [pairKernelVec_apply_off hone htwo, zero_mul]
  rw [hrestrict, Finset.sum_insert hnotOne, Finset.sum_singleton,
    pairKernelVec_apply_one, pairKernelVec_apply_two hne,
    assembly_row_pairKernelVec hne, assembly_row_pairKernelVec hne]
  ring

/-- **THE EQUAL-SQUARES LAW.**  A pair kernel vector of the assembly with
the constant diagonal forces equal coordinate squares: the two pair rows
price the mixed entries, and the two pair probes cap their sum. -/
theorem pair_coordinate_squares_eq
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    {H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    (hpsd : H.PosSemidef)
    {firstCoord secondCoord : ℝ} {atomOne atomTwo : Fin size}
    (hne : atomOne ≠ atomTwo)
    (hone : firstCoord ≠ 0) (htwo : secondCoord ≠ 0)
    (hker : chartMultiplierAssembly activeSet activeWeight tightDir
        *ᵥ pairKernelVec firstCoord secondCoord atomOne atomTwo = 0) :
    firstCoord = secondCoord ∨ firstCoord = -secondCoord := by
  set assembly := chartMultiplierAssembly activeSet activeWeight tightDir
    with hassembly
  have hrowOne : assembly atomOne atomOne * secondCoord
      - assembly atomOne atomTwo * firstCoord = 0 := by
    have hentry := congrFun hker atomOne
    rw [Pi.zero_apply] at hentry
    rw [← assembly_row_pairKernelVec hne atomOne]
    exact hentry
  have hrowTwo : assembly atomTwo atomOne * secondCoord
      - assembly atomTwo atomTwo * firstCoord = 0 := by
    have hentry := congrFun hker atomTwo
    rw [Pi.zero_apply] at hentry
    rw [← assembly_row_pairKernelVec hne atomTwo]
    exact hentry
  have hdiagOne := hdata.assembly_diagonal atomOne
  have hdiagTwo := hdata.assembly_diagonal atomTwo
  rw [← hassembly] at hdiagOne hdiagTwo
  have hsizePos : (0 : ℝ) < ((size : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (size_pos_of_isChartStationaryData hdata))
  have hplus := assembly_quadratic_nonneg hHform hpsd
    (pairKernelVec (-1) 1 atomOne atomTwo)
  have hminus := assembly_quadratic_nonneg hHform hpsd
    (pairKernelVec 1 1 atomOne atomTwo)
  rw [← hassembly, pair_quadratic_expand hne] at hplus hminus
  rw [hdiagOne, hdiagTwo] at hplus hminus
  rw [hdiagOne] at hrowOne
  rw [hdiagTwo] at hrowTwo
  have hprodOne : assembly atomOne atomTwo * firstCoord * secondCoord
      = secondCoord * secondCoord * ((size : ℝ))⁻¹ := by
    linear_combination (-secondCoord) * hrowOne
  have hprodTwo : assembly atomTwo atomOne * secondCoord * firstCoord
      = firstCoord * firstCoord * ((size : ℝ))⁻¹ := by
    linear_combination firstCoord * hrowTwo
  rcases lt_trichotomy (firstCoord * secondCoord) 0 with hsign | hsign | hsign
  · right
    have hsquare : (firstCoord + secondCoord) ^ 2 ≤ 0 := by
      nlinarith [mul_nonneg (neg_pos.mpr hsign).le hplus, hprodOne, hprodTwo,
        hsizePos]
    have hzero : firstCoord + secondCoord = 0 :=
      sq_eq_zero_iff.mp (le_antisymm hsquare (sq_nonneg _))
    linarith
  · exact absurd hsign (mul_ne_zero hone htwo)
  · left
    have hsquare : (firstCoord - secondCoord) ^ 2 ≤ 0 := by
      nlinarith [mul_nonneg hsign.le hminus, hprodOne, hprodTwo, hsizePos]
    have hzero : firstCoord - secondCoord = 0 :=
      sq_eq_zero_iff.mp (le_antisymm hsquare (sq_nonneg _))
    linarith

/-- **THE KERNEL INVARIANCE.**  Commutation keeps the assembly kernel
under the projection. -/
theorem assembly_mulVec_projection_pairKernelVec
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {probe : Fin size → ℝ}
    (hker : chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ probe = 0) :
    chartMultiplierAssembly activeSet activeWeight tightDir
        *ᵥ (projection *ᵥ probe) = 0 := by
  rw [Matrix.mulVec_mulVec, ← hdata.assembly_commutes, ← Matrix.mulVec_mulVec,
    hker, Matrix.mulVec_zero]

end Gtz
