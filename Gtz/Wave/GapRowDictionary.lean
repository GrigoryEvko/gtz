import Gtz.Wave.ParallelConcentrationLayer

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The gap row dictionary — eigen rows, range invariance, and column reads

The both-parallel probes show the pair-plane invariants: across the whole
witness family the gap vanishes between the two single atoms, the two
diagonal entries agree, and the pair block dominates the value with the
uniform margin.  These invariants are consequences of three structure
layers, and this file lands all three at the abstract datum, generic over
the basis count so the laws transfer to the higher ranks.

The layers:

1. **The gap row dictionary.**  Tightness in entry form: the gap row of a
   block atom against its direction sums to the value multiple.  The
   triple-collapsed form turns a card-3 support into three explicit
   entries — the shape a polynomial certificate consumes.
2. **The range invariance.**  The commutation moves the projection through
   the assembly range.  A coordinate single inside the range keeps its gap
   image inside the range: the diagonal acts on a single as a scalar.
3. **The span bridge and the column reads.**  A four-direction combination
   is a span member, a span member of the assembly range has a coefficient
   vector over the basis, and the gap column of an in-span single is
   readable through the basis at EVERY row.  Composed with the
   concentration capstone, both gap columns of the single-atom pair of a
   both-parallel C4 configuration become basis-readable.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.gap_row_eigen_sum`, `Gtz.gap_row_eigen_triple` — **THE ROW
  DICTIONARY.**
* `Gtz.mulVec_mem_range_of_commutes`,
  `Gtz.single_mem_range_of_smul_single_mem`,
  `Gtz.gap_mulVec_single_mem_range` — **THE RANGE INVARIANCE.**
* `Gtz.mem_span_range_of_four_direction_combination`,
  `Gtz.exists_coeff_sum_of_mem_span` — **THE SPAN BRIDGE.**
* `Gtz.exists_gapColumn_coeff_of_single_mem` — **THE COLUMN READ.**
* `Gtz.sum_collapse_one`, `Gtz.sum_collapse_two`,
  `Gtz.gapColumn_read_one_carrier`, `Gtz.gapColumn_read_two_carriers` —
  **THE COLLAPSE CALCULUS** with the evaluated reads.
* `Gtz.gap_entry_symm`, `Gtz.gap_row_eigen_pair` — the symmetry entries
  and the branch-(A) pair row dictionary.
* `Gtz.projection_entry_symm`, `Gtz.projection_entry_eq_gap_add`,
  `Gtz.projection_row_square`, `Gtz.projection_offdiag_square`,
  `Gtz.projection_row_product` — **THE ROW SQUARES**, the quadratic
  supply of the disjunctive certificate.
* `Gtz.bothParallel_gapColumn_reads` — **THE PAIR-PLANE READS** at the
  both-parallel C4 configuration.

The pair-plane invariants the probes measured (the vanishing gap entry
between the single atoms, the equal pair diagonals, the uniform pair
margin) are consequences of this system: the two column reads, the four
eigen rows through the pair, the row squares, and the symmetry.  The
four-way disjunctive certificate composes these with the ceiling.

## Vacuity

The statements hold at every stationary datum with the stated span and
pattern hypotheses.  Nothing here quantifies over a crux.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## Layer 1 — the gap row dictionary -/

/-- **THE ROW DICTIONARY, SUM FORM.**  Tightness in entry form: the gap
row of a block atom against its direction sums to the value multiple. -/
theorem gap_row_eigen_sum
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomRow : Fin size} (hrow : atomRow ∈ activeSubset label) :
    ∑ atomCol : Fin size,
      chartStationaryGap projection weight atomRow atomCol * tightDir label atomCol
      = value * tightDir label atomRow :=
  hdata.tightDir_isTight label hmem atomRow hrow

/-- **THE ROW DICTIONARY, TRIPLE FORM.**  A card-3 support collapses the
row sum to three explicit gap entries: the shape a polynomial certificate
consumes. -/
theorem gap_row_eigen_triple
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomRow : Fin size} (hrow : atomRow ∈ activeSubset label)
    {atomU atomV atomT : Fin size} (hUV : atomU ≠ atomV) (hUT : atomU ≠ atomT)
    (hVT : atomV ≠ atomT)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomT → tightDir label atomIndex = 0) :
    chartStationaryGap projection weight atomRow atomU * tightDir label atomU
      + chartStationaryGap projection weight atomRow atomV * tightDir label atomV
      + chartStationaryGap projection weight atomRow atomT * tightDir label atomT
      = value * tightDir label atomRow := by
  have hsum := gap_row_eigen_sum hdata hmem hrow
  have hnotU : atomU ∉ ({atomV, atomT} : Finset (Fin size)) := by
    intro hmemU
    rcases Finset.mem_insert.mp hmemU with heq | hmemU'
    · exact hUV heq
    · exact hUT (Finset.mem_singleton.mp hmemU')
  have hnotV : atomV ∉ ({atomT} : Finset (Fin size)) := fun hmemV =>
    hVT (Finset.mem_singleton.mp hmemV)
  have hrestrict : ∑ atomCol : Fin size,
      chartStationaryGap projection weight atomRow atomCol
        * tightDir label atomCol
      = ∑ atomCol ∈ ({atomU, atomV, atomT} : Finset (Fin size)),
          chartStationaryGap projection weight atomRow atomCol
            * tightDir label atomCol := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro atomCol _ hnot
    obtain ⟨hcu, hcv, hct⟩ := notMem_triple.mp hnot
    rw [hsupp atomCol hcu hcv hct, mul_zero]
  rw [hrestrict, Finset.sum_insert hnotU, Finset.sum_insert hnotV,
    Finset.sum_singleton] at hsum
  linarith [hsum]

/-! ## Layer 2 — the range invariance -/

/-- **THE RANGE INVARIANCE.**  A matrix that commutes with the assembly
moves vectors inside the assembly range. -/
theorem mulVec_mem_range_of_commutes
    {commuting assembly : Matrix (Fin size) (Fin size) ℝ}
    (hcomm : commuting * assembly = assembly * commuting)
    {ambientVec : Fin size → ℝ}
    (hmem : ambientVec ∈ LinearMap.range (Matrix.toLin' assembly)) :
    commuting *ᵥ ambientVec ∈ LinearMap.range (Matrix.toLin' assembly) := by
  obtain ⟨preVec, hpre⟩ := hmem
  refine ⟨commuting *ᵥ preVec, ?_⟩
  rw [Matrix.toLin'_apply] at hpre ⊢
  rw [← hpre, Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec]

/-- A nonzero multiple of a single inside the range puts the single itself
inside the range. -/
theorem single_mem_range_of_smul_single_mem
    {assembly : Matrix (Fin size) (Fin size) ℝ}
    {scale : ℝ} (hscale : scale ≠ 0) {atomB : Fin size}
    (hmem : scale • (Pi.single atomB 1 : Fin size → ℝ)
      ∈ LinearMap.range (Matrix.toLin' assembly)) :
    (Pi.single atomB 1 : Fin size → ℝ)
      ∈ LinearMap.range (Matrix.toLin' assembly) := by
  have hsmul := Submodule.smul_mem (LinearMap.range (Matrix.toLin' assembly))
    scale⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hscale, one_smul] at hsmul

/-- The diagonal acts on a single as a scalar. -/
theorem diagonal_mulVec_single_eq_smul (weightVec : Fin size → ℝ)
    (atomB : Fin size) :
    Matrix.diagonal weightVec *ᵥ (Pi.single atomB 1 : Fin size → ℝ)
      = weightVec atomB • (Pi.single atomB 1 : Fin size → ℝ) := by
  funext atomIndex
  rw [Matrix.mulVec_diagonal]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hb : atomIndex = atomB
  · rw [hb]
  · rw [Pi.single_eq_of_ne hb, mul_zero, mul_zero]

/-- **THE GAP IMAGE OF AN IN-RANGE SINGLE.**  The commutation moves the
projection through the range, and the diagonal acts as a scalar: the gap
column of an in-range single stays inside the range. -/
theorem gap_mulVec_single_mem_range
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {atomB : Fin size}
    (hmem : (Pi.single atomB 1 : Fin size → ℝ)
      ∈ LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir))) :
    chartStationaryGap projection weight *ᵥ (Pi.single atomB 1 : Fin size → ℝ)
      ∈ LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir)) := by
  have hproj := mulVec_mem_range_of_commutes hdata.assembly_commutes hmem
  rw [chartStationaryGap, Matrix.sub_mulVec,
    diagonal_mulVec_single_eq_smul weight atomB]
  exact Submodule.sub_mem _ hproj (Submodule.smul_mem _ _ hmem)

/-! ## Layer 3 — the span bridge -/

/-- A four-direction combination is a span member. -/
theorem mem_span_range_of_four_direction_combination
    (basisLabel : Fin basisCount → activeIndex)
    {slotA slotB slotC slotD : Fin basisCount}
    {coeffA coeffB coeffC coeffD : ℝ} {ambientVec : Fin size → ℝ}
    (hcomb : coeffA • tightDir (basisLabel slotA)
        + coeffB • tightDir (basisLabel slotB)
        + coeffC • tightDir (basisLabel slotC)
        + coeffD • tightDir (basisLabel slotD) = ambientVec) :
    ambientVec ∈ Submodule.span ℝ
      (Set.range fun slotIndex => tightDir (basisLabel slotIndex)) := by
  rw [← hcomb]
  refine Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨slotA, rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨slotB, rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨slotC, rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨slotD, rfl⟩)

/-- A span member over the basis directions has a coefficient vector. -/
theorem exists_coeff_sum_of_mem_span
    (basisLabel : Fin basisCount → activeIndex) {ambientVec : Fin size → ℝ}
    (hmem : ambientVec ∈ Submodule.span ℝ
      (Set.range fun slotIndex => tightDir (basisLabel slotIndex))) :
    ∃ coeff : Fin basisCount → ℝ,
      ∑ slotIndex, coeff slotIndex • tightDir (basisLabel slotIndex)
        = ambientVec := by
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  exact hmem

/-! ## The column read -/

/-- **THE COLUMN READ.**  When a nonzero multiple of a coordinate single
lies in the span of the basis directions, and the span is the assembly
range, the gap column of the single is basis-readable at every row. -/
theorem exists_gapColumn_coeff_of_single_mem
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hspan : Submodule.span ℝ
        (Set.range fun slotIndex => tightDir (basisLabel slotIndex))
      = LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir)))
    {scale : ℝ} (hscale : scale ≠ 0) {atomB : Fin size}
    (hsingle : scale • (Pi.single atomB 1 : Fin size → ℝ)
      ∈ Submodule.span ℝ
        (Set.range fun slotIndex => tightDir (basisLabel slotIndex))) :
    ∃ coeff : Fin basisCount → ℝ, ∀ atomRow : Fin size,
      ∑ slotIndex, coeff slotIndex * tightDir (basisLabel slotIndex) atomRow
        = chartStationaryGap projection weight atomRow atomB := by
  rw [hspan] at hsingle
  have hsingleMem := single_mem_range_of_smul_single_mem hscale hsingle
  have hgapMem := gap_mulVec_single_mem_range hdata hsingleMem
  rw [← hspan] at hgapMem
  obtain ⟨coeff, hcoeff⟩ := exists_coeff_sum_of_mem_span basisLabel hgapMem
  refine ⟨coeff, fun atomRow => ?_⟩
  have hentry := congrFun hcoeff atomRow
  rw [Finset.sum_apply] at hentry
  simp only [Pi.smul_apply, smul_eq_mul] at hentry
  rw [hentry, Matrix.mulVec_single_one]
  simp [Matrix.col]

/-! ## The collapse calculus and the evaluated reads -/

/-- A slot sum with one surviving slot collapses to that slot. -/
theorem sum_collapse_one {termOf : Fin basisCount → ℝ} {slotK : Fin basisCount}
    (hvanish : ∀ slotIndex, slotIndex ≠ slotK → termOf slotIndex = 0) :
    ∑ slotIndex, termOf slotIndex = termOf slotK := by
  rw [Finset.sum_eq_single slotK (fun slotIndex _ hne => hvanish slotIndex hne)
    (fun hnot => absurd (Finset.mem_univ _) hnot)]

/-- A slot sum with two surviving slots collapses to the pair. -/
theorem sum_collapse_two {termOf : Fin basisCount → ℝ}
    {slotK slotL : Fin basisCount} (hKL : slotK ≠ slotL)
    (hvanish : ∀ slotIndex, slotIndex ≠ slotK → slotIndex ≠ slotL →
      termOf slotIndex = 0) :
    ∑ slotIndex, termOf slotIndex = termOf slotK + termOf slotL := by
  have hrestrict : ∑ slotIndex, termOf slotIndex
      = ∑ slotIndex ∈ ({slotK, slotL} : Finset (Fin basisCount)),
          termOf slotIndex := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro slotIndex _ hnot
    refine hvanish slotIndex ?_ ?_
    · intro heq
      exact hnot (heq ▸ Finset.mem_insert_self _ _)
    · intro heq
      exact hnot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [hrestrict, Finset.sum_pair hKL]

/-- **THE EVALUATED READ, ONE CARRIER.**  A basis-readable gap column
evaluated at a row where one slot carries: one product equals the
entry. -/
theorem gapColumn_read_one_carrier
    (basisLabel : Fin basisCount → activeIndex)
    {gapColumnCoeff : Fin basisCount → ℝ} {atomB : Fin size}
    (hread : ∀ atomRow : Fin size,
      ∑ slotIndex, gapColumnCoeff slotIndex
          * tightDir (basisLabel slotIndex) atomRow
        = chartStationaryGap projection weight atomRow atomB)
    {atomRow : Fin size} {slotK : Fin basisCount}
    (hvanish : ∀ slotIndex, slotIndex ≠ slotK →
      tightDir (basisLabel slotIndex) atomRow = 0) :
    gapColumnCoeff slotK * tightDir (basisLabel slotK) atomRow
      = chartStationaryGap projection weight atomRow atomB := by
  have hcollapse := sum_collapse_one (termOf := fun slotIndex =>
    gapColumnCoeff slotIndex * tightDir (basisLabel slotIndex) atomRow)
    (fun slotIndex hne => by rw [hvanish slotIndex hne, mul_zero])
  rw [← hread atomRow, hcollapse]

/-- **THE EVALUATED READ, TWO CARRIERS.**  A basis-readable gap column
evaluated at a row where two slots carry: two products equal the entry.
Every atom of the C4 shape has exactly two carriers, thus this read
covers every row of the pair-plane system. -/
theorem gapColumn_read_two_carriers
    (basisLabel : Fin basisCount → activeIndex)
    {gapColumnCoeff : Fin basisCount → ℝ} {atomB : Fin size}
    (hread : ∀ atomRow : Fin size,
      ∑ slotIndex, gapColumnCoeff slotIndex
          * tightDir (basisLabel slotIndex) atomRow
        = chartStationaryGap projection weight atomRow atomB)
    {atomRow : Fin size} {slotK slotL : Fin basisCount} (hKL : slotK ≠ slotL)
    (hvanish : ∀ slotIndex, slotIndex ≠ slotK → slotIndex ≠ slotL →
      tightDir (basisLabel slotIndex) atomRow = 0) :
    gapColumnCoeff slotK * tightDir (basisLabel slotK) atomRow
      + gapColumnCoeff slotL * tightDir (basisLabel slotL) atomRow
      = chartStationaryGap projection weight atomRow atomB := by
  have hcollapse := sum_collapse_two hKL (termOf := fun slotIndex =>
    gapColumnCoeff slotIndex * tightDir (basisLabel slotIndex) atomRow)
    (fun slotIndex hK hL => by rw [hvanish slotIndex hK hL, mul_zero])
  rw [← hread atomRow, hcollapse]

/-! ## The gap symmetry entries and the pair row dictionary -/

/-- The gap is symmetric in entries at every symmetric chart. -/
theorem gap_entry_symm
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (atomRow atomCol : Fin size) :
    chartStationaryGap projection weight atomRow atomCol
      = chartStationaryGap projection weight atomCol atomRow := by
  have hentry := congrFun (congrFun
    (chartStationaryGap_transpose (weight := weight) hdata.isSymmetric) atomCol)
    atomRow
  rw [Matrix.transpose_apply] at hentry
  exact hentry

/-- **THE ROW DICTIONARY, PAIR FORM.**  A card-2 support collapses the row
sum to two explicit gap entries.  This is the branch-(A) shape: a
support-two direction feeds a two-entry eigen system at every block
row. -/
theorem gap_row_eigen_pair
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomRow : Fin size} (hrow : atomRow ∈ activeSubset label)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    chartStationaryGap projection weight atomRow atomU * tightDir label atomU
      + chartStationaryGap projection weight atomRow atomV * tightDir label atomV
      = value * tightDir label atomRow := by
  have hsum := gap_row_eigen_sum hdata hmem hrow
  have hrestrict : ∑ atomCol : Fin size,
      chartStationaryGap projection weight atomRow atomCol
        * tightDir label atomCol
      = ∑ atomCol ∈ ({atomU, atomV} : Finset (Fin size)),
          chartStationaryGap projection weight atomRow atomCol
            * tightDir label atomCol := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro atomCol _ hnot
    refine ?_
    have hcu : atomCol ≠ atomU := fun heq =>
      hnot (heq ▸ Finset.mem_insert_self _ _)
    have hcv : atomCol ≠ atomV := fun heq =>
      hnot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [hsupp atomCol hcu hcv, mul_zero]
  rw [hrestrict, Finset.sum_pair hUV] at hsum
  exact hsum

/-! ## The idempotency row squares -/

/-- The chart entries are symmetric. -/
theorem projection_entry_symm
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (atomRow atomCol : Fin size) :
    projection atomRow atomCol = projection atomCol atomRow := by
  have hentry := congrFun (congrFun hdata.isSymmetric atomCol) atomRow
  rw [Matrix.transpose_apply] at hentry
  exact hentry

/-- The chart entry is the gap entry plus the diagonal weight. -/
theorem projection_entry_eq_gap_add
    (atomRow atomCol : Fin size) :
    projection atomRow atomCol
      = chartStationaryGap projection weight atomRow atomCol
        + if atomRow = atomCol then weight atomRow else 0 := by
  rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply]
  ring

/-- **THE ROW SQUARE.**  Idempotency with symmetry prices every row of the
chart: the sum of the squared row entries is the diagonal entry.  This is
the quadratic supply of the disjunctive ceiling certificate. -/
theorem projection_row_square
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (atomRow : Fin size) :
    ∑ atomCol : Fin size,
      projection atomRow atomCol * projection atomRow atomCol
      = projection atomRow atomRow := by
  have hentry := congrFun (congrFun hdata.isIdempotent atomRow) atomRow
  rw [Matrix.mul_apply] at hentry
  rw [← hentry]
  refine Finset.sum_congr rfl fun atomCol _ => ?_
  rw [projection_entry_symm hdata atomCol atomRow]

/-- **THE OFF-DIAGONAL SQUARE MASS.**  The squared off-diagonal row mass
is the diagonal entry times its complement: the row square with the
diagonal term removed. -/
theorem projection_offdiag_square
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (atomRow : Fin size) :
    ∑ atomCol ∈ Finset.univ.erase atomRow,
      projection atomRow atomCol * projection atomRow atomCol
      = projection atomRow atomRow
        - projection atomRow atomRow * projection atomRow atomRow := by
  have hsquare := projection_row_square hdata atomRow
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ atomRow)] at hsquare
  linarith [hsquare]

/-- The cross-square mass between two rows: idempotency prices the mixed
row product as the corresponding entry.  The certificate consumes the
rows of the two single atoms. -/
theorem projection_row_product
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (atomRow atomRow' : Fin size) :
    ∑ atomCol : Fin size,
      projection atomRow atomCol * projection atomRow' atomCol
      = projection atomRow atomRow' := by
  have hentry := congrFun (congrFun hdata.isIdempotent atomRow) atomRow'
  rw [Matrix.mul_apply] at hentry
  rw [← hentry]
  refine Finset.sum_congr rfl fun atomCol _ => ?_
  rw [projection_entry_symm hdata atomCol atomRow']

/-! ## The pair-plane reads at the both-parallel configuration -/

/-- **THE PAIR-PLANE READS.**  At every both-parallel C4 configuration
with dense blocks, a left inverse, and the span law, BOTH gap columns of
the single-atom pair are basis-readable at every row.  This is the entry
supply of the four-way disjunctive ceiling certificate. -/
theorem bothParallel_gapColumn_reads
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {L : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    (hspan : Submodule.span ℝ
        (Set.range fun slotIndex => tightDir (basisLabel slotIndex))
      = LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir)))
    {slotA slotB slotC slotD : Fin basisCount}
    (hCA : slotC ≠ slotA) (hCB : slotC ≠ slotB) (hCD : slotC ≠ slotD)
    {atomA1 atomA2 atomB atomC1 atomC2 atomD : Fin size}
    (hBA1 : atomB ≠ atomA1) (hBA2 : atomB ≠ atomA2) (hBD : atomB ≠ atomD)
    (hdetAB : tightDir (basisLabel slotA) atomA1
        * tightDir (basisLabel slotB) atomA2
      - tightDir (basisLabel slotA) atomA2
        * tightDir (basisLabel slotB) atomA1 = 0)
    (hdetCD : tightDir (basisLabel slotC) atomC1
        * tightDir (basisLabel slotD) atomC2
      - tightDir (basisLabel slotC) atomC2
        * tightDir (basisLabel slotD) atomC1 = 0)
    (hsuppA : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomD → tightDir (basisLabel slotA) atomIndex = 0)
    (hsuppB : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomB → tightDir (basisLabel slotB) atomIndex = 0)
    (hsuppC : ∀ atomIndex, atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
      atomIndex ≠ atomB → tightDir (basisLabel slotC) atomIndex = 0)
    (hsuppD : ∀ atomIndex, atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
      atomIndex ≠ atomD → tightDir (basisLabel slotD) atomIndex = 0)
    (hqAa1 : tightDir (basisLabel slotA) atomA1 ≠ 0)
    (hqBb : tightDir (basisLabel slotB) atomB ≠ 0)
    (hqDc1 : tightDir (basisLabel slotD) atomC1 ≠ 0) :
    (∃ coeff : Fin basisCount → ℝ, ∀ atomRow : Fin size,
      ∑ slotIndex, coeff slotIndex * tightDir (basisLabel slotIndex) atomRow
        = chartStationaryGap projection weight atomRow atomB)
    ∧ ∃ coeff : Fin basisCount → ℝ, ∀ atomRow : Fin size,
      ∑ slotIndex, coeff slotIndex * tightDir (basisLabel slotIndex) atomRow
        = chartStationaryGap projection weight atomRow atomD := by
  obtain ⟨scale, hscale, ⟨coeffAB, coeffBB, coeffCB, coeffDB, hcombB⟩,
    coeffAD, coeffBD, coeffCD', coeffDD, hcombD⟩ :=
    bothParallel_single_exports basisLabel hleft hCA hCB hCD hBA1 hBA2 hBD
      hdetAB hdetCD hsuppA hsuppB hsuppC hsuppD hqAa1 hqBb hqDc1
  constructor
  · exact exists_gapColumn_coeff_of_single_mem hdata basisLabel hspan hscale
      (mem_span_range_of_four_direction_combination basisLabel hcombB)
  · exact exists_gapColumn_coeff_of_single_mem hdata basisLabel hspan hscale
      (mem_span_range_of_four_direction_combination basisLabel hcombD)

end Gtz
