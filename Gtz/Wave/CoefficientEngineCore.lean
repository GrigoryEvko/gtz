import Gtz.Wave.SupportTwoClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The coefficient engine core — the shared skeleton of the commutation kills

The drop probes located closures one, three, and four at the same
structural ingredient: commutation.  In the coefficient frame commutation
supplies the representation, the representation supplies idempotency and
the carried rows, and the carried rows price every two-carrier product.
This module lands the shared skeleton as exact scalar laws, ready for the
three payloads.

The layers:

1. **The idempotency products.**  A diagonal entry of an idempotent matrix
   is the sum of its row-column products, and the off-diagonal part reads
   `T (1 - T)`.
2. **The division-free pricing.**  Two collapsed carried rows at a
   two-carrier atom price the opposite product exactly:
   `M_ij M_ji = (d - T_i)(d - T_j)`.  The carrier coordinates cancel, and
   no ratio appears.
3. **The doubled-pair dichotomy.**  Two atoms pricing the same product
   force equal shifted weights or the exact corner trace
   `T_i + T_j = d + d'`.
4. **The second symmetric function.**  A four-by-four idempotent with
   trace two has `e2 = 1`: the six corner determinants sum to one.
5. **The master identities.**  On the complete pattern the six pricings
   turn `e2 = 1` into `Σ T_i D_i = 1 + Σ d_e²`.  On the doubled cycle the
   two uncarried products stay explicit.  The vertex equations localize
   idempotency per slot, on the complete pattern and on the cycle.
6. **The exchange entries.**  The exchange law read entrywise, generic and
   in the expanded four-slot form.

The vertex probe verdicts that shaped this module: the doubled-cycle
vertex system alone is FEASIBLE, thus the cycle kill must consume the
exchange layer.  The complete-pattern vertex system escapes only through
one heavy edge with the value near zero, thus the complete kill needs a
wedge that is uniform in the value.  Both continuations consume the laws
below unchanged.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.sum_products_eq_diag_of_idempotent`,
  `Gtz.offdiag_products_eq_of_idempotent`,
  `Gtz.trace_fin_four_eq` — **LAYER 1.**
* `Gtz.two_carrier_product_pricing` — **LAYER 2.**
* `Gtz.doubled_pair_dichotomy` — **LAYER 3.**
* `Gtz.e2_eq_one_of_idempotent_trace_two` — **LAYER 4.**
* `Gtz.kfour_master_identity`, the four `Gtz.kfour_vertex_equation_*`,
  `Gtz.cfour_master_identity`, the four `Gtz.cfour_vertex_equation_*` —
  **LAYER 5.**
* `Gtz.exchange_entry_eq`, `Gtz.exchange_entry_fin_four` — **LAYER 6.**

## Vacuity

Every statement is a scalar or matrix identity with explicit hypotheses.
Nothing quantifies over a crux.
-/

namespace Gtz

open Matrix

variable {basisCount : ℕ}

/-! ## Layer 1 — the idempotency products -/

/-- A diagonal entry of an idempotent matrix is the sum of its row-column
products. -/
theorem sum_products_eq_diag_of_idempotent
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hM : M * M = M) (slotIndex : Fin basisCount) :
    ∑ innerIndex : Fin basisCount,
        M slotIndex innerIndex * M innerIndex slotIndex
      = M slotIndex slotIndex := by
  have hentry := congrFun (congrFun hM slotIndex) slotIndex
  rw [Matrix.mul_apply] at hentry
  exact hentry

/-- The off-diagonal products of an idempotent matrix read `T (1 - T)` at
each diagonal entry. -/
theorem offdiag_products_eq_of_idempotent
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hM : M * M = M) (slotIndex : Fin basisCount) :
    ∑ innerIndex ∈ Finset.univ.erase slotIndex,
        M slotIndex innerIndex * M innerIndex slotIndex
      = M slotIndex slotIndex
        - M slotIndex slotIndex * M slotIndex slotIndex := by
  have hsum := sum_products_eq_diag_of_idempotent hM slotIndex
  have hsplit : M slotIndex slotIndex * M slotIndex slotIndex
      + ∑ innerIndex ∈ Finset.univ.erase slotIndex,
          M slotIndex innerIndex * M innerIndex slotIndex
      = ∑ innerIndex : Fin basisCount,
          M slotIndex innerIndex * M innerIndex slotIndex :=
    Finset.add_sum_erase Finset.univ
      (fun innerIndex => M slotIndex innerIndex * M innerIndex slotIndex)
      (Finset.mem_univ slotIndex)
  rw [hsum] at hsplit
  linarith

/-- The four-slot trace, expanded to the diagonal entries. -/
theorem trace_fin_four_eq (M : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix.trace M = M 0 0 + M 1 1 + M 2 2 + M 3 3 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_four]

/-! ## Layer 2 — the division-free pricing -/

/-- **THE PRICING.**  Two collapsed carried rows at a two-carrier atom
price the opposite product with no division: the carrier coordinates
cancel against each other. -/
theorem two_carrier_product_pricing
    {firstCoord secondCoord shifted : ℝ}
    {Mii Mij Mji Mjj : ℝ}
    (hfirst : firstCoord ≠ 0) (hsecond : secondCoord ≠ 0)
    (hrowFirst : firstCoord * Mii + secondCoord * Mji
      = shifted * firstCoord)
    (hrowSecond : firstCoord * Mij + secondCoord * Mjj
      = shifted * secondCoord) :
    Mij * Mji = (shifted - Mii) * (shifted - Mjj) := by
  have hone : secondCoord * Mji = firstCoord * (shifted - Mii) := by
    linear_combination hrowFirst
  have htwo : firstCoord * Mij = secondCoord * (shifted - Mjj) := by
    linear_combination hrowSecond
  have hkey : firstCoord * secondCoord * (Mij * Mji)
      = firstCoord * secondCoord * ((shifted - Mii) * (shifted - Mjj)) := by
    linear_combination (firstCoord * Mij) * hone
      + (firstCoord * (shifted - Mii)) * htwo
  exact mul_left_cancel₀ (mul_ne_zero hfirst hsecond) hkey

/-! ## Layer 3 — the doubled-pair dichotomy -/

/-- **THE DICHOTOMY.**  Two atoms pricing the same product force equal
shifted weights or the exact corner trace. -/
theorem doubled_pair_dichotomy
    {firstShifted secondShifted Ti Tj : ℝ} {product : ℝ}
    (hfirst : product = (firstShifted - Ti) * (firstShifted - Tj))
    (hsecond : product = (secondShifted - Ti) * (secondShifted - Tj)) :
    firstShifted = secondShifted
      ∨ Ti + Tj = firstShifted + secondShifted := by
  have hzero : (firstShifted - secondShifted)
      * (firstShifted + secondShifted - Ti - Tj) = 0 := by
    linear_combination hsecond - hfirst
  rcases mul_eq_zero.mp hzero with hleft | hright
  · exact Or.inl (sub_eq_zero.mp hleft)
  · exact Or.inr (by linarith)

/-! ## Layer 4 — the second symmetric function -/

/-- **`e2 = 1`.**  A four-by-four idempotent with trace two has second
symmetric function one: the six corner determinants sum to one. -/
theorem e2_eq_one_of_idempotent_trace_two
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : M * M = M) (htrace : Matrix.trace M = 2) :
    (M 0 0 * M 1 1 - M 0 1 * M 1 0) + (M 0 0 * M 2 2 - M 0 2 * M 2 0)
      + (M 0 0 * M 3 3 - M 0 3 * M 3 0) + (M 1 1 * M 2 2 - M 1 2 * M 2 1)
      + (M 1 1 * M 3 3 - M 1 3 * M 3 1) + (M 2 2 * M 3 3 - M 2 3 * M 3 2)
      = 1 := by
  have htr : M 0 0 + M 1 1 + M 2 2 + M 3 3 = 2 := by
    rw [← trace_fin_four_eq M]
    exact htrace
  have hzero := sum_products_eq_diag_of_idempotent hM 0
  have hone := sum_products_eq_diag_of_idempotent hM 1
  have htwo := sum_products_eq_diag_of_idempotent hM 2
  have hthree := sum_products_eq_diag_of_idempotent hM 3
  rw [Fin.sum_univ_four] at hzero hone htwo hthree
  linear_combination ((M 0 0 + M 1 1 + M 2 2 + M 3 3 + 1) / 2) * htr
    - (1 / 2 : ℝ) * hzero - (1 / 2 : ℝ) * hone - (1 / 2 : ℝ) * htwo
    - (1 / 2 : ℝ) * hthree

/-! ## Layer 5 — the master identities and the vertex equations -/

/-- **THE COMPLETE MASTER IDENTITY.**  On the complete pattern the six
pricings turn `e2 = 1` into the weighted vertex sum
`Σ T_i D_i = 1 + Σ d_e²`. -/
theorem kfour_master_identity
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : M * M = M) (htrace : Matrix.trace M = 2)
    {d01 d02 d03 d12 d13 d23 : ℝ}
    (h01 : M 0 1 * M 1 0 = (d01 - M 0 0) * (d01 - M 1 1))
    (h02 : M 0 2 * M 2 0 = (d02 - M 0 0) * (d02 - M 2 2))
    (h03 : M 0 3 * M 3 0 = (d03 - M 0 0) * (d03 - M 3 3))
    (h12 : M 1 2 * M 2 1 = (d12 - M 1 1) * (d12 - M 2 2))
    (h13 : M 1 3 * M 3 1 = (d13 - M 1 1) * (d13 - M 3 3))
    (h23 : M 2 3 * M 3 2 = (d23 - M 2 2) * (d23 - M 3 3)) :
    M 0 0 * (d01 + d02 + d03) + M 1 1 * (d01 + d12 + d13)
      + M 2 2 * (d02 + d12 + d23) + M 3 3 * (d03 + d13 + d23)
      = 1 + (d01 * d01 + d02 * d02 + d03 * d03 + d12 * d12 + d13 * d13
        + d23 * d23) := by
  have he2 := e2_eq_one_of_idempotent_trace_two hM htrace
  linear_combination he2 + h01 + h02 + h03 + h12 + h13 + h23

/-- **THE CYCLE MASTER IDENTITY.**  On the doubled cycle only four pairs
carry atoms, and the two uncarried products stay explicit on the left. -/
theorem cfour_master_identity
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : M * M = M) (htrace : Matrix.trace M = 2)
    {d01 d12 d23 d30 : ℝ}
    (h01 : M 0 1 * M 1 0 = (d01 - M 0 0) * (d01 - M 1 1))
    (h12 : M 1 2 * M 2 1 = (d12 - M 1 1) * (d12 - M 2 2))
    (h23 : M 2 3 * M 3 2 = (d23 - M 2 2) * (d23 - M 3 3))
    (h30 : M 0 3 * M 3 0 = (d30 - M 3 3) * (d30 - M 0 0)) :
    (d01 * (M 0 0 + M 1 1) - d01 * d01) + (d12 * (M 1 1 + M 2 2) - d12 * d12)
      + (d23 * (M 2 2 + M 3 3) - d23 * d23)
      + (d30 * (M 3 3 + M 0 0) - d30 * d30)
      + (M 0 0 * M 2 2 - M 0 2 * M 2 0) + (M 1 1 * M 3 3 - M 1 3 * M 3 1)
      = 1 := by
  have he2 := e2_eq_one_of_idempotent_trace_two hM htrace
  linear_combination he2 + h01 + h12 + h23 + h30

/-- **THE VERTEX EQUATION** at the zeroth slot of the complete pattern:
the three pricings at the slot localize idempotency to the shifted
weights. -/
theorem kfour_vertex_equation_zero
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : M * M = M)
    {d01 d02 d03 : ℝ}
    (h01 : M 0 1 * M 1 0 = (d01 - M 0 0) * (d01 - M 1 1))
    (h02 : M 0 2 * M 2 0 = (d02 - M 0 0) * (d02 - M 2 2))
    (h03 : M 0 3 * M 3 0 = (d03 - M 0 0) * (d03 - M 3 3)) :
    M 0 0 - M 0 0 * M 0 0
      = (d01 - M 0 0) * (d01 - M 1 1) + (d02 - M 0 0) * (d02 - M 2 2)
        + (d03 - M 0 0) * (d03 - M 3 3) := by
  have hsum := sum_products_eq_diag_of_idempotent hM 0
  rw [Fin.sum_univ_four] at hsum
  linear_combination h01 + h02 + h03 - hsum

/-- The vertex equation at the first slot of the complete pattern. -/
theorem kfour_vertex_equation_one
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : M * M = M)
    {d01 d12 d13 : ℝ}
    (h01 : M 0 1 * M 1 0 = (d01 - M 0 0) * (d01 - M 1 1))
    (h12 : M 1 2 * M 2 1 = (d12 - M 1 1) * (d12 - M 2 2))
    (h13 : M 1 3 * M 3 1 = (d13 - M 1 1) * (d13 - M 3 3)) :
    M 1 1 - M 1 1 * M 1 1
      = (d01 - M 0 0) * (d01 - M 1 1) + (d12 - M 1 1) * (d12 - M 2 2)
        + (d13 - M 1 1) * (d13 - M 3 3) := by
  have hsum := sum_products_eq_diag_of_idempotent hM 1
  rw [Fin.sum_univ_four] at hsum
  linear_combination h01 + h12 + h13 - hsum

/-- The vertex equation at the second slot of the complete pattern. -/
theorem kfour_vertex_equation_two
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : M * M = M)
    {d02 d12 d23 : ℝ}
    (h02 : M 0 2 * M 2 0 = (d02 - M 0 0) * (d02 - M 2 2))
    (h12 : M 1 2 * M 2 1 = (d12 - M 1 1) * (d12 - M 2 2))
    (h23 : M 2 3 * M 3 2 = (d23 - M 2 2) * (d23 - M 3 3)) :
    M 2 2 - M 2 2 * M 2 2
      = (d02 - M 0 0) * (d02 - M 2 2) + (d12 - M 1 1) * (d12 - M 2 2)
        + (d23 - M 2 2) * (d23 - M 3 3) := by
  have hsum := sum_products_eq_diag_of_idempotent hM 2
  rw [Fin.sum_univ_four] at hsum
  linear_combination h02 + h12 + h23 - hsum

/-- The vertex equation at the third slot of the complete pattern. -/
theorem kfour_vertex_equation_three
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : M * M = M)
    {d03 d13 d23 : ℝ}
    (h03 : M 0 3 * M 3 0 = (d03 - M 0 0) * (d03 - M 3 3))
    (h13 : M 1 3 * M 3 1 = (d13 - M 1 1) * (d13 - M 3 3))
    (h23 : M 2 3 * M 3 2 = (d23 - M 2 2) * (d23 - M 3 3)) :
    M 3 3 - M 3 3 * M 3 3
      = (d03 - M 0 0) * (d03 - M 3 3) + (d13 - M 1 1) * (d13 - M 3 3)
        + (d23 - M 2 2) * (d23 - M 3 3) := by
  have hsum := sum_products_eq_diag_of_idempotent hM 3
  rw [Fin.sum_univ_four] at hsum
  linear_combination h03 + h13 + h23 - hsum

/-- **THE CYCLE VERTEX EQUATION** at the zeroth slot: two priced products
and one explicit product. -/
theorem cfour_vertex_equation_zero
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : M * M = M)
    {d01 d30 : ℝ}
    (h01 : M 0 1 * M 1 0 = (d01 - M 0 0) * (d01 - M 1 1))
    (h30 : M 0 3 * M 3 0 = (d30 - M 3 3) * (d30 - M 0 0)) :
    M 0 0 - M 0 0 * M 0 0
      = (d01 - M 0 0) * (d01 - M 1 1) + M 0 2 * M 2 0
        + (d30 - M 3 3) * (d30 - M 0 0) := by
  have hsum := sum_products_eq_diag_of_idempotent hM 0
  rw [Fin.sum_univ_four] at hsum
  linear_combination h01 + h30 - hsum

/-- The cycle vertex equation at the first slot. -/
theorem cfour_vertex_equation_one
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : M * M = M)
    {d01 d12 : ℝ}
    (h01 : M 0 1 * M 1 0 = (d01 - M 0 0) * (d01 - M 1 1))
    (h12 : M 1 2 * M 2 1 = (d12 - M 1 1) * (d12 - M 2 2)) :
    M 1 1 - M 1 1 * M 1 1
      = (d01 - M 0 0) * (d01 - M 1 1) + (d12 - M 1 1) * (d12 - M 2 2)
        + M 1 3 * M 3 1 := by
  have hsum := sum_products_eq_diag_of_idempotent hM 1
  rw [Fin.sum_univ_four] at hsum
  linear_combination h01 + h12 - hsum

/-- The cycle vertex equation at the second slot. -/
theorem cfour_vertex_equation_two
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : M * M = M)
    {d12 d23 : ℝ}
    (h12 : M 1 2 * M 2 1 = (d12 - M 1 1) * (d12 - M 2 2))
    (h23 : M 2 3 * M 3 2 = (d23 - M 2 2) * (d23 - M 3 3)) :
    M 2 2 - M 2 2 * M 2 2
      = M 0 2 * M 2 0 + (d12 - M 1 1) * (d12 - M 2 2)
        + (d23 - M 2 2) * (d23 - M 3 3) := by
  have hsum := sum_products_eq_diag_of_idempotent hM 2
  rw [Fin.sum_univ_four] at hsum
  linear_combination h12 + h23 - hsum

/-- The cycle vertex equation at the third slot. -/
theorem cfour_vertex_equation_three
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : M * M = M)
    {d23 d30 : ℝ}
    (h23 : M 2 3 * M 3 2 = (d23 - M 2 2) * (d23 - M 3 3))
    (h30 : M 0 3 * M 3 0 = (d30 - M 3 3) * (d30 - M 0 0)) :
    M 3 3 - M 3 3 * M 3 3
      = (d30 - M 3 3) * (d30 - M 0 0) + M 1 3 * M 3 1
        + (d23 - M 2 2) * (d23 - M 3 3) := by
  have hsum := sum_products_eq_diag_of_idempotent hM 3
  rw [Fin.sum_univ_four] at hsum
  linear_combination h23 + h30 - hsum

/-! ## Layer 6 — the exchange entries -/

/-- The exchange law, read entrywise: each mixed row of `M H` agrees with
the mirrored row through `H`. -/
theorem exchange_entry_eq
    {M H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hexchange : M * H = H * Mᵀ)
    (rowIndex colIndex : Fin basisCount) :
    ∑ innerIndex : Fin basisCount,
        M rowIndex innerIndex * H innerIndex colIndex
      = ∑ innerIndex : Fin basisCount,
          H rowIndex innerIndex * M colIndex innerIndex := by
  have hentry := congrFun (congrFun hexchange rowIndex) colIndex
  rw [Matrix.mul_apply, Matrix.mul_apply] at hentry
  refine hentry.trans ?_
  refine Finset.sum_congr rfl fun innerIndex _ => ?_
  rw [Matrix.transpose_apply]

/-- The exchange entries in the expanded four-slot form, ready for the
`linear_combination` consumers of the payloads. -/
theorem exchange_entry_fin_four
    {M H : Matrix (Fin 4) (Fin 4) ℝ}
    (hexchange : M * H = H * Mᵀ)
    (rowIndex colIndex : Fin 4) :
    M rowIndex 0 * H 0 colIndex + M rowIndex 1 * H 1 colIndex
      + M rowIndex 2 * H 2 colIndex + M rowIndex 3 * H 3 colIndex
      = H rowIndex 0 * M colIndex 0 + H rowIndex 1 * M colIndex 1
        + H rowIndex 2 * M colIndex 2 + H rowIndex 3 * M colIndex 3 := by
  have hentry := exchange_entry_eq hexchange rowIndex colIndex
  rw [Fin.sum_univ_four, Fin.sum_univ_four] at hentry
  exact hentry

/-! ## Layer 7 — the datum-level bridges -/

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE DATUM PRICING.**  At a two-carrier atom of a stationary datum,
the opposite coefficient product is the shifted-weight pricing of the two
diagonal entries. -/
theorem two_carrier_pricing_of_datum
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {firstSlot secondSlot : Fin basisCount} (hne : firstSlot ≠ secondSlot)
    (hmemFirst : basisLabel firstSlot ∈ activeSet)
    (hmemSecond : basisLabel secondSlot ∈ activeSet)
    {atomIndex : Fin size}
    (hatomFirst : atomIndex ∈ activeSubset (basisLabel firstSlot))
    (hatomSecond : atomIndex ∈ activeSubset (basisLabel secondSlot))
    (hcarriers : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) atomIndex = 0)
    (hfirstNe : tightDir (basisLabel firstSlot) atomIndex ≠ 0)
    (hsecondNe : tightDir (basisLabel secondSlot) atomIndex ≠ 0) :
    M firstSlot secondSlot * M secondSlot firstSlot
      = (value + weight atomIndex - M firstSlot firstSlot)
        * (value + weight atomIndex - M secondSlot secondSlot) := by
  have hrowFirst := two_carrier_row_reading hdata basisLabel hrepresentation
    hne hmemFirst hatomFirst hcarriers
  have hrowSecond := two_carrier_row_reading hdata basisLabel hrepresentation
    hne hmemSecond hatomSecond hcarriers
  exact two_carrier_product_pricing hfirstNe hsecondNe hrowFirst hrowSecond

/-- **THE DATUM DOUBLED DICHOTOMY.**  Two atoms carried by the same slot
pair force equal weights or the exact corner trace. -/
theorem doubled_pair_dichotomy_of_datum
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {firstSlot secondSlot : Fin basisCount} (hne : firstSlot ≠ secondSlot)
    (hmemFirst : basisLabel firstSlot ∈ activeSet)
    (hmemSecond : basisLabel secondSlot ∈ activeSet)
    {firstAtom secondAtom : Fin size}
    (hatomFirstA : firstAtom ∈ activeSubset (basisLabel firstSlot))
    (hatomFirstB : firstAtom ∈ activeSubset (basisLabel secondSlot))
    (hatomSecondA : secondAtom ∈ activeSubset (basisLabel firstSlot))
    (hatomSecondB : secondAtom ∈ activeSubset (basisLabel secondSlot))
    (hcarriersFirst : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) firstAtom = 0)
    (hcarriersSecond : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) secondAtom = 0)
    (hfirstNeA : tightDir (basisLabel firstSlot) firstAtom ≠ 0)
    (hsecondNeA : tightDir (basisLabel secondSlot) firstAtom ≠ 0)
    (hfirstNeB : tightDir (basisLabel firstSlot) secondAtom ≠ 0)
    (hsecondNeB : tightDir (basisLabel secondSlot) secondAtom ≠ 0) :
    weight firstAtom = weight secondAtom
      ∨ M firstSlot firstSlot + M secondSlot secondSlot
        = 2 * value + weight firstAtom + weight secondAtom := by
  have hpriceFirst := two_carrier_pricing_of_datum hdata basisLabel
    hrepresentation hne hmemFirst hmemSecond hatomFirstA hatomFirstB
    hcarriersFirst hfirstNeA hsecondNeA
  have hpriceSecond := two_carrier_pricing_of_datum hdata basisLabel
    hrepresentation hne hmemFirst hmemSecond hatomSecondA hatomSecondB
    hcarriersSecond hfirstNeB hsecondNeB
  rcases doubled_pair_dichotomy hpriceFirst hpriceSecond with heq | htrace
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- **THE DATUM MASTER IDENTITY.**  A literal four-slot basis whose six
slot pairs each carry an atom prices the complete master identity with
the shifted weights of the six atoms. -/
theorem kfour_master_identity_of_datum
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin 4 → activeIndex)
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hM : M * M = M) (htrace : Matrix.trace M = 2)
    (hmemAll : ∀ columnIndex, basisLabel columnIndex ∈ activeSet)
    (edgeAtom : Fin 4 → Fin 4 → Fin size)
    (hatomMem : ∀ firstSlot secondSlot, firstSlot ≠ secondSlot →
      edgeAtom firstSlot secondSlot ∈ activeSubset (basisLabel firstSlot)
      ∧ edgeAtom firstSlot secondSlot ∈ activeSubset (basisLabel secondSlot))
    (hcarriers : ∀ firstSlot secondSlot, firstSlot ≠ secondSlot →
      ∀ columnIndex, columnIndex ≠ firstSlot → columnIndex ≠ secondSlot →
        tightDir (basisLabel columnIndex) (edgeAtom firstSlot secondSlot) = 0)
    (hcoordNe : ∀ firstSlot secondSlot, firstSlot ≠ secondSlot →
      tightDir (basisLabel firstSlot) (edgeAtom firstSlot secondSlot) ≠ 0
      ∧ tightDir (basisLabel secondSlot) (edgeAtom firstSlot secondSlot) ≠ 0) :
    M 0 0 * ((value + weight (edgeAtom 0 1)) + (value + weight (edgeAtom 0 2))
        + (value + weight (edgeAtom 0 3)))
      + M 1 1 * ((value + weight (edgeAtom 0 1)) + (value + weight (edgeAtom 1 2))
        + (value + weight (edgeAtom 1 3)))
      + M 2 2 * ((value + weight (edgeAtom 0 2)) + (value + weight (edgeAtom 1 2))
        + (value + weight (edgeAtom 2 3)))
      + M 3 3 * ((value + weight (edgeAtom 0 3)) + (value + weight (edgeAtom 1 3))
        + (value + weight (edgeAtom 2 3)))
      = 1 + ((value + weight (edgeAtom 0 1)) * (value + weight (edgeAtom 0 1))
        + (value + weight (edgeAtom 0 2)) * (value + weight (edgeAtom 0 2))
        + (value + weight (edgeAtom 0 3)) * (value + weight (edgeAtom 0 3))
        + (value + weight (edgeAtom 1 2)) * (value + weight (edgeAtom 1 2))
        + (value + weight (edgeAtom 1 3)) * (value + weight (edgeAtom 1 3))
        + (value + weight (edgeAtom 2 3)) * (value + weight (edgeAtom 2 3))) := by
  have hprice : ∀ firstSlot secondSlot : Fin 4, ∀ hne : firstSlot ≠ secondSlot,
      M firstSlot secondSlot * M secondSlot firstSlot
        = (value + weight (edgeAtom firstSlot secondSlot)
            - M firstSlot firstSlot)
          * (value + weight (edgeAtom firstSlot secondSlot)
            - M secondSlot secondSlot) := by
    intro firstSlot secondSlot hne
    exact two_carrier_pricing_of_datum hdata basisLabel hrepresentation hne
      (hmemAll firstSlot) (hmemAll secondSlot)
      (hatomMem firstSlot secondSlot hne).1 (hatomMem firstSlot secondSlot hne).2
      (hcarriers firstSlot secondSlot hne)
      (hcoordNe firstSlot secondSlot hne).1 (hcoordNe firstSlot secondSlot hne).2
  exact kfour_master_identity hM htrace
    (hprice 0 1 (by decide)) (hprice 0 2 (by decide)) (hprice 0 3 (by decide))
    (hprice 1 2 (by decide)) (hprice 1 3 (by decide)) (hprice 2 3 (by decide))

/-- **THE DATUM CYCLE MASTER.**  A literal four-slot basis whose four
cycle pairs each carry an atom prices the cycle master identity, with the
two uncarried products explicit. -/
theorem cfour_master_identity_of_datum
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin 4 → activeIndex)
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hM : M * M = M) (htrace : Matrix.trace M = 2)
    (hmemAll : ∀ columnIndex, basisLabel columnIndex ∈ activeSet)
    {atom01 atom12 atom23 atom30 : Fin size}
    (hmem01 : atom01 ∈ activeSubset (basisLabel 0)
      ∧ atom01 ∈ activeSubset (basisLabel 1))
    (hmem12 : atom12 ∈ activeSubset (basisLabel 1)
      ∧ atom12 ∈ activeSubset (basisLabel 2))
    (hmem23 : atom23 ∈ activeSubset (basisLabel 2)
      ∧ atom23 ∈ activeSubset (basisLabel 3))
    (hmem30 : atom30 ∈ activeSubset (basisLabel 3)
      ∧ atom30 ∈ activeSubset (basisLabel 0))
    (hcar01 : ∀ columnIndex, columnIndex ≠ 0 → columnIndex ≠ 1 →
      tightDir (basisLabel columnIndex) atom01 = 0)
    (hcar12 : ∀ columnIndex, columnIndex ≠ 1 → columnIndex ≠ 2 →
      tightDir (basisLabel columnIndex) atom12 = 0)
    (hcar23 : ∀ columnIndex, columnIndex ≠ 2 → columnIndex ≠ 3 →
      tightDir (basisLabel columnIndex) atom23 = 0)
    (hcar30 : ∀ columnIndex, columnIndex ≠ 3 → columnIndex ≠ 0 →
      tightDir (basisLabel columnIndex) atom30 = 0)
    (hne01 : tightDir (basisLabel 0) atom01 ≠ 0
      ∧ tightDir (basisLabel 1) atom01 ≠ 0)
    (hne12 : tightDir (basisLabel 1) atom12 ≠ 0
      ∧ tightDir (basisLabel 2) atom12 ≠ 0)
    (hne23 : tightDir (basisLabel 2) atom23 ≠ 0
      ∧ tightDir (basisLabel 3) atom23 ≠ 0)
    (hne30 : tightDir (basisLabel 3) atom30 ≠ 0
      ∧ tightDir (basisLabel 0) atom30 ≠ 0) :
    ((value + weight atom01) * (M 0 0 + M 1 1)
        - (value + weight atom01) * (value + weight atom01))
      + ((value + weight atom12) * (M 1 1 + M 2 2)
        - (value + weight atom12) * (value + weight atom12))
      + ((value + weight atom23) * (M 2 2 + M 3 3)
        - (value + weight atom23) * (value + weight atom23))
      + ((value + weight atom30) * (M 3 3 + M 0 0)
        - (value + weight atom30) * (value + weight atom30))
      + (M 0 0 * M 2 2 - M 0 2 * M 2 0) + (M 1 1 * M 3 3 - M 1 3 * M 3 1)
      = 1 := by
  have hp01 := two_carrier_pricing_of_datum hdata basisLabel hrepresentation
    (by decide : (0 : Fin 4) ≠ 1) (hmemAll 0) (hmemAll 1) hmem01.1 hmem01.2
    hcar01 hne01.1 hne01.2
  have hp12 := two_carrier_pricing_of_datum hdata basisLabel hrepresentation
    (by decide : (1 : Fin 4) ≠ 2) (hmemAll 1) (hmemAll 2) hmem12.1 hmem12.2
    hcar12 hne12.1 hne12.2
  have hp23 := two_carrier_pricing_of_datum hdata basisLabel hrepresentation
    (by decide : (2 : Fin 4) ≠ 3) (hmemAll 2) (hmemAll 3) hmem23.1 hmem23.2
    hcar23 hne23.1 hne23.2
  have hp30 := two_carrier_pricing_of_datum hdata basisLabel hrepresentation
    (by decide : (3 : Fin 4) ≠ 0) (hmemAll 3) (hmemAll 0) hmem30.1 hmem30.2
    hcar30 hne30.1 hne30.2
  have hmaster := cfour_master_identity (d30 := value + weight atom30)
    hM htrace hp01 hp12 hp23 (by linear_combination hp30)
  linear_combination hmaster

end Gtz
