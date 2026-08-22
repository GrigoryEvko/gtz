/-
# The kernel chart: a row law for the pair minors, and domination at a single dependency

The landed `Gtz.dominates_iff_dependencyBound` removes the atoms from the problem: a
`k`-subset `C` dominates exactly when EVERY linear dependency `z` of the atoms obeys

    `∑_{c ∈ C} z_c² / (t_c (1 - t_c))  ≤  ∑_c z_c² / t_c` .

Write `h_c(z) := z_c² / (t_c (1 - t_c))` for the READING of the dependency at a label.
Then `z_c²/(1 - t_c) = t_c h_c` and `z_c²/t_c = (1 - t_c) h_c`, so the criterion is

    `∑_{c ∈ C} t_c h_c  ≤  ∑_{c ∉ C} (1 - t_c) h_c` ,

one inequality between the selected labels weighted by their WEIGHTS and the unselected
labels weighted by their CO-WEIGHTS.  This file proves two things about that inequality.

## 1.  The criterion holds at every single dependency

**`Gtz.exists_dependencyBound_lower`.**  Fix any dependency.  Order the labels by their
readings and take the `k` smallest.  That `k`-subset satisfies the criterion AT THAT
DEPENDENCY, at every size and rank with `k < m`, with no hypothesis on the design at all.

The proof is two lines of bookkeeping.  Let `d₀` be a label off `C` of least reading.
Every selected reading is at most `h_{d₀}` and every unselected reading is at least
`h_{d₀}`, so the two sides are pinched between `h_{d₀} ∑_{c ∈ C} t_c` and
`h_{d₀} ∑_{c ∉ C}(1 - t_c)`, and

    `∑_{c ∈ C} t_c = 1 - S`  while  `∑_{c ∉ C}(1 - t_c) = (m - k) - S` ,   `S := ∑_{c ∉ C} t_c` ,

so the comparison is `1 ≤ m - k`.  The margin is `(m - k - 1)·h_{d₀}`
(`Gtz.exists_dependencyBound_margin`): at `(6,3)` the `k`-smallest subset beats the
criterion by twice the least outside reading.

**This localises the whole of GTZ to a SELECTION problem.**  Nothing fails pointwise.  A
design refutes GTZ only if the `k`-smallest subset ROTATES as the dependency moves, so
that no single subset is smallest everywhere.  `Gtz.not_dominates_imp_exists_swap` is the
contrapositive: a subset that does not dominate is beaten at some dependency by a swap.

## 2.  When one subset is smallest everywhere, it dominates

**`Gtz.dominates_of_uniformly_lower`.**  If a single `k`-subset is among the `k` smallest
readings at EVERY dependency, it dominates.  That is a sufficient criterion for GTZ on a
design, and it is exactly the selection statement above with the quantifiers exchanged.

## 3.  The row law of the excess pair minors

`Gtz.excessPairMinor D c d = (l_c - 1)(l_d - 1) - ⟨g_c, g_d⟩²` is the quantity whose
positivity the campaign reads at every admissible pair.  The tree owns the WEIGHTED TOTAL
`∑_{c,d} t_c t_d q_cd = k² - 3k + 1`; what it does not own is the ROW:

  **`Gtz.sum_weight_mul_excessPairMinor_erase`:**
  `∑_{d ≠ c} t_d q_cd = (k - 1)(l_c - 1) - l_c + t_c(2 l_c - 1)` ,

at every rank and size.  Two Parseval readings and nothing else: the trace gives
`∑_d t_d(l_d - 1) = k - 1`, and Parseval tested against `g_c` gives `∑_d t_d ⟨g_c,g_d⟩² = l_c`.
Summing the row against `t_c` recovers the landed total, so the row is a strict
refinement of it (`Gtz.sum_sum_weight_mul_excessPairMinor`).

[MEASURED before proving, `scratchpad/kchart`, double precision.  The row law over ten
cells of ranks two through five, forty designs each: `max |err| = 2.6e-13`.  The criterion
`C dominates ↔ ∑_{c ∈ C} v_c v_cᵀ ⪯ 1` in the corank frame `v_c = w_c/√(1-t_c)`:
`0/15680` mismatches.  The directional statement at `(6,3)`, `(7,3)`, `(8,4)`, `(9,4)`,
`(10,5)`: `0` violations in `4002` design-dependency pairs, worst margin `-2.6e-1`.

NOT PROVED HERE, measured only, and recorded so a successor does not re-derive them:
with `ε_c := t_c(l_c-1)/(1-t_c)`, `E := ∑ ε_c`, `E_t := ∑ t_c ε_c`, and the corank frame
`N := ∑_c v_c v_cᵀ`, `M_t := ∑_c t_c v_c v_cᵀ`, the identities `E = (k-1) + E_t`,
`tr M_t = 1 - E_t`, `N = 1 + M_t`, `∑_{c<d} q'_cd = (E² - 2E + m - ‖N‖_F²)/2` and
`∑_{c<d}(2 - t_c - t_d) q'_cd = (k-2)E + 2E_t - 1` hold to `1.5e-14`.  The leverage floor
`l_c ≥ 1` forces `M_t ⪯ 1`, hence `N ⪯ 2·1`, in `1588` samples with none without it -- the
floor is NEEDED, the worst `λ_max(M_t)` without it being `3.26`.] -/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Quantitative.ChartHadamard
import Gtz.Wave.DependencyDominationCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1 — the excess pair minor and its row law -/

/-- **THE EXCESS PAIR MINOR** at any rank: the `2×2` determinant of the pair's gap block.
The tree's `Gtz.pairMinor` is this quantity at rank three only. -/
def excessPairMinor (D : WeightedDesign m k) (atomFirst atomSecond : Fin m) : ℝ :=
  (leverageOf (D.atom atomFirst) - 1) * (leverageOf (D.atom atomSecond) - 1)
    - (D.atom atomFirst ⬝ᵥ D.atom atomSecond) ^ 2

theorem excessPairMinor_comm (D : WeightedDesign m k) (atomFirst atomSecond : Fin m) :
    excessPairMinor D atomFirst atomSecond = excessPairMinor D atomSecond atomFirst := by
  rw [excessPairMinor, excessPairMinor, dotProduct_comm]
  ring

/-- The diagonal reading: a label against itself. -/
theorem excessPairMinor_self (D : WeightedDesign m k) (atomIndex : Fin m) :
    excessPairMinor D atomIndex atomIndex = 1 - 2 * leverageOf (D.atom atomIndex) := by
  have hself : D.atom atomIndex ⬝ᵥ D.atom atomIndex = leverageOf (D.atom atomIndex) := by
    rw [leverageOf, dotProduct]
    exact Finset.sum_congr rfl fun _ _ => (pow_two _).symm
  rw [excessPairMinor, hself]
  ring

/-- The weighted excesses total `rank - 1`: the trace of Parseval, shifted by the weights. -/
theorem sum_weight_mul_excess (D : WeightedDesign m k) :
    ∑ atomIndex, D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1) = (k : ℝ) - 1 := by
  have hlev := sum_weighted_leverage D
  have hsplit : ∑ atomIndex, D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1)
      = (∑ atomIndex, D.weight atomIndex * leverageOf (D.atom atomIndex))
        - ∑ atomIndex, D.weight atomIndex := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hsplit, hlev, D.weight_sum_one]

/-- **THE FULL ROW.**  Parseval twice: the trace reading on the excesses and the quadratic
reading against `g_c` on the squared pairings. -/
theorem sum_weight_mul_excessPairMinor (D : WeightedDesign m k) (atomIndex : Fin m) :
    ∑ otherIndex, D.weight otherIndex * excessPairMinor D atomIndex otherIndex
      = ((k : ℝ) - 1) * (leverageOf (D.atom atomIndex) - 1) - leverageOf (D.atom atomIndex) := by
  have hpair := sum_weight_mul_sq_atomPairing D atomIndex
  have hexc := sum_weight_mul_excess D
  have hsplit : ∑ otherIndex, D.weight otherIndex * excessPairMinor D atomIndex otherIndex
      = (leverageOf (D.atom atomIndex) - 1)
          * (∑ otherIndex, D.weight otherIndex * (leverageOf (D.atom otherIndex) - 1))
        - ∑ otherIndex,
            D.weight otherIndex * (D.atom atomIndex ⬝ᵥ D.atom otherIndex) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by rw [excessPairMinor]; ring
  rw [hsplit, hexc, hpair]
  ring

/-- **THE ROW LAW OF THE EXCESS PAIR MINORS.**  Off the diagonal, the row of a label
against the other labels is a polynomial in that label's own leverage and weight, at every
rank and every size.  The tree owns the total of these rows; this is the row. -/
theorem sum_weight_mul_excessPairMinor_erase (D : WeightedDesign m k) (atomIndex : Fin m) :
    ∑ otherIndex ∈ Finset.univ.erase atomIndex,
        D.weight otherIndex * excessPairMinor D atomIndex otherIndex
      = ((k : ℝ) - 1) * (leverageOf (D.atom atomIndex) - 1) - leverageOf (D.atom atomIndex)
        + D.weight atomIndex * (2 * leverageOf (D.atom atomIndex) - 1) := by
  classical
  have hfull := sum_weight_mul_excessPairMinor D atomIndex
  have hpeel : ∑ otherIndex, D.weight otherIndex * excessPairMinor D atomIndex otherIndex
      = D.weight atomIndex * excessPairMinor D atomIndex atomIndex
        + ∑ otherIndex ∈ Finset.univ.erase atomIndex,
            D.weight otherIndex * excessPairMinor D atomIndex otherIndex :=
    (Finset.add_sum_erase _
      (fun otherIndex => D.weight otherIndex * excessPairMinor D atomIndex otherIndex)
      (Finset.mem_univ atomIndex)).symm
  rw [hpeel, excessPairMinor_self] at hfull
  linarith

/-- **THE WEIGHTED TOTAL, FROM THE ROW.**  Summing the row against the weights recovers the
landed off-diagonal total, so the row law refines it. -/
theorem sum_sum_weight_mul_excessPairMinor (D : WeightedDesign m k) :
    ∑ atomIndex, ∑ otherIndex ∈ Finset.univ.erase atomIndex,
        D.weight atomIndex * D.weight otherIndex * excessPairMinor D atomIndex otherIndex
      = ((k : ℝ) - 1) ^ 2 - (k : ℝ)
        + ∑ atomIndex, D.weight atomIndex ^ 2
            * (2 * leverageOf (D.atom atomIndex) - 1) := by
  classical
  have hrow : ∀ atomIndex : Fin m,
      ∑ otherIndex ∈ Finset.univ.erase atomIndex,
          D.weight atomIndex * D.weight otherIndex * excessPairMinor D atomIndex otherIndex
        = D.weight atomIndex
            * (((k : ℝ) - 1) * (leverageOf (D.atom atomIndex) - 1)
              - leverageOf (D.atom atomIndex)
              + D.weight atomIndex * (2 * leverageOf (D.atom atomIndex) - 1)) := by
    intro atomIndex
    rw [← sum_weight_mul_excessPairMinor_erase D atomIndex, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [Finset.sum_congr rfl fun atomIndex (_ : atomIndex ∈ Finset.univ) => hrow atomIndex]
  have hexpand : ∀ atomIndex : Fin m,
      D.weight atomIndex
          * (((k : ℝ) - 1) * (leverageOf (D.atom atomIndex) - 1)
            - leverageOf (D.atom atomIndex)
            + D.weight atomIndex * (2 * leverageOf (D.atom atomIndex) - 1))
        = ((k : ℝ) - 1) * (D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1))
          - D.weight atomIndex * leverageOf (D.atom atomIndex)
          + D.weight atomIndex ^ 2 * (2 * leverageOf (D.atom atomIndex) - 1) := fun _ => by ring
  rw [Finset.sum_congr rfl fun atomIndex (_ : atomIndex ∈ Finset.univ) => hexpand atomIndex,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_weight_mul_excess D, sum_weighted_leverage D]
  ring

/-! ## Part 2 — the reading of a dependency, and the two rewritings of the criterion -/

/-- **THE READING** of a dependency at a label: `z_c² / (t_c (1 - t_c))`.  It is the
quantity the landed dependency criterion compares across the selection, and it is
nonnegative because both weights are. -/
noncomputable def dependencyReading (D : WeightedDesign m k) (dep : Fin m → ℝ)
    (atomIndex : Fin m) : ℝ :=
  dep atomIndex ^ 2 / (D.weight atomIndex * (1 - D.weight atomIndex))

theorem dependencyReading_nonneg (D : WeightedDesign m k) (hsize : 2 ≤ m) (dep : Fin m → ℝ)
    (atomIndex : Fin m) : 0 ≤ dependencyReading D dep atomIndex := by
  refine div_nonneg (sq_nonneg _) ?_
  have hone := weight_lt_one D hsize atomIndex
  nlinarith [D.weight_pos atomIndex]

/-- The selected side of the criterion, in the reading. -/
theorem selected_eq_weight_mul_reading (D : WeightedDesign m k) (hsize : 2 ≤ m)
    (dep : Fin m → ℝ) (atomIndex : Fin m) :
    dep atomIndex ^ 2 / (1 - D.weight atomIndex)
      = D.weight atomIndex * dependencyReading D dep atomIndex := by
  have hone := weight_lt_one D hsize atomIndex
  have hco : (1 : ℝ) - D.weight atomIndex ≠ 0 := by linarith
  have hwt : D.weight atomIndex ≠ 0 := (D.weight_pos atomIndex).ne'
  rw [dependencyReading, eq_comm]
  field_simp
  try ring

/-- The unselected side of the criterion, in the reading. -/
theorem unselected_eq_coWeight_mul_reading (D : WeightedDesign m k) (hsize : 2 ≤ m)
    (dep : Fin m → ℝ) (atomIndex : Fin m) :
    dep atomIndex ^ 2 / D.weight atomIndex
      = (1 - D.weight atomIndex) * dependencyReading D dep atomIndex := by
  have hone := weight_lt_one D hsize atomIndex
  have hco : (1 : ℝ) - D.weight atomIndex ≠ 0 := by linarith
  have hwt : D.weight atomIndex ≠ 0 := (D.weight_pos atomIndex).ne'
  rw [dependencyReading, eq_comm]
  field_simp
  try ring

/-! ## Part 3 — the weight comparison that makes the selection work

The whole content of the directional theorem is this: the selected weights total at most
the unselected CO-weights, and the slack is `m - k - 1`. -/

/-- **THE WEIGHT COMPARISON.**  For any `k`-subset of an `m`-atom design with `k < m`, the
selected weights total at most the unselected co-weights, with slack exactly `m - k - 1`. -/
theorem sum_weight_add_le_sum_coWeight_compl (D : WeightedDesign m k) {selection : Finset (Fin m)}
    (hcard : selection.card = k) (hlt : k < m) :
    (∑ atomIndex ∈ selection, D.weight atomIndex) + ((m : ℝ) - (k : ℝ) - 1)
      ≤ ∑ atomIndex ∈ selectionᶜ, (1 - D.weight atomIndex) := by
  classical
  have hsplit : (∑ atomIndex ∈ selection, D.weight atomIndex)
      + ∑ atomIndex ∈ selectionᶜ, D.weight atomIndex = 1 := by
    rw [Finset.sum_add_sum_compl]
    exact D.weight_sum_one
  have hcardCompl : (selectionᶜ.card : ℝ) = (m : ℝ) - (k : ℝ) := by
    have hnat : selectionᶜ.card = m - k := by
      rw [Finset.card_compl, hcard, Fintype.card_fin]
    rw [hnat, Nat.cast_sub hlt.le]
  have hco : ∑ atomIndex ∈ selectionᶜ, (1 - D.weight atomIndex)
      = (selectionᶜ.card : ℝ) - ∑ atomIndex ∈ selectionᶜ, D.weight atomIndex := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hco, hcardCompl]
  linarith

/-! ## Part 4 — the directional theorem

A `k`-subset is LOWER for a dependency when every selected reading is at most every
unselected reading.  The `k` smallest readings always form such a subset. -/

/-- A selection is lower for a reading when nothing outside reads smaller than anything
inside. -/
def IsLowerFor {size : ℕ} (value : Fin size → ℝ) (selection : Finset (Fin size)) : Prop :=
  ∀ inside ∈ selection, ∀ outside, outside ∉ selection → value inside ≤ value outside

/-- **A LOWER SUBSET OF EVERY SIZE EXISTS.**  Peel the least remaining value `r` times. -/
theorem exists_isLowerFor {size : ℕ} (value : Fin size → ℝ) :
    ∀ chosenCard : ℕ, chosenCard ≤ size →
      ∃ selection : Finset (Fin size),
        selection.card = chosenCard ∧ IsLowerFor value selection := by
  classical
  intro chosenCard
  induction chosenCard with
  | zero => intro _; exact ⟨∅, Finset.card_empty, by intro _ hmem; exact absurd hmem (by simp)⟩
  | succ smaller ih =>
    intro hle
    obtain ⟨selection, hcard, hlower⟩ := ih (by omega)
    have hne : (selectionᶜ : Finset (Fin size)).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, hcard, Fintype.card_fin]
      omega
    obtain ⟨least, hleastMem, hleastMin⟩ := Finset.exists_min_image selectionᶜ value hne
    have hleastOut : least ∉ selection := Finset.mem_compl.mp hleastMem
    refine ⟨insert least selection, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hleastOut, hcard]
    · intro inside hinside outside houtside
      have houtSel : outside ∉ selection := fun hmem =>
        houtside (Finset.mem_insert_of_mem hmem)
      rcases Finset.mem_insert.mp hinside with hEq | hMem
      · subst hEq
        exact hleastMin outside (Finset.mem_compl.mpr houtSel)
      · exact hlower inside hMem outside houtSel

/-- **THE DIRECTIONAL THEOREM, WITH ITS MARGIN.**  At any single dependency, a lower
`k`-subset satisfies the domination inequality, and it beats it by `(m - k - 1)` times the
least outside reading.  No hypothesis on the design: only `k < m`.

At `(6,3)` the margin is twice the least outside reading. -/
theorem exists_dependencyBound_margin (D : WeightedDesign m k) (hsize : 2 ≤ m) (hlt : k < m)
    (dep : Fin m → ℝ) {selection : Finset (Fin m)} (hcard : selection.card = k)
    (hlower : IsLowerFor (dependencyReading D dep) selection) :
    ∃ least ∈ selectionᶜ,
      (∑ atomIndex ∈ selection, dep atomIndex ^ 2 / (1 - D.weight atomIndex))
          + ((m : ℝ) - (k : ℝ) - 1) * dependencyReading D dep least
        ≤ ∑ atomIndex ∈ selectionᶜ, dep atomIndex ^ 2 / D.weight atomIndex := by
  classical
  have hne : (selectionᶜ : Finset (Fin m)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, hcard, Fintype.card_fin]
    omega
  obtain ⟨least, hleastMem, hleastMin⟩ :=
    Finset.exists_min_image selectionᶜ (dependencyReading D dep) hne
  have hleastOut : least ∉ selection := Finset.mem_compl.mp hleastMem
  have hleastNonneg := dependencyReading_nonneg D hsize dep least
  -- the selected side is pinched above by the least outside reading
  have hleft : ∑ atomIndex ∈ selection, dep atomIndex ^ 2 / (1 - D.weight atomIndex)
      ≤ dependencyReading D dep least * ∑ atomIndex ∈ selection, D.weight atomIndex := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun inside hinside => ?_
    rw [selected_eq_weight_mul_reading D hsize dep inside]
    have hcompare := hlower inside hinside least hleastOut
    nlinarith [D.weight_pos inside]
  -- the unselected side is pinched below by the same number
  have hright : dependencyReading D dep least * ∑ atomIndex ∈ selectionᶜ, (1 - D.weight atomIndex)
      ≤ ∑ atomIndex ∈ selectionᶜ, dep atomIndex ^ 2 / D.weight atomIndex := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun outside houtside => ?_
    rw [unselected_eq_coWeight_mul_reading D hsize dep outside]
    have hcompare := hleastMin outside houtside
    have hone := weight_lt_one D hsize outside
    nlinarith
  have hweights := sum_weight_add_le_sum_coWeight_compl D hcard hlt
  refine ⟨least, hleastMem, ?_⟩
  have hscale : dependencyReading D dep least
        * ((∑ atomIndex ∈ selection, D.weight atomIndex) + ((m : ℝ) - (k : ℝ) - 1))
      ≤ dependencyReading D dep least * ∑ atomIndex ∈ selectionᶜ, (1 - D.weight atomIndex) :=
    mul_le_mul_of_nonneg_left hweights hleastNonneg
  nlinarith [hleft, hright, hscale]

/-- **THE DIRECTIONAL THEOREM.**  At any single dependency, the `k` labels of least reading
satisfy the domination inequality.  Nothing about GTZ fails pointwise: only the CHOICE of
the subset can move with the dependency. -/
theorem exists_dependencyBound_lower (D : WeightedDesign m k) (hsize : 2 ≤ m) (hlt : k < m)
    (dep : Fin m → ℝ) :
    ∃ selection : Finset (Fin m), selection.card = k
      ∧ IsLowerFor (dependencyReading D dep) selection
      ∧ (∑ atomIndex ∈ selection, dep atomIndex ^ 2 / (1 - D.weight atomIndex))
          ≤ ∑ atomIndex ∈ selectionᶜ, dep atomIndex ^ 2 / D.weight atomIndex := by
  classical
  obtain ⟨selection, hcard, hlower⟩ :=
    exists_isLowerFor (dependencyReading D dep) k hlt.le
  obtain ⟨least, hleastMem, hbound⟩ :=
    exists_dependencyBound_margin D hsize hlt dep hcard hlower
  refine ⟨selection, hcard, hlower, ?_⟩
  have hslack : (0 : ℝ) ≤ ((m : ℝ) - (k : ℝ) - 1) * dependencyReading D dep least := by
    refine mul_nonneg ?_ (dependencyReading_nonneg D hsize dep least)
    have : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hlt
    linarith
  linarith

/-! ## Part 5 — one subset lower everywhere dominates

The selection problem, with the quantifiers exchanged.  This is a sufficient criterion for
GTZ on a design, and by Part 4 it is the ONLY obstruction: the inequality itself never
fails, only the constancy of the choice. -/

/-- **A UNIFORMLY LOWER SUBSET DOMINATES.**  If one `k`-subset is lower for the reading at
every dependency of the atoms, it dominates.  With Part 4 this says that the ONLY
obstruction to GTZ is the constancy of the choice: the inequality itself never fails at a
dependency, only the identity of the subset that satisfies it can move. -/
theorem dominates_of_uniformly_lower (D : WeightedDesign m k) (hsize : 2 ≤ m) (hlt : k < m)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick)
    (huniform : ∀ dep : Fin m → ℝ, (∑ index, dep index • D.atom index) = 0 →
        IsLowerFor (dependencyReading D dep) (Finset.image pick Finset.univ)) :
    Dominates D (Finset.image pick Finset.univ) := by
  classical
  have hcard : (Finset.image pick Finset.univ).card = k := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hnn : (0 : ℝ) ≤ (m : ℝ) - (k : ℝ) - 1 := by
    have hcast : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hlt
    linarith
  rw [dominates_iff_dependencyBound_compl D hsize pick hinj]
  intro dep hdep
  obtain ⟨least, _, hbound⟩ :=
    exists_dependencyBound_margin D hsize hlt dep hcard (huniform dep hdep)
  have hslack : (0 : ℝ) ≤ ((m : ℝ) - (k : ℝ) - 1) * dependencyReading D dep least :=
    mul_nonneg hnn (dependencyReading_nonneg D hsize dep least)
  linarith

/-- **THE CONTRAPOSITIVE: A FAILING SUBSET IS OUT OF ORDER SOMEWHERE.**  If a `k`-subset
does not dominate, then at some dependency an unselected label reads STRICTLY below a
selected one.  A design refutes GTZ only if EVERY `k`-subset is out of order at some
dependency of its own. -/
theorem exists_swap_of_not_dominates (D : WeightedDesign m k) (hsize : 2 ≤ m) (hlt : k < m)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick)
    (hfail : ¬ Dominates D (Finset.image pick Finset.univ)) :
    ∃ dep : Fin m → ℝ, (∑ index, dep index • D.atom index) = 0
      ∧ ∃ inside ∈ Finset.image pick Finset.univ,
          ∃ outside, outside ∉ Finset.image pick Finset.univ
            ∧ dependencyReading D dep outside < dependencyReading D dep inside := by
  classical
  have hcard : (Finset.image pick Finset.univ).card = k := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hnn : (0 : ℝ) ≤ (m : ℝ) - (k : ℝ) - 1 := by
    have hcast : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hlt
    linarith
  rw [dominates_iff_dependencyBound_compl D hsize pick hinj] at hfail
  push_neg at hfail
  obtain ⟨dep, hdep, hviolate⟩ := hfail
  refine ⟨dep, hdep, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hlower : IsLowerFor (dependencyReading D dep) (Finset.image pick Finset.univ) := by
    intro inside hinside outside houtside
    exact hcon inside hinside outside houtside
  obtain ⟨least, _, hbound⟩ := exists_dependencyBound_margin D hsize hlt dep hcard hlower
  have hslack : (0 : ℝ) ≤ ((m : ℝ) - (k : ℝ) - 1) * dependencyReading D dep least :=
    mul_nonneg hnn (dependencyReading_nonneg D hsize dep least)
  linarith

end Gtz
