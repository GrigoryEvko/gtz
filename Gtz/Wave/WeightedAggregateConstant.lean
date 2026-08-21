/-
# The weighted aggregate of the gap determinants is the constant `-4`

Three separate rounds of this campaign discovered, each time by measurement and
each time as a surprise, that aggregating the triple gap determinants destroys
every trace of the design.  The twenty-triple aggregation of the wedge-bracket
tax is vacuous at every size; the corner's global bracket budget reduces to
zero; the summed two-point form collapses to a field-blind identity.  The
banked rule that came out of it -- *select a slot or multiply slots, never add
them* -- was an empirical rule with three sightings behind it.

It is a theorem.

## The law

For EVERY weighted design of rank three, at EVERY size,

  `∑_a ∑_b ∑_c  t_a t_b t_c · tripleGapDet (g_a, g_b, g_c)  =  -4` .

No hypothesis beyond the design axioms.  The right-hand side mentions neither
the atoms nor the weights nor the size: **the weighted ordered aggregate of the
gap determinants is a universal constant.**

## Why

The Sylvester expansion of a triple's gap determinant is
`det (K - 1) = det K - e₂(K) + tr K - 1`, and each of those three pieces is a
landed conservation law once it is summed against the weights:

| piece | weighted ordered total | landed as |
|---|---|---|
| `det K = [abc]²` | `6` | `Gtz.bracket_budget` |
| `e₂(K) = w_ab + w_ac + w_bc` | `3 · 6 · 1 = 18` | `Gtz.wedge_mass_budget` |
| `tr K = ℓ_a + ℓ_b + ℓ_c` | `3 · 3 = 9` | `Gtz.sum_weighted_leverage` |
| `1` | `1` | `weight_sum_one` |

and `6 - 18 + 9 - 1 = -4`.  The three budgets are exactly the three Sylvester
minors of the gap, so the cancellation is not a coincidence of small numbers --
it is the statement that the design's own conservation laws already determine
every symmetric weighted total of its gap determinants.

## What it closes

Any certificate that reaches its conclusion by summing the gap determinants
against the weights is refuted before it is built: it evaluates to `-4` at the
`(5,3)` primitive diamond, at the `(6,3)` split diamond, at the tetrahedron, at
every complex tie, and at every design that is not a tie at all
(`Gtz.weighted_aggregate_design_blind`).  It cannot separate any two of them.

This is the sharpest possible form of the campaign's aggregation doctrine, and
it converts a rule of thumb into a refutation that costs one rewrite.
-/
import Gtz.Wave.InvariantBudgets
import Gtz.Wave.TripleSumSizeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The Sylvester expansion of a gap determinant -/

/-- **THE THREE MINORS OF A TRIPLE'S GAP.**  The gap determinant is the squared
bracket, less the wedge mass of the three pairs, plus the leverage total, less
one.  A `ring` identity in the six dot products -- the same expansion
`det (K - 1) = det K - e₂(K) + tr K - 1` that drives the Sylvester criterion,
written in the campaign's currencies. -/
theorem tripleGapDet_eq_bracket_sub_wedge_add_leverage (a b c : Fin 3 → ℝ) :
    tripleGapDet a b c
      = tripleBracket a b c ^ 2
        - ((leverageOf a * leverageOf b - (a ⬝ᵥ b) ^ 2)
            + (leverageOf a * leverageOf c - (a ⬝ᵥ c) ^ 2)
            + (leverageOf b * leverageOf c - (b ⬝ᵥ c) ^ 2))
        + (leverageOf a + leverageOf b + leverageOf c)
        - 1 := by
  rw [tripleGapDet, sq_tripleBracket_eq_gramDet]
  ring

/-! ## 2. Factoring a free index out of a weighted triple sum -/

/-- A summand that does not mention the third label factors the third weight
out, and the design's weights total one. -/
theorem weightedTriple_factor_last (D : WeightedDesign m 3) (f : Fin m → Fin m → ℝ) :
    ∑ a, ∑ b, ∑ c, D.weight a * (D.weight b * (D.weight c * f a b))
      = ∑ a, ∑ b, D.weight a * (D.weight b * f a b) := by
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have : ∑ c, D.weight a * (D.weight b * (D.weight c * f a b))
      = (D.weight a * (D.weight b * f a b)) * ∑ c, D.weight c := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [this, D.weight_sum_one, mul_one]

/-- The same with the middle label free. -/
theorem weightedTriple_factor_mid (D : WeightedDesign m 3) (f : Fin m → Fin m → ℝ) :
    ∑ a, ∑ b, ∑ c, D.weight a * (D.weight b * (D.weight c * f a c))
      = ∑ a, ∑ c, D.weight a * (D.weight c * f a c) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : ∑ b, D.weight a * (D.weight b * (D.weight c * f a c))
      = (D.weight a * (D.weight c * f a c)) * ∑ b, D.weight b := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [this, D.weight_sum_one, mul_one]

/-- The same with the first label free. -/
theorem weightedTriple_factor_first (D : WeightedDesign m 3) (f : Fin m → Fin m → ℝ) :
    ∑ a, ∑ b, ∑ c, D.weight a * (D.weight b * (D.weight c * f b c))
      = ∑ b, ∑ c, D.weight b * (D.weight c * f b c) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : ∑ a, D.weight a * (D.weight b * (D.weight c * f b c))
      = (D.weight b * (D.weight c * f b c)) * ∑ a, D.weight a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [this, D.weight_sum_one, mul_one]

/-- A summand depending on ONE label collapses to a single weighted sum. -/
theorem weightedTriple_factor_single (D : WeightedDesign m 3) (g : Fin m → ℝ) :
    ∑ a, ∑ b, ∑ c, D.weight a * (D.weight b * (D.weight c * g a))
      = ∑ a, D.weight a * g a := by
  rw [weightedTriple_factor_last D (fun a _ => g a)]
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) rfl
  have : ∑ b, D.weight a * (D.weight b * g a)
      = (D.weight a * g a) * ∑ b, D.weight b := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [this, D.weight_sum_one, mul_one]

/-! ## 3. The constant -/

/-- **THE WEIGHTED AGGREGATE IS `-4`.**  For every weighted design of rank
three, at every size, the ordered weighted total of the triple gap
determinants is the universal constant `-4`.

The proof spends exactly the three conservation laws that are the three
Sylvester minors of the gap: the bracket budget `6`, the wedge mass budget `6`
(entering three times, once per pair of the triple, hence `18`), and the
leverage total `3` (entering three times, hence `9`), against the unit weight
total `1`.  `6 - 18 + 9 - 1 = -4`. -/
theorem weighted_ordered_tripleGapDet_sum (D : WeightedDesign m 3) :
    ∑ a, ∑ b, ∑ c, D.weight a * (D.weight b * (D.weight c *
        tripleGapDet (D.atom a) (D.atom b) (D.atom c))) = -4 := by
  have hlev : ∑ c, D.weight c * leverageOf (D.atom c) = 3 := by
    have h := sum_weighted_leverage D
    norm_num at h
    exact h
  -- the four pieces of the Sylvester expansion, each a landed total
  have hsplit : ∀ a b c : Fin m,
      D.weight a * (D.weight b * (D.weight c *
          tripleGapDet (D.atom a) (D.atom b) (D.atom c)))
        = D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))
          - D.weight a * (D.weight b * (D.weight c *
              (leverageOf (D.atom a) * leverageOf (D.atom b)
                - atomPairing D a b ^ 2)))
          - D.weight a * (D.weight b * (D.weight c *
              (leverageOf (D.atom a) * leverageOf (D.atom c)
                - atomPairing D a c ^ 2)))
          - D.weight a * (D.weight b * (D.weight c *
              (leverageOf (D.atom b) * leverageOf (D.atom c)
                - atomPairing D b c ^ 2)))
          + D.weight a * (D.weight b * (D.weight c * leverageOf (D.atom a)))
          + D.weight a * (D.weight b * (D.weight c * leverageOf (D.atom b)))
          + D.weight a * (D.weight b * (D.weight c * leverageOf (D.atom c)))
          - D.weight a * (D.weight b * (D.weight c * 1)) := by
    intro a b c
    rw [tripleGapDet_eq_bracket_sub_wedge_add_leverage, atomBracket, atomPairing,
      atomPairing, atomPairing]
    ring
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => hsplit a b c]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- evaluate the eight totals
  rw [bracket_budget D]
  rw [weightedTriple_factor_last D (fun a b =>
    leverageOf (D.atom a) * leverageOf (D.atom b) - atomPairing D a b ^ 2)]
  rw [weightedTriple_factor_mid D (fun a c =>
    leverageOf (D.atom a) * leverageOf (D.atom c) - atomPairing D a c ^ 2)]
  rw [weightedTriple_factor_first D (fun b c =>
    leverageOf (D.atom b) * leverageOf (D.atom c) - atomPairing D b c ^ 2)]
  rw [wedge_mass_budget D]
  rw [weightedTriple_factor_single D (fun a => leverageOf (D.atom a))]
  rw [weightedTriple_factor_mid D (fun _ c => leverageOf (D.atom c))]
  rw [weightedTriple_factor_first D (fun b _ => leverageOf (D.atom b))]
  rw [weightedTriple_factor_single D (fun _ => (1 : ℝ))]
  simp only [mul_one]
  rw [hlev]
  -- the two remaining doubles are the wedge budget and the leverage total
  have hmid : ∑ a, ∑ c, D.weight a * (D.weight c * leverageOf (D.atom c)) = 3 := by
    rw [← hlev]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    have : ∑ a, D.weight a * (D.weight c * leverageOf (D.atom c))
        = (D.weight c * leverageOf (D.atom c)) * ∑ a, D.weight a := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [this, D.weight_sum_one, mul_one]
  have hfirst : ∑ b, ∑ c, D.weight b * (D.weight c * leverageOf (D.atom b)) = 3 := by
    rw [← hlev]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : ∑ c, D.weight b * (D.weight c * leverageOf (D.atom b))
        = (D.weight b * leverageOf (D.atom b)) * ∑ c, D.weight c := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [this, D.weight_sum_one, mul_one]
  rw [hmid, hfirst, D.weight_sum_one]
  norm_num

/-! ## 4. What the constant refutes -/

/-- **THE WEIGHTED AGGREGATE IS DESIGN-BLIND.**  Any two weighted designs of
rank three -- of any two sizes, one a tie and one not, one real and one the
realification of a complex tie -- give the SAME weighted aggregate.  So no
inequality whose left side is that aggregate can separate them, and no
certificate can be built from it.

This is the campaign's aggregation doctrine as a theorem.  Three rounds
discovered it by measurement, once per arm.  It costs one rewrite to apply. -/
theorem weighted_aggregate_design_blind {m' : ℕ}
    (D : WeightedDesign m 3) (D' : WeightedDesign m' 3) :
    ∑ a, ∑ b, ∑ c, D.weight a * (D.weight b * (D.weight c *
        tripleGapDet (D.atom a) (D.atom b) (D.atom c)))
      = ∑ a, ∑ b, ∑ c, D'.weight a * (D'.weight b * (D'.weight c *
          tripleGapDet (D'.atom a) (D'.atom b) (D'.atom c))) := by
  rw [weighted_ordered_tripleGapDet_sum D, weighted_ordered_tripleGapDet_sum D']

/-- **THE AGGREGATE IS NEVER ZERO, SO IT NEVER VANISHES AT A TIE EITHER.**  A
certificate of the shape "at a tie the weighted aggregate vanishes" is refuted
outright: the aggregate is `-4` at every design. -/
theorem weighted_aggregate_ne_zero (D : WeightedDesign m 3) :
    ∑ a, ∑ b, ∑ c, D.weight a * (D.weight b * (D.weight c *
        tripleGapDet (D.atom a) (D.atom b) (D.atom c))) ≠ 0 := by
  rw [weighted_ordered_tripleGapDet_sum D]
  norm_num

/-- **THE DEGENERATE SLOTS CARRY THE WHOLE CONSTANT AT A TIE.**  Split the
ordered aggregate into the part indexed by triples of DISTINCT labels and the
rest.  If every distinct triple has nonpositive gap determinant -- which a tie
with all triples live supplies -- then the degenerate part alone is at least
`-4`.

The degenerate part mentions only repeated labels, so it is a function of the
weights and the leverages and NOT of the angles.  A tie therefore constrains
its weight-and-leverage data directly, with no geometry left in the statement. -/
theorem isTie_degenerate_slots_ge (D : WeightedDesign m 3)
    (hnonpos : ∀ a b c : Fin m, a ≠ b → a ≠ c → b ≠ c →
      tripleGapDet (D.atom a) (D.atom b) (D.atom c) ≤ 0) :
    -4 ≤ ∑ a, ∑ b, ∑ c, if a = b ∨ a = c ∨ b = c then
        D.weight a * (D.weight b * (D.weight c *
          tripleGapDet (D.atom a) (D.atom b) (D.atom c))) else 0 := by
  classical
  have hkey := weighted_ordered_tripleGapDet_sum D
  have hle : ∀ a b c : Fin m,
      D.weight a * (D.weight b * (D.weight c *
          tripleGapDet (D.atom a) (D.atom b) (D.atom c)))
        ≤ (if a = b ∨ a = c ∨ b = c then
            D.weight a * (D.weight b * (D.weight c *
              tripleGapDet (D.atom a) (D.atom b) (D.atom c))) else 0) := by
    intro a b c
    by_cases hd : a = b ∨ a = c ∨ b = c
    · simp [hd]
    · have hd' := hd
      push_neg at hd
      obtain ⟨hab, hac, hbc⟩ := hd
      have hw := mul_nonneg (le_of_lt (D.weight_pos a))
        (mul_nonneg (le_of_lt (D.weight_pos b)) (le_of_lt (D.weight_pos c)))
      have : D.weight a * (D.weight b * (D.weight c *
          tripleGapDet (D.atom a) (D.atom b) (D.atom c))) ≤ 0 := by
        have hprod : D.weight a * (D.weight b * (D.weight c *
            tripleGapDet (D.atom a) (D.atom b) (D.atom c)))
            = (D.weight a * (D.weight b * D.weight c)) *
              tripleGapDet (D.atom a) (D.atom b) (D.atom c) := by ring
        rw [hprod]
        exact mul_nonpos_of_nonneg_of_nonpos hw (hnonpos a b c hab hac hbc)
      rw [if_neg hd']
      exact this
  calc (-4 : ℝ) = ∑ a, ∑ b, ∑ c, D.weight a * (D.weight b * (D.weight c *
        tripleGapDet (D.atom a) (D.atom b) (D.atom c))) := hkey.symm
    _ ≤ _ := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          Finset.sum_le_sum fun c _ => hle a b c

end Gtz
