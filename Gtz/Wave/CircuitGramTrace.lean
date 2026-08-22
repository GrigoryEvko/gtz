/-
# The aggregate swap law is a TRACE, and it is the weakest of three

`Gtz/Wave/CircuitSwapLaw.lean` lands, at a dominating triple of a `(6,3)` design,

    `th_a delta_bc + th_b delta_ac + th_c delta_ab <= (3 + th_a + th_b + th_c) nu_abc` ,

and calls it the trace reading of the dependency criterion.  This module proves
that it IS a trace, of the explicit `3 x 3` matrix that
`Gtz/Wave/DependencyAtomCap.lean` builds, and it draws the two consequences that
the trace alone was hiding.

## 1. The slack of one circuit, in volume currency

  **`Gtz.weightProd_mul_depSlack_circuitDep`:**
    `t_a t_b t_c t_d * depSlack D {a,b,c} (circuitDep D a b c d)`
    `  = nu_abc - (th_a nu_bcd + th_b nu_acd + th_c nu_abd)` .

The left side is a DIAGONAL entry of `Gtz.circuitGram`, and the right side is the
slack of the landed swap law `Gtz.swapLaw_volume_of_dominates`.  So the swap law
is exactly the nonnegativity of one diagonal entry of the circuit Gram, and there
are three of them.

## 2. The three diagonal entries total the aggregate

Summing over the three outside labels and spending the landed two-point marginal
`Gtz.sum_selectionVolume_eq_pairVolume` collapses the nine swapped masses onto
the three pair masses inside the triple:

  **`Gtz.sum_weighted_depSlack_circuitDep_sixThree`:**
    `sum_{d outside} t_a t_b t_c t_d * depSlack D {a,b,c} (circuitDep D a b c d)`
    `  = (3 + th_a + th_b + th_c) nu_abc - (th_a delta_bc + th_b delta_ac + th_c delta_ab)` .

The right side is exactly the slack of the landed aggregate.  So

  **the aggregate swap law is the statement that the TRACE of the circuit Gram,
  weighted by the four weights of each circuit, is nonnegative.**

## 3. What the trace was hiding

A `3 x 3` matrix with nonnegative trace need not be positive semidefinite, and
`Gtz.dominates_iff_posSemidef_circuitGram_sixThree` says that domination is the
positive semidefiniteness.  Sylvester supplies two more conditions, and both are
polynomial in the brackets and the weights:

* the three TWO-BY-TWO minors, which are the two-circuit minors of
  `Gtz.twoCircuitMinor_of_dominates`, and
* the DETERMINANT, which `Gtz.det_circuitGram_eq_zero_of_isTie_sixThree` shows
  VANISHES at every dominator of a tie.

`Gtz.dominator_circuitGram_ladder_sixThree` packages the three levels, and
`Gtz.tie_circuitGram_ladder_sixThree` adds the tie's equality.

[MEASURED, `scratchpad/kzero`, double precision.  The trace identity of part 2
was checked at 2000000 triples of 100000 random `(6,3)` designs with ZERO
deviations and worst relative error `6.0e-10`.  Of the 1646557 triples that pass
all three diagonal conditions only 1247248 dominate; the three two-by-two minors
remove `83.07` percent of the impostors and the determinant removes the rest.

A NEGATIVE, and it is the reason the trace cannot be pushed.  Normalise the
circuit Gram so that domination reads `sigma_max <= 1`; then the trace is
`sigma_1^2 + sigma_2^2 + sigma_3^2`.  At a TIE the dominating triple has
`sigma_max = 1` exactly, so the trace is at least one at EVERY triple of a tie,
and a test of the form "some triple has trace at most one" is false.  At the
five `(6,3)` splits of the `(5,3)` diamond the smallest such trace over the
twenty triples is exactly `13/12`, the singular squares of the best triple being
`(0, 1/12, 1)`.  The same argument applies to EVERY quantity that dominates
`sigma_max^2`, so no such relaxation can decide `Gtz.GtzWeighted 6 3`.]
-/
import Gtz.Wave.DependencyAtomCap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## Part 1 — one circuit, in volume currency -/

/-- **THE SLACK OF ONE CIRCUIT IS THE SWAP LAW'S SLACK.**  Scaling the diagonal
entry of the circuit Gram by the four weights of the circuit turns every bracket
into a triple mass, and the entry becomes the dominator's own mass minus the
three swapped masses at their odds. -/
theorem weightProd_mul_depSlack_circuitDep (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {a b c d : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d) :
    D.weight a * D.weight b * D.weight c * D.weight d
        * depSlack D ({a, b, c} : Finset (Fin m)) (circuitDep D a b c d)
      = selectionVolume D a b c
        - (weightOdds D a * selectionVolume D b c d
            + weightOdds D b * selectionVolume D a c d
            + weightOdds D c * selectionVolume D a b d) := by
  have hwa : (0 : ℝ) < 1 - D.weight a := by linarith [weight_lt_one D hm a]
  have hwb : (0 : ℝ) < 1 - D.weight b := by linarith [weight_lt_one D hm b]
  have hwc : (0 : ℝ) < 1 - D.weight c := by linarith [weight_lt_one D hm c]
  have hta := D.weight_pos a
  have htb := D.weight_pos b
  have htc := D.weight_pos c
  have htd := D.weight_pos d
  rw [depSlack_circuitDep D hab hac hbc had hbd hcd, weightOdds, weightOdds, weightOdds,
    selectionVolume, selectionVolume, selectionVolume, selectionVolume]
  field_simp
  try ring

/-! ## Part 2 — the three diagonal entries total the aggregate -/

/-- **THE WEIGHTED TRACE OF THE CIRCUIT GRAM IS THE AGGREGATE'S SLACK.**  The nine
swapped masses collapse onto the three pair masses inside the triple, and the
correction is exactly three copies of the triple's own mass.  So the landed
aggregate swap law is the nonnegativity of a TRACE. -/
theorem sum_weighted_depSlack_circuitDep_sixThree (D : WeightedDesign 6 3)
    {a b c d e f : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    D.weight a * D.weight b * D.weight c * D.weight d
          * depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c d)
        + D.weight a * D.weight b * D.weight c * D.weight e
          * depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c e)
        + D.weight a * D.weight b * D.weight c * D.weight f
          * depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c f)
      = (3 + weightOdds D a + weightOdds D b + weightOdds D c) * selectionVolume D a b c
        - (weightOdds D a * pairVolume D b c + weightOdds D b * pairVolume D a c
            + weightOdds D c * pairVolume D a b) := by
  have hm : (2 : ℕ) ≤ 6 := by norm_num
  have hone := weightProd_mul_depSlack_circuitDep D hm hab hac hbc had hbd hcd
  have htwo := weightProd_mul_depSlack_circuitDep D hm hab hac hbc hae hbe hce
  have hthree := weightProd_mul_depSlack_circuitDep D hm hab hac hbc haf hbf hcf
  -- the three pair rows of the landed two-point marginal
  have hrowBC := sum_outside_selectionVolume_sixThree D
    (bijective_six hbc (Ne.symm hab) hbd hbe hbf (Ne.symm hac) hcd hce hcf had hae haf
      hde hdf hef)
  have hrowAC := sum_outside_selectionVolume_sixThree D
    (bijective_six hac hab had hae haf (Ne.symm hbc) hcd hce hcf hbd hbe hbf hde hdf hef)
  have hrowAB := sum_outside_selectionVolume_sixThree D
    (bijective_six hab hac had hae haf hbc hbd hbe hbf hcd hce hcf hde hdf hef)
  rw [selectionVolume_rotate D a b c] at hrowBC
  rw [selectionVolume_swap_right D a c b] at hrowAC
  rw [hone, htwo, hthree]
  linear_combination (-(weightOdds D a)) * hrowBC + (-(weightOdds D b)) * hrowAC
    + (-(weightOdds D c)) * hrowAB

/-- **THE AGGREGATE, RE-DERIVED FROM THE TRACE.**  A dominating triple makes each
of the three diagonal entries nonnegative, so their total is nonnegative, and
that total is the aggregate's slack.  This reproves
`Gtz.aggregate_swapLaw_of_dominates_sixThree` from the circuit Gram, and it makes
plain that the aggregate is only the FIRST of the three Sylvester conditions. -/
theorem aggregate_of_dominates_from_trace_sixThree (D : WeightedDesign 6 3)
    {a b c d e f : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hdom : Dominates D ({a, b, c} : Finset (Fin 6))) :
    weightOdds D a * pairVolume D b c + weightOdds D b * pairVolume D a c
        + weightOdds D c * pairVolume D a b
      ≤ (3 + weightOdds D a + weightOdds D b + weightOdds D c) * selectionVolume D a b c := by
  have hm : (2 : ℕ) ≤ 6 := by norm_num
  have hinj : Function.Injective (![a, b, c] : Fin 3 → Fin 6) :=
    injective_tripleVec hab hac hbc
  have himage : Finset.image (![a, b, c] : Fin 3 → Fin 6) Finset.univ
      = ({a, b, c} : Finset (Fin 6)) := image_tripleVec_eq
  have hcrit : ∀ dep : Fin 6 → ℝ, (∑ index, dep index • D.atom index) = 0 →
      0 ≤ depSlack D ({a, b, c} : Finset (Fin 6)) dep := by
    intro dep hdep
    have hstep := (dominates_iff_depSlack_nonneg D hm _ hinj).mp (by rw [himage]; exact hdom)
      dep hdep
    rwa [himage] at hstep
  have hweights : ∀ x : Fin 6, (0 : ℝ) < D.weight a * D.weight b * D.weight c * D.weight x :=
    fun x => mul_pos (mul_pos (mul_pos (D.weight_pos a) (D.weight_pos b)) (D.weight_pos c))
      (D.weight_pos x)
  have hd := mul_nonneg (hweights d).le (hcrit _ (sum_circuitDep_smul_atom D a b c d))
  have he := mul_nonneg (hweights e).le (hcrit _ (sum_circuitDep_smul_atom D a b c e))
  have hf := mul_nonneg (hweights f).le (hcrit _ (sum_circuitDep_smul_atom D a b c f))
  have htotal := sum_weighted_depSlack_circuitDep_sixThree D hab hac had hae haf hbc hbd hbe
    hbf hcd hce hcf hde hdf hef
  linarith

/-! ## Part 3 — the ladder the trace was hiding -/

/-- **THE THREE LEVELS OF THE DOMINATION CRITERION AT `(6,3)`.**  A dominating
triple satisfies all seven Sylvester conditions of its circuit Gram: three
diagonal entries — the swap law — three two-by-two minors — the two-circuit
minors — and one determinant.  The aggregate of part 2 is the total of the first
three and is strictly weaker than the whole. -/
theorem dominator_circuitGram_ladder_sixThree (D : WeightedDesign 6 3)
    {a b c d e f : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hdom : Dominates D ({a, b, c} : Finset (Fin 6))) :
    (0 ≤ depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c d)
        ∧ 0 ≤ depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c e)
        ∧ 0 ≤ depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c f))
      ∧ (depCross D ({a, b, c} : Finset (Fin 6))
              (circuitDep D a b c d) (circuitDep D a b c e) ^ 2
            ≤ depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c d)
              * depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c e)
          ∧ depCross D ({a, b, c} : Finset (Fin 6))
              (circuitDep D a b c d) (circuitDep D a b c f) ^ 2
            ≤ depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c d)
              * depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c f)
          ∧ depCross D ({a, b, c} : Finset (Fin 6))
              (circuitDep D a b c e) (circuitDep D a b c f) ^ 2
            ≤ depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c e)
              * depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c f))
      ∧ 0 ≤ (circuitGram D a b c ![d, e, f]).det := by
  have hm : (2 : ℕ) ≤ 6 := by norm_num
  have hinj : Function.Injective (![a, b, c] : Fin 3 → Fin 6) :=
    injective_tripleVec hab hac hbc
  have himage : Finset.image (![a, b, c] : Fin 3 → Fin 6) Finset.univ
      = ({a, b, c} : Finset (Fin 6)) := image_tripleVec_eq
  have hdom' : Dominates D (Finset.image (![a, b, c] : Fin 3 → Fin 6) Finset.univ) := by
    rw [himage]; exact hdom
  have hcrit : ∀ dep : Fin 6 → ℝ, (∑ index, dep index • D.atom index) = 0 →
      0 ≤ depSlack D ({a, b, c} : Finset (Fin 6)) dep := by
    intro dep hdep
    have hstep := (dominates_iff_depSlack_nonneg D hm _ hinj).mp hdom' dep hdep
    rwa [himage] at hstep
  have hminor : ∀ x y : Fin 6,
      depCross D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c x) (circuitDep D a b c y) ^ 2
        ≤ depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c x)
          * depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c y) := by
    intro x y
    have hstep := depCross_sq_le_depSlack_mul_of_dominates D hm _ hinj hdom'
      (sum_circuitDep_smul_atom D a b c x) (sum_circuitDep_smul_atom D a b c y)
    rwa [himage] at hstep
  refine ⟨⟨hcrit _ (sum_circuitDep_smul_atom D a b c d),
    hcrit _ (sum_circuitDep_smul_atom D a b c e),
    hcrit _ (sum_circuitDep_smul_atom D a b c f)⟩,
    ⟨hminor d e, hminor d f, hminor e f⟩, ?_⟩
  exact (posSemidef_circuitGram_of_dominates D hm hab hac hbc ![d, e, f] hdom).det_nonneg

/-- **THE LADDER AT A TIE.**  The determinant closes.  So at every dominator of a
`(6,3)` tie the circuit Gram is positive semidefinite and SINGULAR, its three
diagonal entries are nonnegative, its three two-by-two minors are nonnegative,
and its determinant is zero. -/
theorem tie_circuitGram_ladder_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    {a b c d e f : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hdom : Dominates D ({a, b, c} : Finset (Fin 6))) :
    (circuitGram D a b c ![d, e, f]).PosSemidef
      ∧ (circuitGram D a b c ![d, e, f]).det = 0 :=
  ⟨posSemidef_circuitGram_of_dominates D (by norm_num) hab hac hbc ![d, e, f] hdom,
    det_circuitGram_eq_zero_of_isTie_sixThree D htie hab hac hbc had hbd hcd hae hbe hce
      haf hbf hcf hde hdf hef hdom⟩

/-- **NO STRICTLY WEAKER SINGLE-TRIPLE TEST DECIDES THE MAIN STATEMENT.**  A tie
refuses STRICT domination at every triple, so any predicate that implies strict
domination is false at all twenty triples of a tie.  A test that produced a
STRICT dominator at every design would therefore refute the existence of a
`(6,3)` tie, which is a strictly stronger statement than `Gtz.GtzWeighted 6 3`.
Only a test that is TIGHT at a tie's dominator can decide the main statement. -/
theorem no_strictTest_at_isTie (D : WeightedDesign m 3) (htie : IsTie D)
    {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ (subsetSum D ({a, b, c} : Finset (Fin m)) - 1).PosDef := by
  refine htie.2 _ ?_
  rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
    Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]

end Gtz
