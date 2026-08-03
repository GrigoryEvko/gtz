/-
# The heavy-atom dichotomy at `(7,3)`: an exact tie at every leverage scale

`Gtz.Design.LeverageCapDecision` settled the PIVOT form of the compactification
brick — `HeavyPivotCovering cap 7` is FALSE at every `cap` (`not_heavyPivotCovering`) —
and named the surviving pivot-FREE form `HeavyAtomCovering`: *some leverage `≥ cap`
implies SOME triple has both discriminant legs nonnegative*, the winning triple not
required to contain the heavy atom. Its two corollaries
(`discriminantCovering_of_heavyAtomCovering_of_capped`,
`rank_three_of_heavyAtomCovering_of_capped`) are already unconditional, so a proof of
`HeavyAtomCovering` at ANY stated `cap` would confine the whole of rank three to a
bounded leverage slice.

**WHAT THIS FILE DOES NOT DO, stated first because the name could be misread.**
`HeavyAtomCovering cap 7` is NOT inhabited here, at any `cap`, and it is NOT refuted
here. Nothing below discharges the hypothesis of either corollary, so both remain
conditional and `DiscriminantCovering 7` — hence `GtzWeightedAll 3`, hence the 1997
statement at rank three — is exactly as open after this file as before it. A
compactification is not a proof, and this file does not even supply the
compactification.

**WHAT IT DOES ESTABLISH: the tie gate binds at EVERY leverage scale.** Take the
shipped class-tie section `splitClassDesign` (`Gtz.Ties.SplitClassTieFamily`) at the
`(2,2,2,1)` partition `sevenIntoFourBalanced`, and put weight `spikeWeight` on the
singleton class with the remaining mass split evenly over the other six atoms. The
result is an exact `IsTie` at every admissible `spikeWeight`, all-heavy, with the
singleton atom's leverage equal to `(2 + spikeWeight)/(3·spikeWeight)`
(`spikeClassTieDesign_spike_leverage`) — which is `cap` exactly at
`spikeWeight = 2/(3·cap − 1)`. So for EVERY `cap` there is an all-heavy weighted
`(7,3)` design carrying an atom of leverage at least `cap` at which NO `3`-subset
dominates strictly (`exists_allHeavy_isTie_seven_with_leverage_ge`).

Three consequences, all of them constraints on how `HeavyAtomCovering` could ever be
proved.

* Every STRICT reading of the heavy-atom brick is false at every `cap`
  (`not_heavyAtomStrictCovering`): no argument may produce a strictly dominating
  triple, and no argument may produce a uniform positive margin in the two legs,
  because the design where it would have to hold sits exactly on the boundary.
* The same holds for the capped half at every `cap` above the uniform tie's leverage
  `3` (`not_cappedStrictCovering_of_three_lt`), so the tightness burden does not move
  off the compactification either — it is present on BOTH hypotheses of the
  corollary at once.
* The `(7,3)` tie stratum carries UNBOUNDED leverage. Reading the leverages off the
  `(7,3)` ties this repository names, they top out at `5` — that is a MEASUREMENT on
  the catalogue, not a theorem and not a fact about the stratum, and
  `exists_allHeavy_isTie_seven_with_leverage_ge` retires the reading "no known tie
  triggers the heavy-atom hypothesis at large `cap`, so the tie gate is vacuous
  there". It is not vacuous anywhere.

At `spikeWeight = 1/4` the section's class totals are `(1/4, 1/4, 1/4, 1/4)` and every
leverage is exactly `3` (`spikeClassTieDesign_quarter_spike_leverage`): the uniform
point, carrying the same invariants as the split tetrahedron of
`Gtz.Quantitative.DecisionAtlasSevenThree` and differing from it only by a rotation
and a relabelling of which class holds the singleton. That identification is NOT
mechanized here — the two constructions come from different sections, the Householder
one and the tetrahedron one — so the curve is stated on its own terms.

**Two routes to the dichotomy that this file deliberately does not take, and why.**
The RESIDUE route — "a spike of weight `w → 0` leaves the other six atoms carrying
weight `→ 1`, hence nearly a design, so use `(6,3)` domination on the residue" — is
refuted as stated: the residue of an atom of weighted leverage `tau` is `I − tau·uuᵀ`,
whose deficit is `tau`, and `tau` is free in `(0,1]` INDEPENDENTLY of the leverage, so
a large `cap` does not make the residue close to a design. The DEFLATION route —
apply `exists_deflatedGapBound` at the heavy atom and land on a smaller rung — is
circular at `(7,3)`: its heavy branch consumes `GtzWeighted 6 3`, which is open.
Neither is mechanized here because neither is true as stated.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.LeverageCapDecision
import Gtz.Ties.SplitClassTieFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

/-! ### The leverage of a corank-one section atom

`simplexTieDesign_leverage_identity` pins `k·t_c·ℓ_c = (k−1) + t_c` at the corank-one
section. Solving it for `ℓ_c` is what turns a weight into a leverage, and it is the
only computation the whole curve needs. -/

/-- The shipped corank-one leverage identity, read directly on the section atom rather
than through the design wrapper. -/
theorem simplexTieAtom_leverage_identity {rank : ℕ} (hrank : 1 ≤ rank)
    (weight : Fin (rank + 1) → ℝ) (hpos : ∀ label, 0 < weight label)
    (hsum : ∑ label, weight label = 1) (label : Fin (rank + 1)) :
    (rank : ℝ) * weight label * leverageOf (simplexTieAtom weight label)
      = ((rank : ℝ) - 1) + weight label :=
  simplexTieDesign_leverage_identity weight hrank hpos hsum label

/-- **Every corank-one section atom is heavy above rank one.** The identity
`k·t·ℓ = (k−1) + t` together with `t < 1` on the open simplex gives
`k·t·ℓ > k·t`, hence `ℓ > 1`. At `rank = 1` this fails with equality — the
hypothesis `2 ≤ rank` is load-bearing, not decoration. -/
theorem one_lt_leverage_simplexTieAtom {rank : ℕ} (hrank : 2 ≤ rank)
    (weight : Fin (rank + 1) → ℝ) (hpos : ∀ label, 0 < weight label)
    (hsum : ∑ label, weight label = 1) (label : Fin (rank + 1)) :
    1 < leverageOf (simplexTieAtom weight label) := by
  have hrankOne : 1 ≤ rank := le_trans one_le_two hrank
  have hrankBound : (2 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
  have hidentity := simplexTieAtom_leverage_identity hrankOne weight hpos hsum label
  have hbelowOne := weight_lt_one_of_simplex hrankOne hpos hsum label
  have hweightPos := hpos label
  have hscalePos : (0 : ℝ) < (rank : ℝ) * weight label :=
    mul_pos (by linarith) hweightPos
  have hstrict : (rank : ℝ) * weight label < ((rank : ℝ) - 1) + weight label := by
    nlinarith [mul_pos (show (0 : ℝ) < (rank : ℝ) - 1 by linarith)
      (show (0 : ℝ) < 1 - weight label by linarith)]
  refine lt_of_mul_lt_mul_left ?_ hscalePos.le
  rw [mul_one, hidentity]
  exact hstrict

/-- The section atom's leverage in closed form, `ℓ_c = ((k−1) + t_c)/(k·t_c)`. -/
theorem leverage_simplexTieAtom_eq {rank : ℕ} (hrank : 1 ≤ rank)
    (weight : Fin (rank + 1) → ℝ) (hpos : ∀ label, 0 < weight label)
    (hsum : ∑ label, weight label = 1) (label : Fin (rank + 1)) :
    leverageOf (simplexTieAtom weight label)
      = (((rank : ℝ) - 1) + weight label) / ((rank : ℝ) * weight label) := by
  have hrankPos : (0 : ℝ) < (rank : ℝ) := by exact_mod_cast hrank
  have hscalePos : (0 : ℝ) < (rank : ℝ) * weight label := mul_pos hrankPos (hpos label)
  rw [eq_div_iff (ne_of_gt hscalePos)]
  linarith [simplexTieAtom_leverage_identity hrank weight hpos hsum label]

/-! ### The spiked weight vector on seven atoms

`sevenIntoFourBalanced = ![0, 1, 2, 3, 1, 2, 3]` puts atom `0` alone in its class and
pairs the remaining six. Loading atom `0` with `spikeWeight` and splitting the rest
evenly makes the class totals `(spikeWeight, s, s, s)` with `s = (1 − spikeWeight)/3`,
so the singleton class total IS the spike weight and the leverage identity applies to
it directly. -/

/-- The weight vector of the spiked class tie: `spikeWeight` on atom `0`, the
remaining mass split evenly over the other six atoms. -/
noncomputable def spikeClassWeight (spikeWeight : ℝ) : Fin 7 → ℝ :=
  ![spikeWeight, (1 - spikeWeight) / 6, (1 - spikeWeight) / 6, (1 - spikeWeight) / 6,
    (1 - spikeWeight) / 6, (1 - spikeWeight) / 6, (1 - spikeWeight) / 6]

theorem spikeClassWeight_zero (spikeWeight : ℝ) :
    spikeClassWeight spikeWeight 0 = spikeWeight := rfl

/-- Every entry is either the spike weight or the common share: the bookkeeping of the
family, isolated once. -/
theorem spikeClassWeight_apply (spikeWeight : ℝ) (atomIndex : Fin 7) :
    spikeClassWeight spikeWeight atomIndex = spikeWeight
      ∨ spikeClassWeight spikeWeight atomIndex = (1 - spikeWeight) / 6 := by
  fin_cases atomIndex
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

theorem spikeClassWeight_pos {spikeWeight : ℝ} (hspikePos : 0 < spikeWeight)
    (hspikeLt : spikeWeight < 1) (atomIndex : Fin 7) :
    0 < spikeClassWeight spikeWeight atomIndex := by
  rcases spikeClassWeight_apply spikeWeight atomIndex with hvalue | hvalue
  · rw [hvalue]; exact hspikePos
  · rw [hvalue]; linarith

theorem spikeClassWeight_sum (spikeWeight : ℝ) :
    ∑ atomIndex, spikeClassWeight spikeWeight atomIndex = 1 := by
  simp only [Fin.sum_univ_seven, spikeClassWeight, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
  ring

/-- The singleton class of `sevenIntoFourBalanced` carries exactly the spike weight. -/
theorem classTotalWeight_spikeClassWeight_zero (spikeWeight : ℝ) :
    classTotalWeight sevenIntoFourBalanced (spikeClassWeight spikeWeight) 0
      = spikeWeight := by
  rw [classTotalWeight_eq, Finset.sum_filter, Fin.sum_univ_seven]
  simp only [sevenIntoFourBalanced, spikeClassWeight, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
  norm_num [Fin.ext_iff]

/-! ### The curve of exact ties -/

/-- **The spiked class tie at `(7,3)`**: the shipped class-tie section at the
`(2,2,2,1)` partition, loaded with `spikeWeight` on the singleton class. -/
noncomputable def spikeClassTieDesign {spikeWeight : ℝ} (hspikePos : 0 < spikeWeight)
    (hspikeLt : spikeWeight < 1) : WeightedDesign 7 3 :=
  splitClassDesign sevenIntoFourBalanced (spikeClassWeight spikeWeight) (by norm_num)
    sevenIntoFourBalanced_surjective (spikeClassWeight_pos hspikePos hspikeLt)
    (spikeClassWeight_sum spikeWeight)

section SpikeClassTie

variable {spikeWeight : ℝ} (hspikePos : 0 < spikeWeight) (hspikeLt : spikeWeight < 1)

theorem spikeClassTieDesign_weight :
    (spikeClassTieDesign hspikePos hspikeLt).weight = spikeClassWeight spikeWeight := rfl

theorem spikeClassTieDesign_atom (atomIndex : Fin 7) :
    (spikeClassTieDesign hspikePos hspikeLt).atom atomIndex
      = simplexTieAtom (classTotalWeight sevenIntoFourBalanced (spikeClassWeight spikeWeight))
          (sevenIntoFourBalanced atomIndex) := rfl

/-- **The curve lies in the tie stratum at every admissible spike weight** — the
shipped `splitClassDesign_isTie`, instantiated. -/
theorem spikeClassTieDesign_isTie : IsTie (spikeClassTieDesign hspikePos hspikeLt) :=
  splitClassDesign_isTie sevenIntoFourBalanced (spikeClassWeight spikeWeight) (by norm_num)
    sevenIntoFourBalanced_surjective (spikeClassWeight_pos hspikePos hspikeLt)
    (spikeClassWeight_sum spikeWeight)

/-- **The curve is all-heavy at every admissible spike weight**, so it lies inside the
stratum `DiscriminantCovering 7` actually quantifies over. Every class total is below
one on the open simplex, and at rank three that forces every leverage above one. -/
theorem spikeClassTieDesign_allHeavy : AllHeavy (spikeClassTieDesign hspikePos hspikeLt) := by
  intro atomIndex
  rw [spikeClassTieDesign_atom hspikePos hspikeLt atomIndex]
  exact one_lt_leverage_simplexTieAtom (rank := 3) (by norm_num) _
    (classTotalWeight_pos sevenIntoFourBalanced_surjective
      (spikeClassWeight_pos hspikePos hspikeLt))
    (classTotalWeight_sum (spikeClassWeight_sum spikeWeight)) _

/-- **The spike leverage in closed form**, `(2 + spikeWeight)/(3·spikeWeight)`: the
singleton class total is the spike weight, and the corank-one identity does the rest.
It diverges as `spikeWeight → 0` while the design stays an exact tie throughout. -/
theorem spikeClassTieDesign_spike_leverage :
    leverageOf ((spikeClassTieDesign hspikePos hspikeLt).atom 0)
      = (2 + spikeWeight) / (3 * spikeWeight) := by
  rw [spikeClassTieDesign_atom hspikePos hspikeLt 0]
  have hlabel : sevenIntoFourBalanced 0 = 0 := rfl
  rw [hlabel, leverage_simplexTieAtom_eq (rank := 3) (by norm_num) _
    (classTotalWeight_pos sevenIntoFourBalanced_surjective
      (spikeClassWeight_pos hspikePos hspikeLt))
    (classTotalWeight_sum (spikeClassWeight_sum spikeWeight)) 0,
    classTotalWeight_spikeClassWeight_zero]
  norm_num

end SpikeClassTie

/-! ### The zero-margin statement, at every cap -/

/-- **AN ALL-HEAVY `(7,3)` EXACT TIE WITH AN ATOM OF LEVERAGE AT LEAST `cap`, FOR
EVERY `cap`.** The witness is the spiked class tie at
`spikeWeight = 2/(3·max cap 2 − 1)`, whose singleton atom then has leverage exactly
`max cap 2`. Since a tie admits no strictly dominating `3`-subset, the heavy-atom
hypothesis of `Gtz.HeavyAtomCovering` is triggered at a design where its conclusion
can hold only with EQUALITY in the tie leg. There is no margin to bound below at any
leverage scale.

SCOPE. This does not refute `HeavyAtomCovering cap 7`, and it is not evidence against
it: `IsTie` supplies a weakly dominating `3`-subset, so the conclusion of the brick
HOLDS on the whole curve. What is refuted is every proof strategy that would produce
a strict inequality or a uniform margin. -/
theorem exists_allHeavy_isTie_seven_with_leverage_ge (cap : ℝ) :
    ∃ (D : WeightedDesign 7 3) (heavyIndex : Fin 7),
      AllHeavy D ∧ cap ≤ leverageOf (D.atom heavyIndex) ∧ IsTie D := by
  have hcapTwo : (2 : ℝ) ≤ max cap 2 := le_max_right _ _
  have hcapLe : cap ≤ max cap 2 := le_max_left _ _
  have hdenomPos : (0 : ℝ) < 3 * max cap 2 - 1 := by linarith
  set spikeWeight : ℝ := 2 / (3 * max cap 2 - 1) with hspikeDef
  have hspikePos : 0 < spikeWeight := by rw [hspikeDef]; positivity
  have hspikeLt : spikeWeight < 1 := by
    rw [hspikeDef, div_lt_one hdenomPos]; linarith
  refine ⟨spikeClassTieDesign hspikePos hspikeLt, 0,
    spikeClassTieDesign_allHeavy hspikePos hspikeLt, ?_,
    spikeClassTieDesign_isTie hspikePos hspikeLt⟩
  rw [spikeClassTieDesign_spike_leverage hspikePos hspikeLt, hspikeDef]
  have hvalue : (2 + 2 / (3 * max cap 2 - 1)) / (3 * (2 / (3 * max cap 2 - 1)))
      = max cap 2 := by
    field_simp
    ring
  rw [hvalue]
  exact hcapLe

/-- **The uniform point of the curve carries leverage exactly three**: at
`spikeWeight = 1/4` all four class totals are `1/4`, so this is the tie the split
tetrahedron already exhibits, and the curve above is a genuine deformation of it
rather than a new species. -/
theorem spikeClassTieDesign_quarter_spike_leverage :
    leverageOf ((spikeClassTieDesign (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (1 : ℝ) / 4 < 1)).atom 0) = 3 := by
  rw [spikeClassTieDesign_spike_leverage]
  norm_num

/-! ### The strict readings, refuted at every cap -/

/-- **The STRICT reading of the heavy-atom brick**: an atom of leverage at least `cap`
forces a `3`-subset that dominates STRICTLY. This is what any argument producing a
uniform positive margin — a barrier, a concentration bound, an interlacing estimate,
a strictly-positive Positivstellensatz certificate — would deliver. It is strictly
stronger than `Gtz.HeavyAtomCovering`, which asks only for both legs nonnegative. -/
def HeavyAtomStrictCovering (cap : ℝ) (size : ℕ) : Prop :=
  ∀ D : WeightedDesign size 3, AllHeavy D → ∀ heavyIndex : Fin size,
    cap ≤ leverageOf (D.atom heavyIndex) →
      ∃ C : Finset (Fin size), C.card = 3 ∧ (subsetSum D C - 1).PosDef

/-- The strict reading is stronger than the brick: a strictly dominating triple is in
particular a dominating triple, and at an all-heavy design that is both legs
nonnegative. Recorded so nobody proves the wrong one of the two by accident. -/
theorem heavyAtomCovering_of_heavyAtomStrictCovering {cap : ℝ} {size : ℕ}
    (hstrict : HeavyAtomStrictCovering cap size) : HeavyAtomCovering cap size := by
  intro D hheavy heavyIndex hcap
  obtain ⟨C, hcard, hposDef⟩ := hstrict D hheavy heavyIndex hcap
  obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
    hsubsetEq⟩ := Finset.card_eq_three.mp hcard
  subst hsubsetEq
  refine ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct, ?_⟩
  exact (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond hpairDistinct
    (hheavy pivot)).mp hposDef.posSemidef

/-- **THE STRICT HEAVY-ATOM BRICK IS FALSE AT EVERY CAP.** No leverage threshold
forces a strictly dominating triple, because the tie curve puts an exact `(7,3)` tie
at every leverage scale. So the pivot-free brick, if it is provable at all, is
provable only with EQUALITY available in the tie leg — every strict or uniform-margin
route to it is dead before it is written, exactly as `not_gtzWeightedFloor_sevenThree_of_one_lt`
already says of the conjecture itself. -/
theorem not_heavyAtomStrictCovering (cap : ℝ) : ¬ HeavyAtomStrictCovering cap 7 := by
  intro hstrictCovering
  obtain ⟨D, heavyIndex, hheavy, hcap, htie⟩ :=
    exists_allHeavy_isTie_seven_with_leverage_ge cap
  obtain ⟨C, hcard, hposDef⟩ := hstrictCovering D hheavy heavyIndex hcap
  exact htie.2 C hcard hposDef

/-- **The STRICT reading of the capped half**, for the same reason: a design all of
whose leverages are below `cap` has a strictly dominating triple. -/
def CappedStrictCovering (cap : ℝ) (size : ℕ) : Prop :=
  ∀ D : WeightedDesign size 3, AllHeavy D →
    (∀ atomIndex : Fin size, leverageOf (D.atom atomIndex) < cap) →
      ∃ C : Finset (Fin size), C.card = 3 ∧ (subsetSum D C - 1).PosDef

/-- **THE STRICT CAPPED BRICK IS FALSE AT EVERY CAP ABOVE THREE.** The uniform point
of the tie curve has every leverage exactly `3`, so it sits inside every leverage cap
above `3` and is still an exact tie. Together with `not_heavyAtomStrictCovering` this
says the zero-margin burden is present on BOTH hypotheses of
`rank_three_of_heavyAtomCovering_of_capped` simultaneously: compactifying moves the
tightness, it does not remove it. -/
theorem not_cappedStrictCovering_of_three_lt {cap : ℝ} (hcap : 3 < cap) :
    ¬ CappedStrictCovering cap 7 := by
  intro hcappedCovering
  have hspikePos : (0 : ℝ) < 1 / 4 := by norm_num
  have hspikeLt : (1 : ℝ) / 4 < 1 := by norm_num
  have hleverage : ∀ atomIndex : Fin 7,
      leverageOf ((spikeClassTieDesign hspikePos hspikeLt).atom atomIndex) < cap := by
    intro atomIndex
    rw [spikeClassTieDesign_atom hspikePos hspikeLt atomIndex,
      leverage_simplexTieAtom_eq (rank := 3) (by norm_num) _
        (classTotalWeight_pos sevenIntoFourBalanced_surjective
          (spikeClassWeight_pos hspikePos hspikeLt))
        (classTotalWeight_sum (spikeClassWeight_sum (1 / 4)))]
    have htotalValue : classTotalWeight sevenIntoFourBalanced (spikeClassWeight (1 / 4))
        (sevenIntoFourBalanced atomIndex) = 1 / 4 := by
      rw [classTotalWeight_eq, Finset.sum_filter, Fin.sum_univ_seven]
      fin_cases atomIndex <;>
        simp only [sevenIntoFourBalanced, spikeClassWeight, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val,
          Matrix.tail_cons] <;> norm_num [Fin.ext_iff]
    rw [htotalValue]
    norm_num
    linarith
  obtain ⟨C, hcard, hposDef⟩ := hcappedCovering (spikeClassTieDesign hspikePos hspikeLt)
    (spikeClassTieDesign_allHeavy hspikePos hspikeLt) hleverage
  exact (spikeClassTieDesign_isTie hspikePos hspikeLt).2 C hcard hposDef

end Gtz
