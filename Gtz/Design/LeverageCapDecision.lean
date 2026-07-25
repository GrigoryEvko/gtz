/-
# The leverage cap: an exact heavy-pivot decision, and why no leverage threshold exists

`Gtz.Quantitative.DiscriminantSystem` reduced rank-three GTZ to `DiscriminantCovering 7`:
every all-heavy weighted `(7,3)` design owns a triple with `discriminantTrace ≥ 0` and
`discriminantTie ≥ 0`. That parameter space is NOT compact — leverages are unbounded,
since a weight may shrink while its weighted leverage stays fixed — so every
Positivstellensatz / quantifier-elimination / interval route wants a threshold theorem
"a large enough leverage forces a dominating triple through that atom", which would
confine the open content to `{all leverages < cap}`. This file settles that programme,
in both directions.

**The decision theorem is exact, and it is not a leverage bound.** Writing
`pairMinorOffPivot` for the pivot-free `2×2` minor `a_Q a_R − p_QR²` of `Gram − I` at the
pair and `pivotTiltForm` for the adjugate form of that block evaluated at the pivot's two
pairings, the whole discriminant system collapses on `{0 < pairMinorOffPivot}` to the
single cubic leg, by the pure-`ring` certificate

  `pairMinorOffPivot * discriminantTrace = (a_Q + a_R) * discriminantTie + square + square`

(`pairMinorOffPivot_mul_discriminantTrace`). Since
`discriminantTie = heavyExcess pivot * pairMinorOffPivot − pivotTiltForm`, the test IS an
explicit inequality on the heavy atom's excess
(`dominates_of_heavyExcess_mul_pairMinorOffPivot_ge`), equivalently a threshold on the
pivot leverage at the level `pairMinorOffPivot / deflatedPairMinor`
(`dominates_of_deflatedPairMinorAtLeverage_ge`). The regular tetrahedron sits on it with
equality, so the threshold is sharp.

**But that threshold is not bounded over the parameter space, and no leverage cap can
replace it.** `liftedMercedesDesign` is an exactly-normalised two-parameter family of
all-heavy weighted `(7,3)` designs — an axial spike of weight `w` plus three lifted
Mercedes plane directions, each doubled — in which

* the spike leverage is `(1 − (1−w)·lift²)/w`, unbounded as `w → 0`
  (`liftedMercedesDesign_spike_leverage`);
* NO triple containing the spike dominates, at any `w`
  (`liftedMercedesDesign_not_dominates_spike_triple`), because the tie leg of a
  cross-direction spike triple equals `(6·planeHalf² − 1)·(1 − 3·lift²)` exactly
  (`discriminantTie_eq_crossValue_of_spikeGramData`) — a quantity in which `spikeHeight`
  has cancelled, so the verdict is free of the spike leverage altogether;
* the spike-free triple of three distinct directions DOES dominate
  (`liftedMercedesDesign_dominates_directionTriple`), with tie leg
  `(6·planeHalf² − 1)²·(3·lift² − 1)` (`discriminantTie_eq_crossTripleValue`): the same
  factor `3·lift² − 1` with the opposite sign. A two-sided dichotomy, tight at
  `3·lift² = 1`;
* and the deflation is NOT degenerate — the deflated pair minor at the pivot leverage is
  `(6·planeHalf² − 1)(2·planeHalf² − lift²) > 0`, as the proven `gtz_rank_two` forces, yet
  it stays strictly below the ambient pair minor at every leverage
  (`deflation_pos_and_below_threshold_of_spikeGramData`). The sharp threshold of the
  decision theorem is finite here and simply never met, because it grows with the leverage
  it is compared against.

Hence `¬ HeavyPivotCovering cap 7` for EVERY `cap` (`not_heavyPivotCovering`): the
requested brick is false, not merely unproven, and GTZ survives on the family through a
triple that avoids the heavy atom. The compactification corollary is therefore stated
against the pivot-free hypothesis `HeavyAtomCovering`, where it is unconditional
(`discriminantCovering_of_heavyAtomCovering_of_capped`,
`rank_three_of_heavyAtomCovering_of_capped`), and that hypothesis is the honest target:
the brick to aim at is the score dichotomy — either the heavy atom is usable, or the
remaining six atoms carry a dominating triple.

**What replaces the leverage.** Along the family the leverage SCORE
`weight · leverage = 1 − (1−w)·lift²` stays interior while the leverage diverges
(`liftedMercedesDesign_spike_leverageScore`), so the blow-up is a coordinate artefact of
a weight reaching the simplex boundary, not a geometric degeneration. The score, not the
leverage, is the variable a compactification must use.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Reduction.Reductions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

variable {m : ℕ}

/-! ### The pivot-free pair minor, the tilt form, and the deflated minor -/

/-- The **pair minor off the pivot** `a_Q a_R − p_QR²`: the `2×2` principal minor of
`Gram − I` at the pair. It carries NO pivot, and it is the pivot-free half of the
domination test. -/
def pairMinorOffPivot (D : WeightedDesign m 3) (pairFirst pairSecond : Fin m) : ℝ :=
  heavyExcess D pairFirst * heavyExcess D pairSecond
    - atomPairing D pairFirst pairSecond ^ 2

/-- The **pivot tilt form**: the adjugate form of the pair's `2×2` excess block evaluated
at the pivot's two pairings, `a_R p_PQ² − 2 p_QR p_PQ p_PR + a_Q p_PR²`. It is the amount
by which deflating along the pivot direction shrinks the pair minor, measured at scale
`leverageOf (D.atom pivot)`. -/
def pivotTiltForm (D : WeightedDesign m 3) (pivot pairFirst pairSecond : Fin m) : ℝ :=
  heavyExcess D pairSecond * atomPairing D pivot pairFirst ^ 2
    - 2 * atomPairing D pairFirst pairSecond * atomPairing D pivot pairFirst
        * atomPairing D pivot pairSecond
    + heavyExcess D pairFirst * atomPairing D pivot pairSecond ^ 2

/-- The **deflated pair minor at the pivot leverage**: the pair minor of the design
projected onto the orthogonal complement of the pivot direction, multiplied by
`leverageOf (D.atom pivot)` so that no square root and no division appears. -/
def deflatedPairMinorAtLeverage (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) : ℝ :=
  leverageOf (D.atom pivot) * pairMinorOffPivot D pairFirst pairSecond
    - pivotTiltForm D pivot pairFirst pairSecond

/-- The tie leg IS the pivot's excess times the pair minor, minus the tilt form — the
`2×2` matrix-determinant lemma read in the six Gram scalars of the triple. -/
theorem discriminantTie_eq_heavyExcess_mul_pairMinorOffPivot_sub_tilt (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    discriminantTie D pivot pairFirst pairSecond
      = heavyExcess D pivot * pairMinorOffPivot D pairFirst pairSecond
        - pivotTiltForm D pivot pairFirst pairSecond := by
  simp only [discriminantTie, pairMinorOffPivot, pivotTiltForm]

/-- **The threshold reading of the tie leg**: the tie leg is the excess of the deflated
pair minor over the ambient one, so `0 ≤ discriminantTie` is literally the statement that
the pair minor survives deflation along the pivot at scale one. -/
theorem discriminantTie_eq_deflatedPairMinorAtLeverage_sub_pairMinorOffPivot
    (D : WeightedDesign m 3) (pivot pairFirst pairSecond : Fin m) :
    discriminantTie D pivot pairFirst pairSecond
      = deflatedPairMinorAtLeverage D pivot pairFirst pairSecond
        - pairMinorOffPivot D pairFirst pairSecond := by
  rw [discriminantTie_eq_heavyExcess_mul_pairMinorOffPivot_sub_tilt,
    deflatedPairMinorAtLeverage, heavyExcess]
  ring

/-! ### The collapse certificate: the trace leg is redundant off the pivot -/

/-- **THE COLLAPSE CERTIFICATE** (pure `ring`): the pair minor times the trace leg equals
the pair's excess sum times the tie leg, plus two explicit squares. So on
`0 < pairMinorOffPivot` the quadratic trace leg is a consequence of the cubic tie leg and
the discriminant system degenerates to its cubic half. -/
theorem pairMinorOffPivot_mul_discriminantTrace (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    pairMinorOffPivot D pairFirst pairSecond
        * discriminantTrace D pivot pairFirst pairSecond
      = (heavyExcess D pairFirst + heavyExcess D pairSecond)
            * discriminantTie D pivot pairFirst pairSecond
        + (heavyExcess D pairSecond * atomPairing D pivot pairFirst
            - atomPairing D pairFirst pairSecond * atomPairing D pivot pairSecond) ^ 2
        + (heavyExcess D pairFirst * atomPairing D pivot pairSecond
            - atomPairing D pairFirst pairSecond * atomPairing D pivot pairFirst) ^ 2 := by
  simp only [pairMinorOffPivot, discriminantTrace, discriminantTie]
  ring

/-- The trace leg is nonnegative as soon as the pair minor is positive and the tie leg is
nonnegative: the certificate divided by the positive pair minor. -/
theorem discriminantTrace_nonneg_of_pairMinorOffPivot_pos (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m}
    (hfirstHeavy : 1 < leverageOf (D.atom pairFirst))
    (hsecondHeavy : 1 < leverageOf (D.atom pairSecond))
    (hminorPos : 0 < pairMinorOffPivot D pairFirst pairSecond)
    (htieNonneg : 0 ≤ discriminantTie D pivot pairFirst pairSecond) :
    0 ≤ discriminantTrace D pivot pairFirst pairSecond := by
  have hfirstPos : 0 < heavyExcess D pairFirst := by rw [heavyExcess]; linarith
  have hsecondPos : 0 < heavyExcess D pairSecond := by rw [heavyExcess]; linarith
  have hproduct : 0 ≤ pairMinorOffPivot D pairFirst pairSecond
      * discriminantTrace D pivot pairFirst pairSecond := by
    rw [pairMinorOffPivot_mul_discriminantTrace]
    have hleadTerm : 0 ≤ (heavyExcess D pairFirst + heavyExcess D pairSecond)
        * discriminantTie D pivot pairFirst pairSecond :=
      mul_nonneg (by linarith) htieNonneg
    have hsquareFirst := sq_nonneg (heavyExcess D pairSecond * atomPairing D pivot pairFirst
      - atomPairing D pairFirst pairSecond * atomPairing D pivot pairSecond)
    have hsquareSecond := sq_nonneg (heavyExcess D pairFirst * atomPairing D pivot pairSecond
      - atomPairing D pairFirst pairSecond * atomPairing D pivot pairFirst)
    linarith
  exact (mul_nonneg_iff_of_pos_left hminorPos).mp hproduct

/-! ### The heavy-pivot decision theorem -/

/-- **THE HEAVY-PIVOT DECISION THEOREM**: an explicit inequality on the heavy atom's
excess decides domination of a triple through it. On the positive-pair-minor stratum,
`pivotTiltForm ≤ heavyExcess pivot * pairMinorOffPivot` forces both legs of the
discriminant system, hence domination. No matrices, no test vectors, no analysis. -/
theorem dominates_of_heavyExcess_mul_pairMinorOffPivot_ge (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    (hfirstHeavy : 1 < leverageOf (D.atom pairFirst))
    (hsecondHeavy : 1 < leverageOf (D.atom pairSecond))
    (hminorPos : 0 < pairMinorOffPivot D pairFirst pairSecond)
    (hexcessLarge : pivotTiltForm D pivot pairFirst pairSecond
      ≤ heavyExcess D pivot * pairMinorOffPivot D pairFirst pairSecond) :
    Dominates D {pivot, pairFirst, pairSecond} := by
  have htieNonneg : 0 ≤ discriminantTie D pivot pairFirst pairSecond := by
    rw [discriminantTie_eq_heavyExcess_mul_pairMinorOffPivot_sub_tilt]
    linarith
  exact (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond hpairDistinct
    hpivotHeavy).mpr
    ⟨discriminantTrace_nonneg_of_pairMinorOffPivot_pos D hfirstHeavy hsecondHeavy hminorPos
      htieNonneg, htieNonneg⟩

/-- **The decision is an equivalence**: on the positive-pair-minor stratum of an all-heavy
design, domination of a triple IS the excess inequality. There is no slack to exploit —
the trace leg carries no information there. -/
theorem dominates_iff_heavyExcess_mul_pairMinorOffPivot_ge (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    (hfirstHeavy : 1 < leverageOf (D.atom pairFirst))
    (hsecondHeavy : 1 < leverageOf (D.atom pairSecond))
    (hminorPos : 0 < pairMinorOffPivot D pairFirst pairSecond) :
    Dominates D {pivot, pairFirst, pairSecond}
      ↔ pivotTiltForm D pivot pairFirst pairSecond
          ≤ heavyExcess D pivot * pairMinorOffPivot D pairFirst pairSecond := by
  constructor
  · intro hdominates
    have htie := ((dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
      hpairDistinct hpivotHeavy).mp hdominates).2
    rw [discriminantTie_eq_heavyExcess_mul_pairMinorOffPivot_sub_tilt] at htie
    linarith
  · exact dominates_of_heavyExcess_mul_pairMinorOffPivot_ge D hpivotFirst hpivotSecond
      hpairDistinct hpivotHeavy hfirstHeavy hsecondHeavy hminorPos

/-- **The same decision, read as a threshold on the pivot leverage.** The triple dominates
as soon as the pair minor survives deflation along the pivot direction at scale one; with
both minors positive that reads
`leverageOf (D.atom pivot) ≥ pairMinorOffPivot / deflatedPairMinor`. -/
theorem dominates_of_deflatedPairMinorAtLeverage_ge (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    (hfirstHeavy : 1 < leverageOf (D.atom pairFirst))
    (hsecondHeavy : 1 < leverageOf (D.atom pairSecond))
    (hminorPos : 0 < pairMinorOffPivot D pairFirst pairSecond)
    (hthreshold : pairMinorOffPivot D pairFirst pairSecond
      ≤ deflatedPairMinorAtLeverage D pivot pairFirst pairSecond) :
    Dominates D {pivot, pairFirst, pairSecond} := by
  refine dominates_of_heavyExcess_mul_pairMinorOffPivot_ge D hpivotFirst hpivotSecond
    hpairDistinct hpivotHeavy hfirstHeavy hsecondHeavy hminorPos ?_
  have hidentity := discriminantTie_eq_deflatedPairMinorAtLeverage_sub_pairMinorOffPivot
    D pivot pairFirst pairSecond
  rw [discriminantTie_eq_heavyExcess_mul_pairMinorOffPivot_sub_tilt] at hidentity
  linarith

/-! ### Calibration: the regular tetrahedron sits on the threshold with equality -/

theorem tetraDesign_pairMinorOffPivot : pairMinorOffPivot tetraDesign 1 2 = 3 := by
  rw [pairMinorOffPivot, tetraDesign_heavyExcess, tetraDesign_heavyExcess,
    tetraDesign_atomPairing_oneTwo]
  norm_num

theorem tetraDesign_pivotTiltForm : pivotTiltForm tetraDesign 0 1 2 = 6 := by
  rw [pivotTiltForm, tetraDesign_heavyExcess, tetraDesign_heavyExcess,
    tetraDesign_atomPairing_zeroOne, tetraDesign_atomPairing_zeroTwo,
    tetraDesign_atomPairing_oneTwo]
  norm_num

theorem tetraDesign_deflatedPairMinorAtLeverage :
    deflatedPairMinorAtLeverage tetraDesign 0 1 2 = 3 := by
  rw [deflatedPairMinorAtLeverage, tetraDesign_leverage, tetraDesign_pairMinorOffPivot,
    tetraDesign_pivotTiltForm]
  norm_num

/-- **The threshold is sharp.** At the tetrahedron the deflated pair minor at the pivot
leverage equals the ambient pair minor exactly, so `dominates_of_deflatedPairMinorAtLeverage_ge`
fires with equality — the same tie as `tetraDesign_discriminantTie`. -/
theorem tetraDesign_threshold_tight :
    pairMinorOffPivot tetraDesign 1 2 = deflatedPairMinorAtLeverage tetraDesign 0 1 2 := by
  rw [tetraDesign_pairMinorOffPivot, tetraDesign_deflatedPairMinorAtLeverage]

/-! ### The three covering hypotheses a leverage cap can be built on -/

/-- **The capped covering**: the discriminant covering restricted to designs all of whose
leverages are below `cap`. This is the statement on a COMPACT parameter set — with every
leverage bounded, the all-heavy `(size,3)` parameter space is a compact semialgebraic set,
so Positivstellensatz, quantifier elimination and interval methods all apply. -/
def CappedDiscriminantCovering (cap : ℝ) (size : ℕ) : Prop :=
  ∀ D : WeightedDesign size 3, AllHeavy D →
    (∀ atomIndex : Fin size, leverageOf (D.atom atomIndex) < cap) →
      ∃ pivot pairFirst pairSecond : Fin size,
        pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ 0 ≤ discriminantTrace D pivot pairFirst pairSecond
          ∧ 0 ≤ discriminantTie D pivot pairFirst pairSecond

/-- **The heavy-atom covering at `cap`**: one atom of leverage at least `cap` already
forces the covering. The witnessing triple need NOT contain that atom — this is the
pivot-FREE hypothesis, and `not_heavyPivotCovering` below shows it is the only shape that
can survive. It is NOT refuted by the family of that theorem: every member is covered,
through its spike-free triple. -/
def HeavyAtomCovering (cap : ℝ) (size : ℕ) : Prop :=
  ∀ D : WeightedDesign size 3, AllHeavy D → ∀ heavyIndex : Fin size,
    cap ≤ leverageOf (D.atom heavyIndex) →
      ∃ pivot pairFirst pairSecond : Fin size,
        pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ 0 ≤ discriminantTrace D pivot pairFirst pairSecond
          ∧ 0 ≤ discriminantTie D pivot pairFirst pairSecond

/-- **The heavy-PIVOT covering at `cap`**: the strong form the compactification programme
asked for — an atom of leverage at least `cap` lies IN a dominating triple. This is the
brick that `not_heavyPivotCovering` refutes at every `cap`. -/
def HeavyPivotCovering (cap : ℝ) (size : ℕ) : Prop :=
  ∀ D : WeightedDesign size 3, AllHeavy D → ∀ heavyIndex : Fin size,
    cap ≤ leverageOf (D.atom heavyIndex) →
      ∃ pairFirst pairSecond : Fin size,
        heavyIndex ≠ pairFirst ∧ heavyIndex ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ Dominates D {heavyIndex, pairFirst, pairSecond}

/-- The pivot form is the stronger hypothesis: a dominating triple through the heavy atom
is in particular a triple whose two discriminant legs are nonnegative. -/
theorem heavyAtomCovering_of_heavyPivotCovering {cap : ℝ} {size : ℕ}
    (hpivotCovering : HeavyPivotCovering cap size) : HeavyAtomCovering cap size := by
  intro D hheavy heavyIndex hcap
  obtain ⟨pairFirst, pairSecond, hheavyFirst, hheavySecond, hpairDistinct, hdominates⟩ :=
    hpivotCovering D hheavy heavyIndex hcap
  have hlegs := (dominates_triple_iff_discriminantSystem D hheavyFirst hheavySecond
    hpairDistinct (hheavy heavyIndex)).mp hdominates
  exact ⟨heavyIndex, pairFirst, pairSecond, hheavyFirst, hheavySecond, hpairDistinct,
    hlegs.1, hlegs.2⟩

/-! ### The compactification corollary -/

/-- **THE COMPACTIFICATION COROLLARY.** A heavy-atom decision at `cap` reduces the whole
covering to its restriction to the leverage-capped — hence compact — parameter set. The
case split is on whether some atom reaches `cap`, so the implication is unconditional
given the two hypotheses. -/
theorem discriminantCovering_of_heavyAtomCovering_of_capped {cap : ℝ}
    (hheavyCovering : HeavyAtomCovering cap 7) (hcapped : CappedDiscriminantCovering cap 7) :
    DiscriminantCovering 7 := by
  intro D hheavy
  by_cases hreachesCap : ∃ atomIndex : Fin 7, cap ≤ leverageOf (D.atom atomIndex)
  · obtain ⟨heavyIndex, hcapLe⟩ := hreachesCap
    exact hheavyCovering D hheavy heavyIndex hcapLe
  · push Not at hreachesCap
    exact hcapped D hheavy hreachesCap

/-- **Rank three from a capped covering.** Chaining
`rank_three_of_discriminantCovering_seven`: with a heavy-atom decision in hand, the entire
1997 conjecture at rank three is a statement about a COMPACT semialgebraic set. -/
theorem rank_three_of_heavyAtomCovering_of_capped {cap : ℝ}
    (hheavyCovering : HeavyAtomCovering cap 7) (hcapped : CappedDiscriminantCovering cap 7) :
    GtzWeightedAll 3 :=
  rank_three_of_discriminantCovering_seven
    (discriminantCovering_of_heavyAtomCovering_of_capped hheavyCovering hcapped)

/-- The same corollary through the pivot hypothesis, for the record: it is a genuine
consequence, and `not_heavyPivotCovering` is what makes it unusable. -/
theorem rank_three_of_heavyPivotCovering_of_capped {cap : ℝ}
    (hpivotCovering : HeavyPivotCovering cap 7) (hcapped : CappedDiscriminantCovering cap 7) :
    GtzWeightedAll 3 :=
  rank_three_of_heavyAtomCovering_of_capped
    (heavyAtomCovering_of_heavyPivotCovering hpivotCovering) hcapped

/-! ### The two normalisation brackets of the spiked lifted-Mercedes family

Both are exact consequences of the family's two normalisation equations — the plane
Parseval block `2(1−w)·planeHalf² = 1` and the axial block
`w·spikeHeight² + (1−w)·lift² = 1` — obtained by solving them for `planeHalf²` and
`spikeHeight²` and clearing denominators. The first bracket is the whole content of the
negative result: it is FREE of the spike leverage. -/

/-- **The cross bracket.** For a spike triple whose pair uses two DISTINCT plane
directions, the tie leg is `(6·planeHalf² − 1)` times this bracket — and the bracket is
exactly `1 − 3·lift²`, with no trace of `spikeHeight` left. So the sign of the tie leg is
independent of the spike leverage, and negative precisely when `1 < 3·lift²`. -/
theorem crossBracketValue (spikeWeight planeHalfSq liftSq spikeHeightSq : ℝ)
    (hweightNe : spikeWeight ≠ 0) (hslackNe : (1 : ℝ) - spikeWeight ≠ 0)
    (hplaneNormalized : 2 * (1 - spikeWeight) * planeHalfSq = 1)
    (hspikeNormalized : spikeWeight * spikeHeightSq + (1 - spikeWeight) * liftSq = 1) :
    (spikeHeightSq - 1) * (2 * planeHalfSq + 2 * liftSq - 1) - 2 * spikeHeightSq * liftSq
      = 1 - 3 * liftSq := by
  have hplaneValue : planeHalfSq = 1 / (2 * (1 - spikeWeight)) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hslackNe)]
    linear_combination hplaneNormalized
  have hspikeValue : spikeHeightSq = (1 - (1 - spikeWeight) * liftSq) / spikeWeight := by
    rw [eq_div_iff hweightNe]
    linear_combination hspikeNormalized
  rw [hplaneValue, hspikeValue]
  field_simp
  ring

/-- **The repeated-direction bracket.** For a spike triple whose pair is a REPEATED plane
direction the tie leg is minus this bracket, and the bracket scaled by the spike weight is
`(4 − 6·lift²) + (1−w)·(3·lift² − 1)` — positive whenever `1 < 3·lift² ≤ 2`, again with no
trace of the spike leverage. -/
theorem repeatBracketValue (spikeWeight planeHalfSq liftSq spikeHeightSq : ℝ)
    (hweightNe : spikeWeight ≠ 0) (hslackNe : (1 : ℝ) - spikeWeight ≠ 0)
    (hplaneNormalized : 2 * (1 - spikeWeight) * planeHalfSq = 1)
    (hspikeNormalized : spikeWeight * spikeHeightSq + (1 - spikeWeight) * liftSq = 1) :
    spikeWeight * ((spikeHeightSq - 1) * (8 * planeHalfSq + 2 * liftSq - 1)
        - 2 * spikeHeightSq * liftSq)
      = 4 - 6 * liftSq + (1 - spikeWeight) * (3 * liftSq - 1) := by
  have hplaneValue : planeHalfSq = 1 / (2 * (1 - spikeWeight)) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hslackNe)]
    linear_combination hplaneNormalized
  have hspikeValue : spikeHeightSq = (1 - (1 - spikeWeight) * liftSq) / spikeWeight := by
    rw [eq_div_iff hweightNe]
    linear_combination hspikeNormalized
  rw [hplaneValue, hspikeValue]
  field_simp
  ring

/-! ### Consequences of the two normalisations, as scalar bounds -/

theorem planeHalfSq_pos {spikeWeight planeHalf : ℝ}
    (hplaneNormalized : 2 * (1 - spikeWeight) * planeHalf ^ 2 = 1) : 0 < planeHalf ^ 2 := by
  rcases (sq_nonneg planeHalf).lt_or_eq with hstrict | hzero
  · exact hstrict
  · rw [← hzero] at hplaneNormalized
    norm_num at hplaneNormalized

/-- The plane normalisation forces `planeHalf² > 1/2`: the plane directions overshoot the
Mercedes level, which is what leaves the deflated pair minor positive. -/
theorem twoPlaneHalfSq_gt_one {spikeWeight planeHalf : ℝ} (hweightPos : 0 < spikeWeight)
    (hplaneNormalized : 2 * (1 - spikeWeight) * planeHalf ^ 2 = 1) : 1 < 2 * planeHalf ^ 2 := by
  nlinarith [hplaneNormalized, mul_pos hweightPos (planeHalfSq_pos hplaneNormalized)]

/-- The axial normalisation makes the spike heavy as soon as `lift² < 1`. -/
theorem spikeHeightSq_gt_one {spikeWeight lift spikeHeight : ℝ} (hweightPos : 0 < spikeWeight)
    (hweightLt : spikeWeight < 1)
    (hspikeNormalized : spikeWeight * spikeHeight ^ 2 + (1 - spikeWeight) * lift ^ 2 = 1)
    (hliftHigh : 3 * lift ^ 2 ≤ 2) : 1 < spikeHeight ^ 2 := by
  nlinarith [hspikeNormalized, hweightPos, hweightLt,
    mul_pos (show (0 : ℝ) < 1 - spikeWeight by linarith)
      (show (0 : ℝ) < 1 - lift ^ 2 by linarith)]

/-! ### The arithmetic core, stated on Gram data alone

These theorems are where the dichotomy lives. They speak only about a design's six Gram
scalars at a triple, so they are independent of any coordinate realisation — and they are
what shows the obstruction is not a numerical near-miss. -/

/-- **THE DECISIVE EVALUATION.** At a spike triple whose pair uses two DISTINCT plane
directions, the tie leg is exactly `(6·planeHalf² − 1)(1 − 3·lift²)`. Every occurrence of
`spikeHeight` has cancelled: the verdict on a triple through the heavy atom does not
depend on the heavy atom's leverage at all. This single identity is the reason no leverage
threshold exists. -/
theorem discriminantTie_eq_crossValue_of_spikeGramData {D : WeightedDesign m 3}
    {spikeWeight planeHalf lift spikeHeight : ℝ} {spike pairFirst pairSecond : Fin m}
    (hweightNe : spikeWeight ≠ 0) (hslackNe : (1 : ℝ) - spikeWeight ≠ 0)
    (hplaneNormalized : 2 * (1 - spikeWeight) * planeHalf ^ 2 = 1)
    (hspikeNormalized : spikeWeight * spikeHeight ^ 2 + (1 - spikeWeight) * lift ^ 2 = 1)
    (hexcessSpike : heavyExcess D spike = spikeHeight ^ 2 - 1)
    (hexcessFirst : heavyExcess D pairFirst = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hexcessSecond : heavyExcess D pairSecond = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hpairingFirst : atomPairing D spike pairFirst = spikeHeight * lift)
    (hpairingSecond : atomPairing D spike pairSecond = spikeHeight * lift)
    (hpairingPair : atomPairing D pairFirst pairSecond = -2 * planeHalf ^ 2 + lift ^ 2) :
    discriminantTie D spike pairFirst pairSecond
      = (6 * planeHalf ^ 2 - 1) * (1 - 3 * lift ^ 2) := by
  have hbracket := crossBracketValue spikeWeight (planeHalf ^ 2) (lift ^ 2) (spikeHeight ^ 2)
    hweightNe hslackNe hplaneNormalized hspikeNormalized
  simp only [discriminantTie, hexcessSpike, hexcessFirst, hexcessSecond, hpairingFirst,
    hpairingSecond, hpairingPair]
  linear_combination (6 * planeHalf ^ 2 - 1) * hbracket

/-- **The repeated-direction evaluation.** At a spike triple whose pair is the SAME plane
direction twice, the tie leg scaled by the spike weight is
`−((4 − 6·lift²) + (1−w)(3·lift² − 1))`, again free of `spikeHeight`. -/
theorem discriminantTie_scaled_eq_repeatValue_of_spikeGramData {D : WeightedDesign m 3}
    {spikeWeight planeHalf lift spikeHeight : ℝ} {spike pairFirst pairSecond : Fin m}
    (hweightNe : spikeWeight ≠ 0) (hslackNe : (1 : ℝ) - spikeWeight ≠ 0)
    (hplaneNormalized : 2 * (1 - spikeWeight) * planeHalf ^ 2 = 1)
    (hspikeNormalized : spikeWeight * spikeHeight ^ 2 + (1 - spikeWeight) * lift ^ 2 = 1)
    (hexcessSpike : heavyExcess D spike = spikeHeight ^ 2 - 1)
    (hexcessFirst : heavyExcess D pairFirst = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hexcessSecond : heavyExcess D pairSecond = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hpairingFirst : atomPairing D spike pairFirst = spikeHeight * lift)
    (hpairingSecond : atomPairing D spike pairSecond = spikeHeight * lift)
    (hpairingPair : atomPairing D pairFirst pairSecond = 4 * planeHalf ^ 2 + lift ^ 2) :
    spikeWeight * discriminantTie D spike pairFirst pairSecond
      = -(4 - 6 * lift ^ 2 + (1 - spikeWeight) * (3 * lift ^ 2 - 1)) := by
  have hbracket := repeatBracketValue spikeWeight (planeHalf ^ 2) (lift ^ 2) (spikeHeight ^ 2)
    hweightNe hslackNe hplaneNormalized hspikeNormalized
  simp only [discriminantTie, hexcessSpike, hexcessFirst, hexcessSecond, hpairingFirst,
    hpairingSecond, hpairingPair]
  linear_combination -hbracket

/-- **NO SPIKE TRIPLE DOMINATES.** Whenever a design carries the family's Gram data — a
spike whose pairing with every other atom is `spikeHeight·lift`, and non-spike atoms of
common excess `4·planeHalf² + lift² − 1` whose mutual pairing is either the repeated-
direction value or the cross-direction value — the tie leg at the spike is STRICTLY
NEGATIVE for `1 < 3·lift² ≤ 2`, hence the triple does not dominate. The bound is uniform
in the spike leverage, by the two evaluations above. -/
theorem discriminantTie_neg_of_spikeGramData {D : WeightedDesign m 3}
    {spikeWeight planeHalf lift spikeHeight : ℝ} {spike pairFirst pairSecond : Fin m}
    (hweightPos : 0 < spikeWeight) (hweightLt : spikeWeight < 1)
    (hplaneNormalized : 2 * (1 - spikeWeight) * planeHalf ^ 2 = 1)
    (hspikeNormalized : spikeWeight * spikeHeight ^ 2 + (1 - spikeWeight) * lift ^ 2 = 1)
    (hliftLow : 1 < 3 * lift ^ 2) (hliftHigh : 3 * lift ^ 2 ≤ 2)
    (hexcessSpike : heavyExcess D spike = spikeHeight ^ 2 - 1)
    (hexcessFirst : heavyExcess D pairFirst = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hexcessSecond : heavyExcess D pairSecond = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hpairingFirst : atomPairing D spike pairFirst = spikeHeight * lift)
    (hpairingSecond : atomPairing D spike pairSecond = spikeHeight * lift)
    (hpairingPair : atomPairing D pairFirst pairSecond = 4 * planeHalf ^ 2 + lift ^ 2
      ∨ atomPairing D pairFirst pairSecond = -2 * planeHalf ^ 2 + lift ^ 2) :
    discriminantTie D spike pairFirst pairSecond < 0 := by
  have hweightNe : spikeWeight ≠ 0 := ne_of_gt hweightPos
  have hslackPos : (0 : ℝ) < 1 - spikeWeight := by linarith
  have hslackNe : (1 : ℝ) - spikeWeight ≠ 0 := ne_of_gt hslackPos
  have hplaneBig : 1 < 2 * planeHalf ^ 2 := twoPlaneHalfSq_gt_one hweightPos hplaneNormalized
  rcases hpairingPair with hrepeat | hcross
  · have hscaled := discriminantTie_scaled_eq_repeatValue_of_spikeGramData hweightNe hslackNe
      hplaneNormalized hspikeNormalized hexcessSpike hexcessFirst hexcessSecond hpairingFirst
      hpairingSecond hrepeat
    by_contra hnonneg
    rw [not_lt] at hnonneg
    have hproduct : 0 ≤ spikeWeight * discriminantTie D spike pairFirst pairSecond :=
      mul_nonneg hweightPos.le hnonneg
    nlinarith [hscaled, hproduct, hliftLow, hliftHigh, hslackPos,
      mul_pos hslackPos (show (0 : ℝ) < 3 * lift ^ 2 - 1 by linarith)]
  · rw [discriminantTie_eq_crossValue_of_spikeGramData hweightNe hslackNe hplaneNormalized
      hspikeNormalized hexcessSpike hexcessFirst hexcessSecond hpairingFirst hpairingSecond
      hcross]
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

/-- **THE FAILURE IS A THRESHOLD FAILURE, NOT A DEGENERACY.** On a cross-direction spike
triple the deflated pair minor at the pivot leverage is `(6·planeHalf² − 1)(2·planeHalf² −
lift²)`, which is STRICTLY POSITIVE — so the sharp criterion
`dominates_of_deflatedPairMinorAtLeverage_ge` has a finite threshold here, as the proven
rank-two theorem `gtz_rank_two` forces it to. It is simply never met: the deflated minor
stays strictly below the ambient one at every spike leverage. That is the exact sense in
which the heavy-pivot route fails — not by the deflation collapsing, but by a finite
threshold that the leverage never overtakes, because the ratio grows with it. -/
theorem deflation_pos_and_below_threshold_of_spikeGramData {D : WeightedDesign m 3}
    {spikeWeight planeHalf lift spikeHeight : ℝ} {spike pairFirst pairSecond : Fin m}
    (hweightPos : 0 < spikeWeight) (hweightLt : spikeWeight < 1)
    (hplaneNormalized : 2 * (1 - spikeWeight) * planeHalf ^ 2 = 1)
    (hspikeNormalized : spikeWeight * spikeHeight ^ 2 + (1 - spikeWeight) * lift ^ 2 = 1)
    (hliftLow : 1 < 3 * lift ^ 2) (hliftHigh : 3 * lift ^ 2 ≤ 2)
    (hexcessSpike : heavyExcess D spike = spikeHeight ^ 2 - 1)
    (hexcessFirst : heavyExcess D pairFirst = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hexcessSecond : heavyExcess D pairSecond = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hpairingFirst : atomPairing D spike pairFirst = spikeHeight * lift)
    (hpairingSecond : atomPairing D spike pairSecond = spikeHeight * lift)
    (hpairingPair : atomPairing D pairFirst pairSecond = -2 * planeHalf ^ 2 + lift ^ 2) :
    0 < deflatedPairMinorAtLeverage D spike pairFirst pairSecond
      ∧ deflatedPairMinorAtLeverage D spike pairFirst pairSecond
          < pairMinorOffPivot D pairFirst pairSecond := by
  have hweightNe : spikeWeight ≠ 0 := ne_of_gt hweightPos
  have hslackNe : (1 : ℝ) - spikeWeight ≠ 0 := by
    have hslackPos : (0 : ℝ) < 1 - spikeWeight := by linarith
    exact ne_of_gt hslackPos
  have hplaneBig : 1 < 2 * planeHalf ^ 2 := twoPlaneHalfSq_gt_one hweightPos hplaneNormalized
  have htieValue := discriminantTie_eq_crossValue_of_spikeGramData hweightNe hslackNe
    hplaneNormalized hspikeNormalized hexcessSpike hexcessFirst hexcessSecond hpairingFirst
    hpairingSecond hpairingPair
  have hminorValue : pairMinorOffPivot D pairFirst pairSecond
      = (6 * planeHalf ^ 2 - 1) * (2 * planeHalf ^ 2 + 2 * lift ^ 2 - 1) := by
    simp only [pairMinorOffPivot, hexcessFirst, hexcessSecond, hpairingPair]
    ring
  have hidentity := discriminantTie_eq_deflatedPairMinorAtLeverage_sub_pairMinorOffPivot
    D spike pairFirst pairSecond
  rw [htieValue, hminorValue] at hidentity
  have hdeflatedValue : deflatedPairMinorAtLeverage D spike pairFirst pairSecond
      = (6 * planeHalf ^ 2 - 1) * (2 * planeHalf ^ 2 - lift ^ 2) := by linarith
  refine ⟨?_, ?_⟩
  · rw [hdeflatedValue]
    exact mul_pos (by linarith) (by linarith)
  · rw [hdeflatedValue, hminorValue]
    nlinarith [hplaneBig, hliftLow]

/-- **THE OTHER SIDE OF THE DICHOTOMY.** A triple of three pairwise cross-direction atoms
has tie leg `(6·planeHalf² − 1)²(3·lift² − 1)` — a pure `ring` identity needing no
normalisation. The factor `3·lift² − 1` is the SAME one that made every spike triple fail,
with the opposite sign: the dichotomy is exact and tight at `3·lift² = 1`. -/
theorem discriminantTie_eq_crossTripleValue {D : WeightedDesign m 3} {planeHalf lift : ℝ}
    {pivot pairFirst pairSecond : Fin m}
    (hexcessPivot : heavyExcess D pivot = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hexcessFirst : heavyExcess D pairFirst = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hexcessSecond : heavyExcess D pairSecond = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hpairingPivotFirst : atomPairing D pivot pairFirst = -2 * planeHalf ^ 2 + lift ^ 2)
    (hpairingPivotSecond : atomPairing D pivot pairSecond = -2 * planeHalf ^ 2 + lift ^ 2)
    (hpairingPair : atomPairing D pairFirst pairSecond = -2 * planeHalf ^ 2 + lift ^ 2) :
    discriminantTie D pivot pairFirst pairSecond
      = (6 * planeHalf ^ 2 - 1) ^ 2 * (3 * lift ^ 2 - 1) := by
  simp only [discriminantTie, hexcessPivot, hexcessFirst, hexcessSecond, hpairingPivotFirst,
    hpairingPivotSecond, hpairingPair]
  ring

/-- The matching trace leg of a cross-direction triple,
`2(6·planeHalf² − 1)(2·planeHalf² + 2·lift² − 1)`, also a pure `ring` identity. -/
theorem discriminantTrace_eq_crossTripleValue {D : WeightedDesign m 3} {planeHalf lift : ℝ}
    {pivot pairFirst pairSecond : Fin m}
    (hexcessPivot : heavyExcess D pivot = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hexcessFirst : heavyExcess D pairFirst = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hexcessSecond : heavyExcess D pairSecond = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hpairingPivotFirst : atomPairing D pivot pairFirst = -2 * planeHalf ^ 2 + lift ^ 2)
    (hpairingPivotSecond : atomPairing D pivot pairSecond = -2 * planeHalf ^ 2 + lift ^ 2) :
    discriminantTrace D pivot pairFirst pairSecond
      = 2 * (6 * planeHalf ^ 2 - 1) * (2 * planeHalf ^ 2 + 2 * lift ^ 2 - 1) := by
  simp only [discriminantTrace, hexcessPivot, hexcessFirst, hexcessSecond, hpairingPivotFirst,
    hpairingPivotSecond]
  ring

/-- **THE SPIKE-FREE TRIPLE DOES DOMINATE**, so GTZ is not contradicted on the family: the
conjecture survives through a triple that avoids the heavy atom. -/
theorem dominates_of_crossDirectionGramData {D : WeightedDesign m 3} {planeHalf lift : ℝ}
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hplaneBig : 1 < 2 * planeHalf ^ 2) (hliftLow : 1 < 3 * lift ^ 2)
    (hexcessPivot : heavyExcess D pivot = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hexcessFirst : heavyExcess D pairFirst = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hexcessSecond : heavyExcess D pairSecond = 4 * planeHalf ^ 2 + lift ^ 2 - 1)
    (hpairingPivotFirst : atomPairing D pivot pairFirst = -2 * planeHalf ^ 2 + lift ^ 2)
    (hpairingPivotSecond : atomPairing D pivot pairSecond = -2 * planeHalf ^ 2 + lift ^ 2)
    (hpairingPair : atomPairing D pairFirst pairSecond = -2 * planeHalf ^ 2 + lift ^ 2) :
    Dominates D {pivot, pairFirst, pairSecond} := by
  have hliftNonneg : (0 : ℝ) ≤ lift ^ 2 := sq_nonneg lift
  have hpivotHeavy : 1 < leverageOf (D.atom pivot) := by
    have hexcessUnfolded := hexcessPivot
    rw [heavyExcess] at hexcessUnfolded
    linarith
  refine (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond hpairDistinct
    hpivotHeavy).mpr ⟨?_, ?_⟩
  · rw [discriminantTrace_eq_crossTripleValue hexcessPivot hexcessFirst hexcessSecond
      hpairingPivotFirst hpairingPivotSecond]
    exact le_of_lt (mul_pos (by linarith) (by linarith))
  · rw [discriminantTie_eq_crossTripleValue hexcessPivot hexcessFirst hexcessSecond
      hpairingPivotFirst hpairingPivotSecond hpairingPair]
    exact le_of_lt (mul_pos (pow_pos (by linarith) 2) (by linarith))

/-! ### The coordinate realisation: an axial spike over three doubled Mercedes directions -/

/-- The seven atoms: an axial spike `(0, 0, spikeHeight)`, and the three lifted Mercedes
plane directions `(2·planeHalf, 0, lift)`, `(−planeHalf, ±planeHeight, lift)`, each taken
TWICE. Doubling is what makes the size `7` while keeping only three distinct plane
directions, so that every pair of non-spike atoms is either a repeat or a cross. -/
noncomputable def liftedMercedesAtom (planeHalf planeHeight lift spikeHeight : ℝ) :
    Fin 7 → Fin 3 → ℝ :=
  ![![0, 0, spikeHeight],
    ![2 * planeHalf, 0, lift],
    ![2 * planeHalf, 0, lift],
    ![-planeHalf, planeHeight, lift],
    ![-planeHalf, planeHeight, lift],
    ![-planeHalf, -planeHeight, lift],
    ![-planeHalf, -planeHeight, lift]]

/-- The weights: `spikeWeight` on the spike, the remaining mass split evenly over the six
plane atoms. -/
noncomputable def liftedMercedesWeight (spikeWeight : ℝ) : Fin 7 → ℝ :=
  ![spikeWeight, (1 - spikeWeight) / 6, (1 - spikeWeight) / 6, (1 - spikeWeight) / 6,
    (1 - spikeWeight) / 6, (1 - spikeWeight) / 6, (1 - spikeWeight) / 6]

section LiftedMercedesFamily

variable {spikeWeight planeHalf planeHeight lift spikeHeight : ℝ}

theorem liftedMercedesAtom_spike : liftedMercedesAtom planeHalf planeHeight lift spikeHeight 0
    = ![0, 0, spikeHeight] := rfl

theorem liftedMercedesAtom_firstDirection :
    liftedMercedesAtom planeHalf planeHeight lift spikeHeight 1
      = ![2 * planeHalf, 0, lift] := rfl

theorem liftedMercedesAtom_secondDirection :
    liftedMercedesAtom planeHalf planeHeight lift spikeHeight 3
      = ![-planeHalf, planeHeight, lift] := rfl

theorem liftedMercedesAtom_thirdDirection :
    liftedMercedesAtom planeHalf planeHeight lift spikeHeight 5
      = ![-planeHalf, -planeHeight, lift] := rfl

/-- Every non-spike atom is one of the three lifted plane directions. This is the whole
index bookkeeping of the family, isolated once. -/
theorem liftedMercedesAtom_direction (atomIndex : Fin 7) (hne : atomIndex ≠ 0) :
    liftedMercedesAtom planeHalf planeHeight lift spikeHeight atomIndex
        = ![2 * planeHalf, 0, lift]
      ∨ liftedMercedesAtom planeHalf planeHeight lift spikeHeight atomIndex
        = ![-planeHalf, planeHeight, lift]
      ∨ liftedMercedesAtom planeHalf planeHeight lift spikeHeight atomIndex
        = ![-planeHalf, -planeHeight, lift] := by
  have hcases : atomIndex = 1 ∨ atomIndex = 2 ∨ atomIndex = 3 ∨ atomIndex = 4
      ∨ atomIndex = 5 ∨ atomIndex = 6 := by
    fin_cases atomIndex <;> simp_all
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inr rfl)

/-- **The family as a genuine weighted `(7,3)` design.** Parseval is exact: the plane block
is `I₂` by the Mercedes cancellation `2·planeHalf² · (4 + 1 + 1) = 12·planeHalf²` against
`planeHeight² = 3·planeHalf²`, the cross block vanishes identically because
`4·planeHalf − 2·planeHalf − 2·planeHalf = 0`, and the axial block is the second
normalisation. No square roots and no approximation anywhere. -/
noncomputable def liftedMercedesDesign (hweightPos : 0 < spikeWeight)
    (hweightLt : spikeWeight < 1)
    (hplaneNormalized : 2 * (1 - spikeWeight) * planeHalf ^ 2 = 1)
    (hheightSquared : planeHeight ^ 2 = 3 * planeHalf ^ 2)
    (hspikeNormalized : spikeWeight * spikeHeight ^ 2 + (1 - spikeWeight) * lift ^ 2 = 1) :
    WeightedDesign 7 3 where
  atom := liftedMercedesAtom planeHalf planeHeight lift spikeHeight
  weight := liftedMercedesWeight spikeWeight
  weight_pos := by
    intro atomIndex
    fin_cases atomIndex <;> simp [liftedMercedesWeight] <;> linarith
  weight_sum_one := by
    simp [liftedMercedesWeight, Fin.sum_univ_seven]
    ring
  isParseval := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply, Fin.sum_univ_seven,
        liftedMercedesWeight, liftedMercedesAtom] <;>
      (first
        | ring1
        | linear_combination hplaneNormalized
        | linear_combination hspikeNormalized
        | linear_combination (2 / 3) * (1 - spikeWeight) * hheightSquared + hplaneNormalized)

variable (hweightPos : 0 < spikeWeight) (hweightLt : spikeWeight < 1)
  (hplaneNormalized : 2 * (1 - spikeWeight) * planeHalf ^ 2 = 1)
  (hheightSquared : planeHeight ^ 2 = 3 * planeHalf ^ 2)
  (hspikeNormalized : spikeWeight * spikeHeight ^ 2 + (1 - spikeWeight) * lift ^ 2 = 1)

theorem liftedMercedesDesign_atom :
    (liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
      hspikeNormalized).atom = liftedMercedesAtom planeHalf planeHeight lift spikeHeight := rfl

theorem liftedMercedesDesign_weight :
    (liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
      hspikeNormalized).weight = liftedMercedesWeight spikeWeight := rfl

/-! #### The family's Gram data -/

theorem liftedMercedesDesign_spike_leverage :
    leverageOf ((liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
      hspikeNormalized).atom 0) = spikeHeight ^ 2 := by
  rw [liftedMercedesDesign_atom]
  simp [leverageOf, liftedMercedesAtom, Fin.sum_univ_three]

theorem liftedMercedesDesign_offSpike_leverage (atomIndex : Fin 7) (hne : atomIndex ≠ 0) :
    leverageOf ((liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
      hspikeNormalized).atom atomIndex) = 4 * planeHalf ^ 2 + lift ^ 2 := by
  rw [liftedMercedesDesign_atom]
  rcases liftedMercedesAtom_direction atomIndex hne with hdir | hdir | hdir <;>
    rw [hdir] <;>
    simp only [leverageOf, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    (first
      | ring1
      | linear_combination hheightSquared)

theorem liftedMercedesDesign_spike_heavyExcess :
    heavyExcess (liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
      hspikeNormalized) 0 = spikeHeight ^ 2 - 1 := by
  rw [heavyExcess, liftedMercedesDesign_spike_leverage]

theorem liftedMercedesDesign_offSpike_heavyExcess (atomIndex : Fin 7) (hne : atomIndex ≠ 0) :
    heavyExcess (liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
      hspikeNormalized) atomIndex = 4 * planeHalf ^ 2 + lift ^ 2 - 1 := by
  rw [heavyExcess, liftedMercedesDesign_offSpike_leverage _ _ _ _ _ atomIndex hne]

theorem liftedMercedesDesign_spike_pairing (atomIndex : Fin 7) (hne : atomIndex ≠ 0) :
    atomPairing (liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
      hspikeNormalized) 0 atomIndex = spikeHeight * lift := by
  rw [atomPairing, liftedMercedesDesign_atom]
  rcases liftedMercedesAtom_direction atomIndex hne with hdir | hdir | hdir <;>
    rw [hdir, liftedMercedesAtom_spike] <;>
    simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    ring

/-- Two non-spike atoms pair either at the repeated-direction value `4·planeHalf² + lift²`
or at the cross-direction value `−2·planeHalf² + lift²`. There is no third case: the six
plane atoms carry only three distinct directions. -/
theorem liftedMercedesDesign_offSpike_pairing (firstIndex secondIndex : Fin 7)
    (hfirstNe : firstIndex ≠ 0) (hsecondNe : secondIndex ≠ 0) :
    atomPairing (liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
        hspikeNormalized) firstIndex secondIndex = 4 * planeHalf ^ 2 + lift ^ 2
      ∨ atomPairing (liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
        hspikeNormalized) firstIndex secondIndex = -2 * planeHalf ^ 2 + lift ^ 2 := by
  rw [atomPairing, liftedMercedesDesign_atom]
  rcases liftedMercedesAtom_direction firstIndex hfirstNe with hfirst | hfirst | hfirst <;>
    rcases liftedMercedesAtom_direction secondIndex hsecondNe with hsecond | hsecond | hsecond <;>
    rw [hfirst, hsecond] <;>
    simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    (first
      | (left; ring1)
      | (left; linear_combination hheightSquared)
      | (right; ring1)
      | (right; linear_combination -hheightSquared))

theorem liftedMercedesDesign_pairing_firstSecond :
    atomPairing (liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
      hspikeNormalized) 1 3 = -2 * planeHalf ^ 2 + lift ^ 2 := by
  rw [atomPairing, liftedMercedesDesign_atom, liftedMercedesAtom_firstDirection,
    liftedMercedesAtom_secondDirection]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem liftedMercedesDesign_pairing_firstThird :
    atomPairing (liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
      hspikeNormalized) 1 5 = -2 * planeHalf ^ 2 + lift ^ 2 := by
  rw [atomPairing, liftedMercedesDesign_atom, liftedMercedesAtom_firstDirection,
    liftedMercedesAtom_thirdDirection]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem liftedMercedesDesign_pairing_secondThird :
    atomPairing (liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
      hspikeNormalized) 3 5 = -2 * planeHalf ^ 2 + lift ^ 2 := by
  rw [atomPairing, liftedMercedesDesign_atom, liftedMercedesAtom_secondDirection,
    liftedMercedesAtom_thirdDirection]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination -hheightSquared

/-! #### All-heaviness, the diverging leverage, and the interior leverage score -/

theorem liftedMercedesDesign_allHeavy (hliftHigh : 3 * lift ^ 2 ≤ 2) :
    AllHeavy (liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
      hspikeNormalized) := by
  intro atomIndex
  rcases eq_or_ne atomIndex 0 with rfl | hne
  · rw [liftedMercedesDesign_spike_leverage]
    exact spikeHeightSq_gt_one hweightPos hweightLt hspikeNormalized hliftHigh
  · rw [liftedMercedesDesign_offSpike_leverage _ _ _ _ _ atomIndex hne]
    have hplaneBig : 1 < 2 * planeHalf ^ 2 := twoPlaneHalfSq_gt_one hweightPos hplaneNormalized
    have hliftNonneg : (0 : ℝ) ≤ lift ^ 2 := sq_nonneg lift
    linarith

/-- **The leverage score stays interior while the leverage diverges.** The spike's weighted
leverage is `1 − (1−w)·lift²`, which for `lift² = 1/2` sits at `(1+w)/2 → 1/2`: the
blow-up `leverage = (1 − (1−w)·lift²)/w → ∞` is entirely a weight reaching the simplex
boundary, not a geometric degeneration. This is why the leverage is the WRONG
compactification variable and the score is the right one. -/
theorem liftedMercedesDesign_spike_leverageScore :
    (liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
        hspikeNormalized).weight 0
      * leverageOf ((liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
        hspikeNormalized).atom 0)
      = 1 - (1 - spikeWeight) * lift ^ 2 := by
  rw [liftedMercedesDesign_spike_leverage, liftedMercedesDesign_weight]
  simp only [liftedMercedesWeight, Matrix.cons_val_zero]
  linarith [hspikeNormalized]

/-! #### The dichotomy on the family -/

/-- **No triple containing the spike dominates — at any spike leverage.** -/
theorem liftedMercedesDesign_not_dominates_spike_triple (hliftLow : 1 < 3 * lift ^ 2)
    (hliftHigh : 3 * lift ^ 2 ≤ 2) (pairFirst pairSecond : Fin 7) (hfirstNe : pairFirst ≠ 0)
    (hsecondNe : pairSecond ≠ 0) (hpairDistinct : pairFirst ≠ pairSecond) :
    ¬ Dominates (liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
      hspikeNormalized) {0, pairFirst, pairSecond} := by
  intro hdominates
  have htieNeg : discriminantTie (liftedMercedesDesign hweightPos hweightLt hplaneNormalized
      hheightSquared hspikeNormalized) 0 pairFirst pairSecond < 0 :=
    discriminantTie_neg_of_spikeGramData hweightPos hweightLt hplaneNormalized hspikeNormalized
      hliftLow hliftHigh
      (liftedMercedesDesign_spike_heavyExcess hweightPos hweightLt hplaneNormalized
        hheightSquared hspikeNormalized)
      (liftedMercedesDesign_offSpike_heavyExcess hweightPos hweightLt hplaneNormalized
        hheightSquared hspikeNormalized pairFirst hfirstNe)
      (liftedMercedesDesign_offSpike_heavyExcess hweightPos hweightLt hplaneNormalized
        hheightSquared hspikeNormalized pairSecond hsecondNe)
      (liftedMercedesDesign_spike_pairing hweightPos hweightLt hplaneNormalized hheightSquared
        hspikeNormalized pairFirst hfirstNe)
      (liftedMercedesDesign_spike_pairing hweightPos hweightLt hplaneNormalized hheightSquared
        hspikeNormalized pairSecond hsecondNe)
      (liftedMercedesDesign_offSpike_pairing hweightPos hweightLt hplaneNormalized
        hheightSquared hspikeNormalized pairFirst pairSecond hfirstNe hsecondNe)
  have hspikeHeavy : 1 < leverageOf ((liftedMercedesDesign hweightPos hweightLt
      hplaneNormalized hheightSquared hspikeNormalized).atom 0) :=
    liftedMercedesDesign_allHeavy hweightPos hweightLt hplaneNormalized hheightSquared
      hspikeNormalized hliftHigh 0
  have htieNonneg := ((dominates_triple_iff_discriminantSystem _ (Ne.symm hfirstNe)
    (Ne.symm hsecondNe) hpairDistinct hspikeHeavy).mp hdominates).2
  linarith

/-- **The spike-free triple of three distinct directions dominates.** GTZ is therefore NOT
contradicted on the family: the conjecture survives through a triple avoiding the heavy
atom, which is exactly the shape a compactification must exploit. -/
theorem liftedMercedesDesign_dominates_directionTriple (hliftLow : 1 < 3 * lift ^ 2) :
    Dominates (liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
      hspikeNormalized) {1, 3, 5} :=
  dominates_of_crossDirectionGramData (by decide) (by decide) (by decide)
    (twoPlaneHalfSq_gt_one hweightPos hplaneNormalized) hliftLow
    (liftedMercedesDesign_offSpike_heavyExcess hweightPos hweightLt hplaneNormalized
      hheightSquared hspikeNormalized 1 (by decide))
    (liftedMercedesDesign_offSpike_heavyExcess hweightPos hweightLt hplaneNormalized
      hheightSquared hspikeNormalized 3 (by decide))
    (liftedMercedesDesign_offSpike_heavyExcess hweightPos hweightLt hplaneNormalized
      hheightSquared hspikeNormalized 5 (by decide))
    (liftedMercedesDesign_pairing_firstSecond hweightPos hweightLt hplaneNormalized
      hheightSquared hspikeNormalized)
    (liftedMercedesDesign_pairing_firstThird hweightPos hweightLt hplaneNormalized
      hheightSquared hspikeNormalized)
    (liftedMercedesDesign_pairing_secondThird hweightPos hweightLt hplaneNormalized
      hheightSquared hspikeNormalized)

end LiftedMercedesFamily

/-! ### The honest negative: the heavy-pivot brick is false at every cap -/

/-- **THE HONEST NEGATIVE.** For every `cap` there is an all-heavy weighted `(7,3)` design
with an atom of leverage at least `cap` that lies in NO dominating triple, while the design
itself does own a dominating triple. So the leverage-threshold brick the compactification
programme asked for does not exist — not because it is unproven, but because it is false —
and the leverage of an atom carries no information about whether that atom is usable. The
witnesses are the `lift² = 1/2` slice of `liftedMercedesDesign` at spike weight
`1/(2·max cap 1)`; the minimisers do not degenerate geometrically, they only push a weight
to the simplex boundary (`liftedMercedesDesign_spike_leverageScore`). -/
theorem exists_allHeavy_seven_design_with_unusable_heavy_atom (cap : ℝ) :
    ∃ design : WeightedDesign 7 3, ∃ heavyIndex : Fin 7,
      AllHeavy design ∧ cap ≤ leverageOf (design.atom heavyIndex)
        ∧ (∀ pairFirst pairSecond : Fin 7, pairFirst ≠ heavyIndex → pairSecond ≠ heavyIndex →
            pairFirst ≠ pairSecond → ¬ Dominates design {heavyIndex, pairFirst, pairSecond})
        ∧ ∃ dominatingSubset : Finset (Fin 7),
            dominatingSubset.card = 3 ∧ Dominates design dominatingSubset := by
  have hcapBoundOne : (1 : ℝ) ≤ max cap 1 := le_max_right _ _
  have hcapLeBound : cap ≤ max cap 1 := le_max_left _ _
  have hdenomPos : (0 : ℝ) < 2 * max cap 1 := by linarith
  set spikeWeight : ℝ := 1 / (2 * max cap 1) with hspikeWeightDef
  have hweightPos : 0 < spikeWeight := by rw [hspikeWeightDef]; positivity
  have hweightLt : spikeWeight < 1 := by
    rw [hspikeWeightDef, div_lt_one hdenomPos]; linarith
  have hslackPos : (0 : ℝ) < 1 - spikeWeight := by linarith
  have hslackNe : (1 : ℝ) - spikeWeight ≠ 0 := ne_of_gt hslackPos
  have hweightNe : spikeWeight ≠ 0 := ne_of_gt hweightPos
  set lift : ℝ := Real.sqrt (1 / 2) with hliftDef
  have hliftSq : lift ^ 2 = 1 / 2 := by rw [hliftDef, Real.sq_sqrt (by norm_num)]
  have hliftLow : 1 < 3 * lift ^ 2 := by rw [hliftSq]; norm_num
  have hliftHigh : 3 * lift ^ 2 ≤ 2 := by rw [hliftSq]; norm_num
  have hplaneArgNonneg : (0 : ℝ) ≤ 1 / (2 * (1 - spikeWeight)) := by
    apply div_nonneg (by norm_num); linarith
  set planeHalf : ℝ := Real.sqrt (1 / (2 * (1 - spikeWeight))) with hplaneHalfDef
  have hplaneHalfSq : planeHalf ^ 2 = 1 / (2 * (1 - spikeWeight)) := by
    rw [hplaneHalfDef, Real.sq_sqrt hplaneArgNonneg]
  have hplaneNormalized : 2 * (1 - spikeWeight) * planeHalf ^ 2 = 1 := by
    rw [hplaneHalfSq]; field_simp
  have hheightArgNonneg : (0 : ℝ) ≤ 3 / (2 * (1 - spikeWeight)) := by
    apply div_nonneg (by norm_num); linarith
  set planeHeight : ℝ := Real.sqrt (3 / (2 * (1 - spikeWeight))) with hplaneHeightDef
  have hheightSquared : planeHeight ^ 2 = 3 * planeHalf ^ 2 := by
    rw [hplaneHeightDef, Real.sq_sqrt hheightArgNonneg, hplaneHalfSq]; ring
  have hspikeArgNonneg : (0 : ℝ) ≤ (1 - (1 - spikeWeight) * (1 / 2)) / spikeWeight := by
    apply div_nonneg _ hweightPos.le; linarith
  set spikeHeight : ℝ := Real.sqrt ((1 - (1 - spikeWeight) * (1 / 2)) / spikeWeight) with
    hspikeHeightDef
  have hspikeHeightSq : spikeHeight ^ 2 = (1 - (1 - spikeWeight) * (1 / 2)) / spikeWeight := by
    rw [hspikeHeightDef, Real.sq_sqrt hspikeArgNonneg]
  have hspikeNormalized : spikeWeight * spikeHeight ^ 2 + (1 - spikeWeight) * lift ^ 2 = 1 := by
    rw [hspikeHeightSq, hliftSq]; field_simp; ring
  refine ⟨liftedMercedesDesign hweightPos hweightLt hplaneNormalized hheightSquared
    hspikeNormalized, 0,
    liftedMercedesDesign_allHeavy hweightPos hweightLt hplaneNormalized hheightSquared
      hspikeNormalized hliftHigh, ?_, ?_, ⟨{1, 3, 5}, by decide,
    liftedMercedesDesign_dominates_directionTriple hweightPos hweightLt hplaneNormalized
      hheightSquared hspikeNormalized hliftLow⟩⟩
  · rw [liftedMercedesDesign_spike_leverage, hspikeHeightSq, hspikeWeightDef]
    have hvalue : (1 - (1 - 1 / (2 * max cap 1)) * (1 / 2)) / (1 / (2 * max cap 1))
        = max cap 1 + 1 / 2 := by
      field_simp
      ring
    rw [hvalue]
    linarith
  · intro pairFirst pairSecond hfirstNe hsecondNe hpairDistinct
    exact liftedMercedesDesign_not_dominates_spike_triple hweightPos hweightLt hplaneNormalized
      hheightSquared hspikeNormalized hliftLow hliftHigh pairFirst pairSecond hfirstNe hsecondNe
      hpairDistinct

/-- **THE HEAVY-PIVOT BRICK IS FALSE AT EVERY CAP.** No leverage threshold can force a
dominating triple through the heavy atom, so the compactification of
`rank_three_of_heavyPivotCovering_of_capped` is unreachable by this route, and the
pivot-free `HeavyAtomCovering` of `rank_three_of_heavyAtomCovering_of_capped` is the only
surviving shape. Concretely, the next brick to aim at is the score dichotomy: EITHER the
heavy atom is usable, OR the remaining six atoms carry a dominating triple. -/
theorem not_heavyPivotCovering (cap : ℝ) : ¬ HeavyPivotCovering cap 7 := by
  intro hpivotCovering
  obtain ⟨design, heavyIndex, hheavy, hcapLe, hunusable, -⟩ :=
    exists_allHeavy_seven_design_with_unusable_heavy_atom cap
  obtain ⟨pairFirst, pairSecond, hheavyFirst, hheavySecond, hpairDistinct, hdominates⟩ :=
    hpivotCovering design hheavy heavyIndex hcapLe
  exact hunusable pairFirst pairSecond (Ne.symm hheavyFirst) (Ne.symm hheavySecond) hpairDistinct
    hdominates

end Gtz
