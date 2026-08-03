/-
# The kernel exceptional witness: an exact rational all-heavy generic
# exceptional design

`Gtz.GenericExceptionalSignClash` quantifies over generic all-heavy designs
with exceptional phase-free image.  Until now the inhabitation of that
quantifier domain was EXTERNAL MEASUREMENT (the Phase-2 module header records
"no design-level exceptional witness is kernel-checked").  This module closes
that caveat: `Gtz.exceptionalWitnessDesign` is an exact rational
`WeightedDesign 6 3` whose Parseval identity, strict heaviness, full generic
bundle, and BOTH clauses of `Gtz.PhaseFreeData.IsExceptional` are certified
by finite rational arithmetic in the kernel —
`Gtz.exists_allHeavy_generic_exceptional_design` packages the inhabitation.

The design is the Phase-3 construction of the recon lane (a Cayley rational
orthonormal frame bent through a stereographic point of the five-sphere,
weighted by exact Parseval shares): atoms over denominators up to `38`
digits, weights over the two rational squares `21819 ^ 2` and `7273 ^ 2`.
What the kernel certifies here:

* the Parseval resolution of the identity, positivity, unit weight sum;
* strict heaviness at every atom (`Gtz.AllHeavy`);
* the five-conjunct generic bundle (`Gtz.IsGenericDesign`): nonzero
  pairings, no parallel pair, strict edges, strict bands, nonzero ties;
* exceptionality of the phase-free image: clause one holds in the STRONG
  uniform form — NO ordered triple of the image is sign-blind good, `102`
  by a strictly negative gap and `18` by the strict box bound, so the
  trace-class restriction is never consulted — and clause two holds with an
  explicit star witness at each of the `16` light ordered edges (`4` leave
  the nonnegative-trace class, `12` break the plus band at both torsion
  readings, closed by the two-readings helper below).

What remains EXTERNAL about this datum (measured by three independent exact
codes, not kernel-checked): its forced-minus count is `8`, its forced sign
system is infeasible, and it carries `4` dominating triples — the design is
a witness for the DOMAIN of the open proposition, not a counterexample to
anything.

Realness note: the two-readings helper is the torsion consumption — the
band-break clause pins `|triangle|` between its two real readings, exactly
the `t = ±r` dichotomy that a free complex phase would void.

Provenance: gtz-p3 land-attack; construction and external certification by
the gtz-p3 recon lane, independently re-certified from raw data by the
verify-adversarial lane.
-/
import Mathlib
import Gtz.Reduction.GenericityReduction
import Gtz.Quantitative.VertexExclusion

namespace Gtz

/-! ## The design -/

/-- The atom table of the exceptional witness: six exact rational vectors. -/
noncomputable def exceptionalWitnessAtom : Fin 6 → Fin 3 → ℝ :=
  ![![-156956985087559209/5866980046350449111, 4626562852326338560/5866980046350449111, 5730173229130789376/5866980046350449111],
    ![2959557496597128/10181077804425841, 3360986677352757719/5212711835866030592, -1546535104040759/1071692400465878],
    ![6104351832158874/5894308202562329, 27021646050434581/17682924607686987, -108362743318545961/4526828699567868672],
    ![5697269539007137/4822615802096451, -28988188221247913/14467847406289353, 3345836053303457/14467847406289353],
    ![9610326148712926/4822615802096451, 1010194399073069/14467847406289353, 19819139726779225/14467847406289353],
    ![-640102814409975/535846200232939, 3911539946345773/20362155608851682, 17809142870534477/20362155608851682]]

/-- **The exceptional witness design**: exact rational Parseval weights over
the two squares `476068761 = 21819 ^ 2` and `52896529 = 7273 ^ 2`. -/
noncomputable def exceptionalWitnessDesign : WeightedDesign 6 3 where
  atom := exceptionalWitnessAtom
  weight := ![119880601/476068761, 94633984/476068761, 7929856/52896529, 5308416/52896529, 5308416/52896529, 94633984/476068761]
  weight_pos := by
    intro atomIndex
    fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext coordFirst coordSecond
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_six, smul_eq_mul,
      exceptionalWitnessAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    fin_cases coordFirst <;> fin_cases coordSecond <;> norm_num [Matrix.one_apply]

/-! ## Heaviness and the generic bundle -/

/-- The witness is all-heavy: every leverage strictly exceeds one. -/
theorem exceptionalWitnessDesign_allHeavy : AllHeavy exceptionalWitnessDesign := by
  intro atomIndex
  fin_cases atomIndex <;>
    simp [exceptionalWitnessDesign, exceptionalWitnessAtom, leverageOf,
      Fin.sum_univ_three]
  all_goals norm_num

-- The generic-bundle certificate is 30 + 30 + 30 + 216 exact rational cases
-- over the witness's large denominators; the heartbeat bump covers the blast.
set_option maxHeartbeats 8000000 in
/-- **The witness passes the full generic bundle** — every conjunct certified
by exact rational arithmetic; the tie conjunct derived from the band conjunct
through the split identity, exactly as for `Gtz.genericWitnessDesign`. -/
theorem exceptionalWitnessDesign_isGenericDesign :
    IsGenericDesign exceptionalWitnessDesign := by
  have hband : ∀ first second third : Fin 6,
      first ≠ second → first ≠ third → second ≠ third →
      excessGap exceptionalWitnessDesign first second third ^ 2
        ≠ 4 * (atomPairing exceptionalWitnessDesign first second
            * atomPairing exceptionalWitnessDesign first third
            * atomPairing exceptionalWitnessDesign second third) ^ 2 := by
    intro first second third hfs hft hst
    fin_cases first <;> fin_cases second <;> fin_cases third
    all_goals try exact absurd rfl hfs
    all_goals try exact absurd rfl hft
    all_goals try exact absurd rfl hst
    all_goals
      simp [excessGap, heavyExcess, atomPairing, leverageOf,
        exceptionalWitnessDesign, exceptionalWitnessAtom, dotProduct,
        Fin.sum_univ_three]
    all_goals norm_num
  have hpairing : ∀ first second : Fin 6, first ≠ second →
      atomPairing exceptionalWitnessDesign first second ≠ 0 := by
    intro first second hne
    fin_cases first <;> fin_cases second
    all_goals try exact absurd rfl hne
    all_goals
      simp [atomPairing, exceptionalWitnessDesign, exceptionalWitnessAtom,
        dotProduct, Fin.sum_univ_three]
    all_goals norm_num
  have hparallel : ∀ first second : Fin 6, first ≠ second →
      atomPairing exceptionalWitnessDesign first second ^ 2
        ≠ leverageOf (exceptionalWitnessDesign.atom first)
          * leverageOf (exceptionalWitnessDesign.atom second) := by
    intro first second hne
    fin_cases first <;> fin_cases second
    all_goals try exact absurd rfl hne
    all_goals
      simp [atomPairing, leverageOf, exceptionalWitnessDesign,
        exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
    all_goals norm_num
  have hedge : ∀ first second : Fin 6, first ≠ second →
      exceptionalWitnessDesign.weight first
          * leverageOf (exceptionalWitnessDesign.atom first)
        + exceptionalWitnessDesign.weight second
          * leverageOf (exceptionalWitnessDesign.atom second) ≠ 1 := by
    intro first second hne
    fin_cases first <;> fin_cases second
    all_goals try exact absurd rfl hne
    all_goals
      simp [leverageOf, exceptionalWitnessDesign, exceptionalWitnessAtom,
        Fin.sum_univ_three]
    all_goals norm_num
  exact ⟨hpairing, hparallel, hedge, hband, fun first second third hfs hft hst =>
    discriminantTie_ne_zero_of_excessGap_sq_ne exceptionalWitnessDesign
      (hband first second third hfs hft hst)⟩

/-! ## Exceptionality of the phase-free image -/

/-- The band-break clause from its two torsion readings: if the gap is
negative enough at BOTH signed readings of the triangle, it is negative
against the absolute reading.  This is where realness enters the clause-two
certificate: `|triangle|` is one of the two real readings. -/
private theorem bandBreak_of_two_readings {gapValue triangleValue : ℝ}
    (hplus : gapValue + 2 * triangleValue < 0)
    (hminus : gapValue - 2 * triangleValue < 0) :
    gapValue + 2 * |triangleValue| < 0 := by
  rcases abs_cases triangleValue with ⟨habs, _⟩ | ⟨habs, _⟩ <;> rw [habs] <;>
    linarith

-- Clause one is 216 exact rational cases (the strong uniform form: no triple
-- is sign-blind good, the trace hypothesis is never consulted); clause two is
-- 36 cases with explicit star witnesses at the 16 light ordered edges.
set_option maxHeartbeats 8000000 in
/-- **The phase-free image of the witness is exceptional** — the first
kernel-checked inhabitant of the residue predicate at a design image.  Clause
one holds in the strong uniform form: NO ordered triple is sign-blind good
(`102` gaps strictly negative, `18` strict box bounds), so its trace-class
guard is never consulted.  Clause two carries an explicit witness in every
light star: `4` leave the nonnegative-trace class, `12` break the plus band
at both torsion readings. -/
theorem exceptionalWitnessDesign_isExceptional :
    (phaseFreeOfDesign exceptionalWitnessDesign).IsExceptional := by
  refine ⟨?_, ?_⟩
  · -- clause one: no ordered triple is sign-blind good.
    intro first second third hfs hft hst _htrace
    fin_cases first <;> fin_cases second <;> fin_cases third
    all_goals try exact absurd rfl hfs
    all_goals try exact absurd rfl hft
    all_goals try exact absurd rfl hst
    all_goals
      simp [PhaseFreeData.IsSignBlindGoodTriple, PhaseFreeData.excessGap,
        phaseFreeOfDesign, heavyExcess, atomPairing, leverageOf,
        exceptionalWitnessDesign, exceptionalWitnessAtom, dotProduct,
        Fin.sum_univ_three]
    all_goals norm_num
  · -- clause two: an explicit witness in every light star.
    intro first second hne
    fin_cases first <;> fin_cases second
    all_goals try exact absurd rfl hne
    · -- light edge (0,1): star atom 2 breaks the plus band
      intro _hshare
      refine ⟨2, by decide, Or.inr (bandBreak_of_two_readings ?_ ?_)⟩ <;>
        · simp [PhaseFreeData.excessGap, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
          norm_num
    · -- light edge (0,2): star atom 1 breaks the plus band
      intro _hshare
      refine ⟨1, by decide, Or.inr (bandBreak_of_two_readings ?_ ?_)⟩ <;>
        · simp [PhaseFreeData.excessGap, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
          norm_num
    · -- light edge (0,3): star atom 1 breaks the plus band
      intro _hshare
      refine ⟨1, by decide, Or.inr (bandBreak_of_two_readings ?_ ?_)⟩ <;>
        · simp [PhaseFreeData.excessGap, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
          norm_num
    · -- light edge (0,4): star atom 1 breaks the plus band
      intro _hshare
      refine ⟨1, by decide, Or.inr (bandBreak_of_two_readings ?_ ?_)⟩ <;>
        · simp [PhaseFreeData.excessGap, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
          norm_num
    · -- light edge (0,5): star atom 1 leaves the nonnegative-trace class
      intro _hshare
      refine ⟨1, by decide, Or.inl ?_⟩
      simp [PhaseFreeData.HasNonnegTraceLeg, PhaseFreeData.traceLeg,
        phaseFreeOfDesign, heavyExcess, atomPairing, leverageOf,
        exceptionalWitnessDesign, exceptionalWitnessAtom, dotProduct,
        Fin.sum_univ_three]
      norm_num
    · -- light edge (1,0): star atom 2 breaks the plus band
      intro _hshare
      refine ⟨2, by decide, Or.inr (bandBreak_of_two_readings ?_ ?_)⟩ <;>
        · simp [PhaseFreeData.excessGap, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
          norm_num
    · -- heavy edge (1,2): the light hypothesis is false
      intro hshare
      exact absurd hshare (by
        simp [PhaseFreeData.atomShare, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
        norm_num)
    · -- heavy edge (1,3): the light hypothesis is false
      intro hshare
      exact absurd hshare (by
        simp [PhaseFreeData.atomShare, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
        norm_num)
    · -- heavy edge (1,4): the light hypothesis is false
      intro hshare
      exact absurd hshare (by
        simp [PhaseFreeData.atomShare, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
        norm_num)
    · -- light edge (1,5): star atom 0 leaves the nonnegative-trace class
      intro _hshare
      refine ⟨0, by decide, Or.inl ?_⟩
      simp [PhaseFreeData.HasNonnegTraceLeg, PhaseFreeData.traceLeg,
        phaseFreeOfDesign, heavyExcess, atomPairing, leverageOf,
        exceptionalWitnessDesign, exceptionalWitnessAtom, dotProduct,
        Fin.sum_univ_three]
      norm_num
    · -- light edge (2,0): star atom 1 breaks the plus band
      intro _hshare
      refine ⟨1, by decide, Or.inr (bandBreak_of_two_readings ?_ ?_)⟩ <;>
        · simp [PhaseFreeData.excessGap, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
          norm_num
    · -- heavy edge (2,1): the light hypothesis is false
      intro hshare
      exact absurd hshare (by
        simp [PhaseFreeData.atomShare, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
        norm_num)
    · -- heavy edge (2,3): the light hypothesis is false
      intro hshare
      exact absurd hshare (by
        simp [PhaseFreeData.atomShare, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
        norm_num)
    · -- heavy edge (2,4): the light hypothesis is false
      intro hshare
      exact absurd hshare (by
        simp [PhaseFreeData.atomShare, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
        norm_num)
    · -- light edge (2,5): star atom 0 breaks the plus band
      intro _hshare
      refine ⟨0, by decide, Or.inr (bandBreak_of_two_readings ?_ ?_)⟩ <;>
        · simp [PhaseFreeData.excessGap, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
          norm_num
    · -- light edge (3,0): star atom 1 breaks the plus band
      intro _hshare
      refine ⟨1, by decide, Or.inr (bandBreak_of_two_readings ?_ ?_)⟩ <;>
        · simp [PhaseFreeData.excessGap, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
          norm_num
    · -- heavy edge (3,1): the light hypothesis is false
      intro hshare
      exact absurd hshare (by
        simp [PhaseFreeData.atomShare, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
        norm_num)
    · -- heavy edge (3,2): the light hypothesis is false
      intro hshare
      exact absurd hshare (by
        simp [PhaseFreeData.atomShare, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
        norm_num)
    · -- heavy edge (3,4): the light hypothesis is false
      intro hshare
      exact absurd hshare (by
        simp [PhaseFreeData.atomShare, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
        norm_num)
    · -- light edge (3,5): star atom 0 breaks the plus band
      intro _hshare
      refine ⟨0, by decide, Or.inr (bandBreak_of_two_readings ?_ ?_)⟩ <;>
        · simp [PhaseFreeData.excessGap, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
          norm_num
    · -- light edge (4,0): star atom 1 breaks the plus band
      intro _hshare
      refine ⟨1, by decide, Or.inr (bandBreak_of_two_readings ?_ ?_)⟩ <;>
        · simp [PhaseFreeData.excessGap, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
          norm_num
    · -- heavy edge (4,1): the light hypothesis is false
      intro hshare
      exact absurd hshare (by
        simp [PhaseFreeData.atomShare, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
        norm_num)
    · -- heavy edge (4,2): the light hypothesis is false
      intro hshare
      exact absurd hshare (by
        simp [PhaseFreeData.atomShare, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
        norm_num)
    · -- heavy edge (4,3): the light hypothesis is false
      intro hshare
      exact absurd hshare (by
        simp [PhaseFreeData.atomShare, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
        norm_num)
    · -- heavy edge (4,5): the light hypothesis is false
      intro hshare
      exact absurd hshare (by
        simp [PhaseFreeData.atomShare, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
        norm_num)
    · -- light edge (5,0): star atom 1 leaves the nonnegative-trace class
      intro _hshare
      refine ⟨1, by decide, Or.inl ?_⟩
      simp [PhaseFreeData.HasNonnegTraceLeg, PhaseFreeData.traceLeg,
        phaseFreeOfDesign, heavyExcess, atomPairing, leverageOf,
        exceptionalWitnessDesign, exceptionalWitnessAtom, dotProduct,
        Fin.sum_univ_three]
      norm_num
    · -- light edge (5,1): star atom 0 leaves the nonnegative-trace class
      intro _hshare
      refine ⟨0, by decide, Or.inl ?_⟩
      simp [PhaseFreeData.HasNonnegTraceLeg, PhaseFreeData.traceLeg,
        phaseFreeOfDesign, heavyExcess, atomPairing, leverageOf,
        exceptionalWitnessDesign, exceptionalWitnessAtom, dotProduct,
        Fin.sum_univ_three]
      norm_num
    · -- light edge (5,2): star atom 0 breaks the plus band
      intro _hshare
      refine ⟨0, by decide, Or.inr (bandBreak_of_two_readings ?_ ?_)⟩ <;>
        · simp [PhaseFreeData.excessGap, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
          norm_num
    · -- light edge (5,3): star atom 0 breaks the plus band
      intro _hshare
      refine ⟨0, by decide, Or.inr (bandBreak_of_two_readings ?_ ?_)⟩ <;>
        · simp [PhaseFreeData.excessGap, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
          norm_num
    · -- heavy edge (5,4): the light hypothesis is false
      intro hshare
      exact absurd hshare (by
        simp [PhaseFreeData.atomShare, phaseFreeOfDesign, heavyExcess,
          atomPairing, leverageOf, exceptionalWitnessDesign,
          exceptionalWitnessAtom, dotProduct, Fin.sum_univ_three]
        norm_num)

/-! ## The packaged inhabitation -/

/-- **THE QUANTIFIER DOMAIN OF `Gtz.GenericExceptionalSignClash` IS
KERNEL-INHABITED**: an exact rational all-heavy generic design with
exceptional phase-free image exists.  This retires the Phase-2 module
header's caveat that no design-level exceptional witness was kernel-checked;
the open proposition is not vacuously true. -/
theorem exists_allHeavy_generic_exceptional_design :
    ∃ D : WeightedDesign 6 3, AllHeavy D ∧ IsGenericDesign D
      ∧ (phaseFreeOfDesign D).IsExceptional :=
  ⟨exceptionalWitnessDesign, exceptionalWitnessDesign_allHeavy,
    exceptionalWitnessDesign_isGenericDesign,
    exceptionalWitnessDesign_isExceptional⟩

end Gtz
