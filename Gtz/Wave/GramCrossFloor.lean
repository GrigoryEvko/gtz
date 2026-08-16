import Gtz.Wave.CellCoverLattice

/-!
# The Gram floor on the cross term, and coherence read off magnitudes

Every cell in this campaign treats the sign of the triple product `(a·b)(a·c)(b·c)`
as unreadable from magnitudes.  `Gtz.tripleDetForm_neg_first` makes that look
forced: flipping one atom flips exactly two pairings, so the sign is invariant.
And `Gtz.signFreeMargin_pos_iff_both_signs` caps every certificate that declines
to read it.  This file shows the cap is a statement about FREE six-tuples, and
that realizable ones are constrained enough to read the sign anyway.

**The floor.**  `Gtz.sq_tripleBracket_eq_gramDet` writes the squared bracket as
the leverage-level even part plus twice the cross term.  A square is
non-negative, so

  `2 (a·b)(a·c)(b·c) ≥ - evenAtLeverage a b c`

with no hypothesis at all.  That is `Gtz.two_mul_atomCross_ge_neg_evenAtLeverage`,
and the campaign carried no lower bound on the cross term of any kind.

**Coherence from magnitudes.**  The floor is worth something exactly when the
leverage-level even part is negative, and then it forces the cross term strictly
positive: `Gtz.atomCross_pos_of_evenAtLeverage_neg`.  Both sides of that
implication read only leverages and pairing SQUARES, so the sign comes out of
sign-free data.

**Why this does not break the sign-blind ceiling.**  The ceiling quantifies over
free reals.  When the leverage-level even part is negative the flipped tuple has
a negative Gram determinant, so NO three vectors realize it
(`Gtz.not_exists_gram_of_flip_of_evenAtLeverage_neg`).  The ceiling still holds
where it is stated and it does not bind on realizable data.

**Where the certificate lives, exactly.**  At an admissible triple the pairing
energy is below the surplus pair sum (`Gtz.energy_lt_pairSurplusSum_of_admissible`),
so the leverage-level even part strictly exceeds the surplus-level one
(`Gtz.atomEvenPart_lt_evenAtLeverage_of_admissible`).  Hence the certificate
never fires while the surplus even part is positive, and it fires only inside the
cover's residue from `Gtz/Wave/CellCoverLattice.lean`.  That is exactly the
region every landed cell misses, and the certificate supplies its coherence half
for free.

**The witness.**  The atoms `(3,1,0)`, `(3,0,2)`, `(3,2,2)` are admissible, carry
`evenAtLeverage = -2430` and surplus even part `-2541`, and dominate with
`tripleGapDet = 33`.  Every landed cell fails there because the surplus even part
is negative, the new floor certifies coherence, and the bracket squared is `144`.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The leverage-level even part -/

/-- The even part of the Gram determinant: the part that reads every pairing
through its square only. -/
noncomputable def evenAtLeverage (a b c : Fin 3 → ℝ) : ℝ :=
  leverageOf a * leverageOf b * leverageOf c
    - leverageOf a * (b ⬝ᵥ c) ^ 2 - leverageOf b * (a ⬝ᵥ c) ^ 2 - leverageOf c * (a ⬝ᵥ b) ^ 2

theorem evenAtLeverage_apply (a b c : Fin 3 → ℝ) :
    evenAtLeverage a b c
      = leverageOf a * leverageOf b * leverageOf c
        - leverageOf a * (b ⬝ᵥ c) ^ 2 - leverageOf b * (a ⬝ᵥ c) ^ 2
        - leverageOf c * (a ⬝ᵥ b) ^ 2 := rfl

/-- The cross term of a triple of atoms. -/
noncomputable def atomTripleProduct (a b c : Fin 3 → ℝ) : ℝ := (a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c)

theorem atomCross_apply (a b c : Fin 3 → ℝ) :
    atomTripleProduct a b c = (a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c) := rfl

/-- **THE BRACKET SPLITS THE SAME WAY THE GAP DOES.**  The squared bracket is the
leverage-level even part plus twice the cross term, exactly as the third minor is
the surplus-level even part plus twice the cross term. -/
theorem sq_tripleBracket_eq_evenAtLeverage_add_cross (a b c : Fin 3 → ℝ) :
    tripleBracket a b c ^ 2 = evenAtLeverage a b c + 2 * atomTripleProduct a b c := by
  rw [sq_tripleBracket_eq_gramDet, evenAtLeverage, atomTripleProduct]; ring

/-! ## 2. The floor, and coherence from magnitudes -/

/-- **THE FLOOR ON THE CROSS TERM.**  Twice the cross term is at least minus the
leverage-level even part, with no hypothesis.  The whole content is that the
bracket is a real number, so its square is non-negative. -/
theorem two_mul_atomCross_ge_neg_evenAtLeverage (a b c : Fin 3 → ℝ) :
    -(evenAtLeverage a b c) ≤ 2 * atomTripleProduct a b c := by
  have hsq : 0 ≤ tripleBracket a b c ^ 2 := sq_nonneg _
  rw [sq_tripleBracket_eq_evenAtLeverage_add_cross] at hsq
  linarith

/-- The floor, stated as a bound on the cross term itself. -/
theorem atomCross_ge_neg_half_evenAtLeverage (a b c : Fin 3 → ℝ) :
    -(evenAtLeverage a b c) / 2 ≤ atomTripleProduct a b c := by
  have := two_mul_atomCross_ge_neg_evenAtLeverage a b c
  linarith

/-- **COHERENCE READ OFF MAGNITUDES.**  A negative leverage-level even part
forces the cross term strictly positive.  The hypothesis reads leverages and
pairing squares only, so the SIGN of the triple product comes out of sign-free
data. -/
theorem atomCross_pos_of_evenAtLeverage_neg (a b c : Fin 3 → ℝ)
    (h : evenAtLeverage a b c < 0) : 0 < atomTripleProduct a b c := by
  have := two_mul_atomCross_ge_neg_evenAtLeverage a b c
  linarith

theorem atomCross_nonneg_of_evenAtLeverage_nonpos (a b c : Fin 3 → ℝ)
    (h : evenAtLeverage a b c ≤ 0) : 0 ≤ atomTripleProduct a b c := by
  have := two_mul_atomCross_ge_neg_evenAtLeverage a b c
  linarith

/-- The floor is tight exactly at a dependent triple, where the bracket vanishes. -/
theorem two_mul_atomCross_eq_neg_evenAtLeverage_iff (a b c : Fin 3 → ℝ) :
    2 * atomTripleProduct a b c = -(evenAtLeverage a b c) ↔ tripleBracket a b c = 0 := by
  rw [← sub_eq_zero]
  constructor
  · intro h
    have hsq : tripleBracket a b c ^ 2 = 0 := by
      rw [sq_tripleBracket_eq_evenAtLeverage_add_cross]; linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  · intro h
    have hsq : tripleBracket a b c ^ 2 = 0 := by rw [h]; ring
    rw [sq_tripleBracket_eq_evenAtLeverage_add_cross] at hsq
    linarith

/-! ## 3. Why the sign-blind ceiling does not bind here

The ceiling is a statement about free six-tuples of reals.  When the
leverage-level even part is negative, the tuple with one pairing flipped has a
negative Gram determinant, so no three vectors carry it. -/

/-- **THE FLIPPED TUPLE IS NOT A GRAM.**  With a negative leverage-level even
part, no three atoms carry the same leverages and pairing squares and the
opposite triple product. -/
theorem not_exists_gram_of_flip_of_evenAtLeverage_neg (a b c : Fin 3 → ℝ)
    (h : evenAtLeverage a b c < 0) :
    ¬ ∃ x y z : Fin 3 → ℝ, evenAtLeverage x y z = evenAtLeverage a b c
      ∧ atomTripleProduct x y z = -(atomTripleProduct a b c) := by
  rintro ⟨x, y, z, heven, hcross⟩
  have hpos : 0 < atomTripleProduct a b c := atomCross_pos_of_evenAtLeverage_neg a b c h
  have hneg : evenAtLeverage x y z < 0 := by rw [heven]; exact h
  have := atomCross_pos_of_evenAtLeverage_neg x y z hneg
  rw [hcross] at this
  linarith

/-- The two even parts differ by a polynomial with no cross term in it. -/
theorem evenAtLeverage_sub_atomEvenPart (a b c : Fin 3 → ℝ) :
    evenAtLeverage a b c - atomEvenPart a b c
      = (leverageOf a - 1) * (leverageOf b - 1) + (leverageOf a - 1) * (leverageOf c - 1)
        + (leverageOf b - 1) * (leverageOf c - 1)
        + ((leverageOf a - 1) + (leverageOf b - 1) + (leverageOf c - 1)) + 1
        - ((a ⬝ᵥ b) ^ 2 + (a ⬝ᵥ c) ^ 2 + (b ⬝ᵥ c) ^ 2) := by
  rw [evenAtLeverage, atomEvenPart, evenTripleDetPart]; ring

/-! ## 4. Where the certificate can fire

An admissible triple keeps the pairing energy below the sum of the three surplus
products, so the leverage-level even part strictly exceeds the surplus-level one.
The certificate therefore never fires while the surplus even part is positive. -/

/-- **THE PAIRING ENERGY IS BELOW THE SURPLUS PAIR SUM.**  Each pairing square is
below its own surplus product, and summing the three is the statement. -/
theorem energy_lt_pairSurplusSum_of_admissible (a b c : Fin 3 → ℝ)
    (hab : 0 < pairGapMinor a b) (hac : 0 < pairGapMinor a c) (hbc : 0 < pairGapMinor b c) :
    (a ⬝ᵥ b) ^ 2 + (a ⬝ᵥ c) ^ 2 + (b ⬝ᵥ c) ^ 2
      < (leverageOf a - 1) * (leverageOf b - 1) + (leverageOf a - 1) * (leverageOf c - 1)
        + (leverageOf b - 1) * (leverageOf c - 1) := by
  rw [pairGapMinor] at hab hac hbc
  linarith

/-- **THE LEVERAGE EVEN PART STRICTLY EXCEEDS THE SURPLUS EVEN PART.**  The gap is
at least the surplus sum plus one, and it is strictly positive at every
admissible triple. -/
theorem atomEvenPart_lt_evenAtLeverage_of_admissible (a b c : Fin 3 → ℝ)
    (hab : 0 < pairGapMinor a b) (hac : 0 < pairGapMinor a c) (hbc : 0 < pairGapMinor b c)
    (ha : 1 < leverageOf a) (hb : 1 < leverageOf b) (hc : 1 < leverageOf c) :
    atomEvenPart a b c < evenAtLeverage a b c := by
  have hgap := evenAtLeverage_sub_atomEvenPart a b c
  have henergy := energy_lt_pairSurplusSum_of_admissible a b c hab hac hbc
  linarith

/-- **SO THE CERTIFICATE FIRES ONLY WHERE EVERY LANDED CELL FAILS.**  A negative
leverage-level even part forces the surplus even part negative too, which is
exactly the cover's residue condition. -/
theorem atomEvenPart_neg_of_evenAtLeverage_neg_of_admissible (a b c : Fin 3 → ℝ)
    (hab : 0 < pairGapMinor a b) (hac : 0 < pairGapMinor a c) (hbc : 0 < pairGapMinor b c)
    (ha : 1 < leverageOf a) (hb : 1 < leverageOf b) (hc : 1 < leverageOf c)
    (h : evenAtLeverage a b c < 0) : atomEvenPart a b c < 0 :=
  lt_trans (atomEvenPart_lt_evenAtLeverage_of_admissible a b c hab hac hbc ha hb hc) h

/-- **THE COVER'S RESIDUE, WITH ITS COHERENCE HALF CERTIFIED.**  At an admissible
dominating triple with a negative leverage-level even part, the triple sits in
the cover's residue and its coherence is read off magnitudes. -/
theorem atomCoverResidue_of_evenAtLeverage_neg (a b c : Fin 3 → ℝ)
    (hab : 0 < pairGapMinor a b) (hac : 0 < pairGapMinor a c) (hbc : 0 < pairGapMinor b c)
    (ha : 1 < leverageOf a) (hb : 1 < leverageOf b) (hc : 1 < leverageOf c)
    (h : evenAtLeverage a b c < 0) (_hdet : 0 < tripleGapDet a b c) :
    ¬ AtomTripleCover a b c ∧ 0 < atomTripleProduct a b c := by
  refine ⟨?_, atomCross_pos_of_evenAtLeverage_neg a b c h⟩
  rw [atomTripleCover_iff]
  rintro ⟨hEpos, _⟩
  exact absurd hEpos (not_lt.mpr (le_of_lt
    (atomEvenPart_neg_of_evenAtLeverage_neg_of_admissible a b c hab hac hbc ha hb hc h)))

/-! ## 5. The determinant in bracket coordinates

The third minor and the squared bracket share their cross term, so eliminating it
leaves a relation with no sign in it at all. -/

/-- **THE THIRD MINOR IS THE SQUARED BRACKET PLUS A SIGN-FREE CORRECTION.** -/
theorem tripleGapDet_eq_sq_tripleBracket_add_correction (a b c : Fin 3 → ℝ) :
    tripleGapDet a b c
      = tripleBracket a b c ^ 2
        + ((a ⬝ᵥ b) ^ 2 + (a ⬝ᵥ c) ^ 2 + (b ⬝ᵥ c) ^ 2)
        - ((leverageOf a - 1) * (leverageOf b - 1) + (leverageOf a - 1) * (leverageOf c - 1)
            + (leverageOf b - 1) * (leverageOf c - 1))
        - ((leverageOf a - 1) + (leverageOf b - 1) + (leverageOf c - 1)) - 1 := by
  rw [tripleGapDet_eq_tripleDetForm, tripleDetForm, sq_tripleBracket_eq_gramDet]; ring

/-- **THE BRACKET FLOOR ON A DOMINATING TRIPLE.**  Domination forces the squared
bracket above an explicit polynomial in the surpluses and pairing squares, with
no cross term and no sign. -/
theorem sq_tripleBracket_gt_of_tripleGapDet_pos (a b c : Fin 3 → ℝ)
    (hdet : 0 < tripleGapDet a b c) :
    ((leverageOf a - 1) * (leverageOf b - 1) + (leverageOf a - 1) * (leverageOf c - 1)
        + (leverageOf b - 1) * (leverageOf c - 1))
      + ((leverageOf a - 1) + (leverageOf b - 1) + (leverageOf c - 1)) + 1
      - ((a ⬝ᵥ b) ^ 2 + (a ⬝ᵥ c) ^ 2 + (b ⬝ᵥ c) ^ 2)
    < tripleBracket a b c ^ 2 := by
  have := tripleGapDet_eq_sq_tripleBracket_add_correction a b c
  linarith

/-- **AND THE FLOOR IS STRICTLY POSITIVE AT AN ADMISSIBLE TRIPLE.**  So every
admissible dominating triple carries a bracket bounded away from zero by data
that reads no sign. -/
theorem sq_tripleBracket_pos_of_admissible_of_tripleGapDet_pos (a b c : Fin 3 → ℝ)
    (hab : 0 < pairGapMinor a b) (hac : 0 < pairGapMinor a c) (hbc : 0 < pairGapMinor b c)
    (ha : 1 < leverageOf a) (hb : 1 < leverageOf b) (hc : 1 < leverageOf c)
    (hdet : 0 < tripleGapDet a b c) : 0 < tripleBracket a b c ^ 2 := by
  have hfloor := sq_tripleBracket_gt_of_tripleGapDet_pos a b c hdet
  have henergy := energy_lt_pairSurplusSum_of_admissible a b c hab hac hbc
  linarith

/-! ## 6. The witness

The three atoms below are admissible, sit in the cover's residue, dominate, and
have a negative leverage-level even part.  So the new floor certifies coherence
at a point where every landed cell fails. -/

/-- The first witness atom.  Given by cases rather than as a literal, because a
vector literal does not reduce at index two in this corpus. -/
def witnessAtomA : Fin 3 → ℝ
  | 0 => 3
  | 1 => 1
  | 2 => 0

/-- The second witness atom. -/
def witnessAtomB : Fin 3 → ℝ
  | 0 => 3
  | 1 => 0
  | 2 => 2

/-- The third witness atom. -/
def witnessAtomC : Fin 3 → ℝ
  | 0 => 3
  | 1 => 2
  | 2 => 2

theorem witness_leverages :
    leverageOf witnessAtomA = 10 ∧ leverageOf witnessAtomB = 13
      ∧ leverageOf witnessAtomC = 17 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [leverageOf, dotProduct, witnessAtomA, witnessAtomB, witnessAtomC,
      Fin.sum_univ_three]

theorem witness_pairings :
    witnessAtomA ⬝ᵥ witnessAtomB = 9 ∧ witnessAtomA ⬝ᵥ witnessAtomC = 11
      ∧ witnessAtomB ⬝ᵥ witnessAtomC = 13 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [dotProduct, witnessAtomA, witnessAtomB, witnessAtomC, Fin.sum_univ_three]

theorem witness_admissible :
    0 < pairGapMinor witnessAtomA witnessAtomB
      ∧ 0 < pairGapMinor witnessAtomA witnessAtomC
      ∧ 0 < pairGapMinor witnessAtomB witnessAtomC := by
  obtain ⟨hla, hlb, hlc⟩ := witness_leverages
  obtain ⟨hab, hac, hbc⟩ := witness_pairings
  refine ⟨?_, ?_, ?_⟩ <;> rw [pairGapMinor] <;>
    simp only [hla, hlb, hlc, hab, hac, hbc] <;> norm_num

theorem witness_heavy :
    1 < leverageOf witnessAtomA ∧ 1 < leverageOf witnessAtomB
      ∧ 1 < leverageOf witnessAtomC := by
  obtain ⟨hla, hlb, hlc⟩ := witness_leverages
  exact ⟨by rw [hla]; norm_num, by rw [hlb]; norm_num, by rw [hlc]; norm_num⟩

/-- **THE LEVERAGE EVEN PART IS NEGATIVE AT THE WITNESS.**  Its exact value is
`-2430`, so the new floor certifies a positive cross term there. -/
theorem witness_evenAtLeverage :
    evenAtLeverage witnessAtomA witnessAtomB witnessAtomC = -2430 := by
  obtain ⟨hla, hlb, hlc⟩ := witness_leverages
  obtain ⟨hab, hac, hbc⟩ := witness_pairings
  rw [evenAtLeverage, hla, hlb, hlc, hab, hac, hbc]; norm_num

/-- The surplus even part is `-2541`, so the witness is in the cover's residue. -/
theorem witness_atomEvenPart :
    atomEvenPart witnessAtomA witnessAtomB witnessAtomC = -2541 := by
  obtain ⟨hla, hlb, hlc⟩ := witness_leverages
  obtain ⟨hab, hac, hbc⟩ := witness_pairings
  rw [atomEvenPart, evenTripleDetPart, hla, hlb, hlc, hab, hac, hbc]; norm_num

/-- The cross term is `1287`, and the floor `1215` certifies it without reading
any sign. -/
theorem witness_atomCross : atomTripleProduct witnessAtomA witnessAtomB witnessAtomC = 1287 := by
  obtain ⟨hab, hac, hbc⟩ := witness_pairings
  rw [atomTripleProduct, hab, hac, hbc]; norm_num

theorem witness_atomCross_pos : 0 < atomTripleProduct witnessAtomA witnessAtomB witnessAtomC :=
  atomCross_pos_of_evenAtLeverage_neg _ _ _ (by rw [witness_evenAtLeverage]; norm_num)

/-- The squared bracket is `144`, matching the split exactly. -/
theorem witness_sq_tripleBracket :
    tripleBracket witnessAtomA witnessAtomB witnessAtomC ^ 2 = 144 := by
  rw [sq_tripleBracket_eq_evenAtLeverage_add_cross, witness_evenAtLeverage, witness_atomCross]
  norm_num

/-- **THE WITNESS DOMINATES.**  Its third minor is `33`, carried entirely by the
cross term against a surplus even part of `-2541`. -/
theorem witness_tripleGapDet :
    tripleGapDet witnessAtomA witnessAtomB witnessAtomC = 33 := by
  obtain ⟨hla, hlb, hlc⟩ := witness_leverages
  obtain ⟨hab, hac, hbc⟩ := witness_pairings
  rw [tripleGapDet_eq_tripleDetForm, tripleDetForm, hla, hlb, hlc, hab, hac, hbc]
  norm_num

/-! ## 7. What the witness settles -/

/-- **THE FLOOR IS NOT VACUOUS.**  There are three atoms with a negative
leverage-level even part, so the coherence certificate has content. -/
theorem exists_evenAtLeverage_neg :
    ∃ a b c : Fin 3 → ℝ, evenAtLeverage a b c < 0 ∧ 0 < atomTripleProduct a b c := by
  refine ⟨witnessAtomA, witnessAtomB, witnessAtomC, ?_, witness_atomCross_pos⟩
  rw [witness_evenAtLeverage]; norm_num

/-! ## 8. The other side of the sandwich

Realizability bounds the cross term from above as well.  The floor came from the
squared bracket being non-negative.  The ceiling comes from the two
Cauchy-Schwarz pair bounds, which an admissible heavy triple supplies for free. -/

/-- At an admissible heavy pair the pairing square is below the leverage product,
which is Cauchy-Schwarz with room to spare. -/
theorem sq_dotProduct_lt_leverage_mul (a b : Fin 3 → ℝ)
    (hab : 0 < pairGapMinor a b) (ha : 1 < leverageOf a) (hb : 1 < leverageOf b) :
    (a ⬝ᵥ b) ^ 2 < leverageOf a * leverageOf b := by
  rw [pairGapMinor] at hab
  nlinarith [hab, ha, hb]

/-- **THE CEILING ON THE CROSS TERM.**  Twice the cross term is below the
leverage-weighted pairing energy.  Together with the floor this sandwiches the
cross term between two quantities that read no sign. -/
theorem two_mul_atomTripleProduct_le_of_admissible (a b c : Fin 3 → ℝ)
    (hab : 0 < pairGapMinor a b) (hac : 0 < pairGapMinor a c)
    (ha : 1 < leverageOf a) (hb : 1 < leverageOf b) (hc : 1 < leverageOf c) :
    2 * atomTripleProduct a b c
      ≤ leverageOf a * (b ⬝ᵥ c) ^ 2 + leverageOf b * (a ⬝ᵥ c) ^ 2
        + leverageOf c * (a ⬝ᵥ b) ^ 2 := by
  have hu := sq_dotProduct_lt_leverage_mul a b hab ha hb
  have hv := sq_dotProduct_lt_leverage_mul a c hac ha hc
  have hapos : (0:ℝ) < leverageOf a := by linarith
  have hbpos : (0:ℝ) < leverageOf b := by linarith
  have hcpos : (0:ℝ) < leverageOf c := by linarith
  rw [atomTripleProduct]
  nlinarith [sq_nonneg (leverageOf a * (b ⬝ᵥ c) - (a ⬝ᵥ b) * (a ⬝ᵥ c)),
    hu, hv, hapos, hbpos, hcpos, sq_nonneg (a ⬝ᵥ b), sq_nonneg (a ⬝ᵥ c), sq_nonneg (b ⬝ᵥ c)]

/-- **THE SANDWICH.**  At an admissible heavy triple the cross term is trapped
between two explicit polynomials in the leverages and the pairing squares. -/
theorem atomTripleProduct_sandwich (a b c : Fin 3 → ℝ)
    (hab : 0 < pairGapMinor a b) (hac : 0 < pairGapMinor a c)
    (ha : 1 < leverageOf a) (hb : 1 < leverageOf b) (hc : 1 < leverageOf c) :
    -(evenAtLeverage a b c) ≤ 2 * atomTripleProduct a b c
      ∧ 2 * atomTripleProduct a b c
        ≤ leverageOf a * (b ⬝ᵥ c) ^ 2 + leverageOf b * (a ⬝ᵥ c) ^ 2
          + leverageOf c * (a ⬝ᵥ b) ^ 2 :=
  ⟨two_mul_atomCross_ge_neg_evenAtLeverage a b c,
    two_mul_atomTripleProduct_le_of_admissible a b c hab hac ha hb hc⟩

/-- **THE SQUARED BRACKET IS BELOW THE LEVERAGE PRODUCT.**  Hadamard's bound for
this Gram, read off the sandwich rather than proved spectrally. -/
theorem sq_tripleBracket_le_leverage_prod (a b c : Fin 3 → ℝ)
    (hab : 0 < pairGapMinor a b) (hac : 0 < pairGapMinor a c)
    (ha : 1 < leverageOf a) (hb : 1 < leverageOf b) (hc : 1 < leverageOf c) :
    tripleBracket a b c ^ 2 ≤ leverageOf a * leverageOf b * leverageOf c := by
  have hceil := two_mul_atomTripleProduct_le_of_admissible a b c hab hac ha hb hc
  rw [sq_tripleBracket_eq_evenAtLeverage_add_cross, evenAtLeverage]
  linarith

/-! ## 9. The certificate at the design level -/

/-- The leverage-level even part of three named labels of a design. -/
noncomputable def designEvenAtLeverage {m : ℕ} (D : WeightedDesign m 3) (x y z : Fin m) : ℝ :=
  evenAtLeverage (D.atom x) (D.atom y) (D.atom z)

/-- **THE COHERENCE CERTIFICATE, DESIGN LEVEL.**  A negative leverage-level even
part at three labels forces their triple product strictly positive. -/
theorem designAtomTripleProduct_pos_of_designEvenAtLeverage_neg {m : ℕ}
    (D : WeightedDesign m 3) (x y z : Fin m) (h : designEvenAtLeverage D x y z < 0) :
    0 < atomTripleProduct (D.atom x) (D.atom y) (D.atom z) :=
  atomCross_pos_of_evenAtLeverage_neg _ _ _ h

/-- **THE DESIGN-LEVEL RESIDUE WITH ITS COHERENCE CERTIFIED.**  At an admissible
heavy triple of a design with a negative leverage-level even part, the triple
escapes every landed cell and its coherence is read from magnitudes. -/
theorem designCoverResidue_coherence_certified {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m)
    (hab : 0 < pairGapMinor (D.atom x) (D.atom y))
    (hac : 0 < pairGapMinor (D.atom x) (D.atom z))
    (hbc : 0 < pairGapMinor (D.atom y) (D.atom z))
    (hx : 1 < leverageOf (D.atom x)) (hy : 1 < leverageOf (D.atom y))
    (hz : 1 < leverageOf (D.atom z))
    (h : designEvenAtLeverage D x y z < 0)
    (hdet : 0 < tripleGapDet (D.atom x) (D.atom y) (D.atom z)) :
    ¬ AtomTripleCover (D.atom x) (D.atom y) (D.atom z)
      ∧ 0 < atomTripleProduct (D.atom x) (D.atom y) (D.atom z) :=
  atomCoverResidue_of_evenAtLeverage_neg _ _ _ hab hac hbc hx hy hz h hdet

/-- **AND IT FIRES INSIDE THE COVER'S RESIDUE.**  At the witness the surplus even
part is negative, so no landed cell reaches the triple, while the floor still
reads its coherence. -/
theorem exists_coverResidue_with_certified_coherence :
    ∃ a b c : Fin 3 → ℝ,
      atomEvenPart a b c < 0 ∧ evenAtLeverage a b c < 0 ∧ 0 < atomTripleProduct a b c := by
  refine ⟨witnessAtomA, witnessAtomB, witnessAtomC, ?_, ?_, witness_atomCross_pos⟩
  · rw [witness_atomEvenPart]; norm_num
  · rw [witness_evenAtLeverage]; norm_num

end Gtz
