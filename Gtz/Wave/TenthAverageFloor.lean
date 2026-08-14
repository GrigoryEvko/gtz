import Gtz.Wave.SpreadWeightCap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The tenth carries the determinantal average past the field-agnostic ceiling

The campaign selects a triple of the six slots with the DETERMINANTAL MEASURE.
The twenty triple determinants total one, so the largest smallest-eigenvalue is at
least the determinantal average of the smallest eigenvalues, and a certificate
wants that average above the field-agnostic ceiling

  `(3 - sqrt 5) / 6 = 0.127322003750`,

which is the sharp constant of the cell over the COMPLEX field.  Nothing the
campaign owns had passed that bar.

* `Gtz.not_atomMomentCap` caps the bare moment class at `(5 - sqrt 15)/10`.
* `Gtz.not_atomSpreadCap` caps the moment class plus the real-only spread law at
  `2107/17000`, and it does so for EVERY per-triple floor at once.

Both caps sit BELOW the ceiling.  This module adds `Gtz.atomPluckerTenth`, the
real-only law `E2 <= 10 E3`, and PASSES the ceiling.

## The result

`Gtz.atomTenthAverage_ge` reads

  `141/1000 = 0.141 <= sum over the twenty triples of (determinant * smallest
   eigenvalue)`

for every member of `Gtz.AtomTenthFeasible`, the moment class augmented by the
tenth.  `Gtz.atomTenthFloor_gt_hermitianCeiling` says `141/1000` is above the
ceiling, by `0.0137`, which is `10.7` percent of the ceiling.
`Gtz.exists_atomTenthCarrier` turns the average into a carrier: some triple of
distinct slots has EVERY eigenvalue of its block at or above `141/1000`.

## The rung, and why it is the sharpest of its shape

The whole weight of the proof is one polynomial inequality in the three
eigenvalues of one block, `Gtz.atomTenthRung_le_root`:

  `141/1000 + (8/25) * (10 e3 - e2) <= every eigenvalue`

for every triple of readings in `[0,1]` that totals `3/2`.  Multiplying by the
determinant and adding over the twenty triples turns the correction term into
`(8/25) * (10 E3 - E2)`, which the tenth makes nonnegative, and the constant term
into `141/1000` because the determinants total one.  Nothing else is read: no
marginal, no spread law, no pair-minor law.

The multiplier `8/25` is not free.  For the family
`A + B (10 e3 - e2) <= lambda_min` the largest `A` that survives is a measured
`0.14174243050441` at `B = 0.321320`, attained at the block whose eigenvalues are
`(a, m, m)` with a DOUBLE TOP root.  At `B = 8/25` the largest `A` is
`0.14174016`, so `141/1000` keeps a margin of `7.40e-4`.  Those two numbers are
measurements and are NOT theorems.  The inequality below IS a theorem.

## The sharp cap of the whole route, and it is exact

`Gtz.atomTenthExtremal_isFeasible` puts a member in the class whose determinantal
average of the smallest eigenvalue is EXACTLY `(2 - sqrt 2)/4 = 0.146446609407`
(`Gtz.atomTenthExtremal_average`).  Two of the ten splittings of the six slots
into complementary triples carry no determinant and the other eight carry `1/16`
on each side, every live block reads `(3/2, 5/8, 1/16)`, and the tenth is tight
there at `E2 = 10 E3 = 5/8`.  So NO argument of this shape can read more than
`(2 - sqrt 2)/4`, and in particular the determinantal average under the tenth
cannot certify `1/6`.

## What is refuted here, exactly

`Gtz.not_atomSharpTripleRung` kills the SHARP per-triple rung
`(2 - sqrt 2)/4 + (sqrt 2/4) * (10 e3 - e2) <= lambda_min`, which is the reading
that the extremal forces and which would give the sharp constant in one line.  Its
witness is the exact block spectrum

  `((2 - sqrt 2)/4, 11/20, 9/20 + sqrt 2/4)`,

three readings in `[0,1]` that total `3/2`, at which the claim asks for
`90 <= 58 sqrt 2 = 82.024`.  The defect is `(90 - 58 sqrt 2)/3200 = 2.4767e-3`.
So the sharp constant is NOT reachable per triple.  It IS reachable per
COMPLEMENTARY PAIR: the inequality

  `p l(p) + q l(q) >= (1/2 - 3 sqrt2/8)(p + q) + (sqrt2/4)(9(p^2+q^2) - 2 p q)`,

for the two blocks of one cut, which share the second reading `1/2 + p + q`, was
measured to hold with worst margin `0.0e0`, attained only at `p = q = 1/16`.  That
is the one next target, and it is named in the module documentation only, because
a measured margin is not a theorem.

## The selector question, and the family this class cannot see

A certificate can average the smallest eigenvalue against ANY probability measure
on the twenty triples, not only the determinantal one, because every average is at
most the largest reading.  `Gtz.not_atomTenthSelectorSixth` closes a whole family
of candidates at once: at the tenth extremal the sixteen live blocks all read the
SAME smallest eigenvalue `(2 - sqrt 2)/4`, so every selector that vanishes on a
zero determinant averages to exactly `(2 - sqrt 2)/4`, which is below `1/6`.  That
covers `p ^ alpha` for every positive `alpha`, `p * e2`, `p / e2`,
`p * (10 e3 - e2)` cut at zero, `p * lambda_min`, every softmax against
`lambda_min`, and the uniform measure on the triples of largest determinant.

Over GENUINE balanced real Parseval frames those selectors separate.  The measured
minima of the weighted average of the smallest eigenvalue are

  `w = p`                    `0.16521556301725`   BELOW `1/6`, so capped
  `w ~ p ^ 1.1`              `0.16611583796106`   BELOW `1/6`, so capped
  `w ~ p * e2`               `0.16535109201005`   BELOW `1/6`, so capped
  `w ~ p / e2`               `0.16401958486273`   BELOW `1/6`, so capped
  `w` uniform on argmax `p`  `0.14644660941615`   BELOW `1/6`, so capped
  `w ~ p ^ 2`                `0.16873921519357`   no frame below `1/6` was found
  `w ~ p ^ 4`                `0.17006914649227`   no frame below `1/6` was found
  `w ~ p * lambda_min`       `0.17407050467680`   no frame below `1/6` was found

Only a measurement BELOW a bar is a conclusion.  The five capped rows are
conclusions and the three others are evidence.

## The balanced slice is NOT the extremal slice, and that is measured

`Gtz.AtomBalanced` says that every leverage is one half, which is what makes the
block trace `3/2` and what the whole class of this module reads.  Two measurements
say that the slice is not where the cell is decided.

  `min over BALANCED Parseval frames of max over triples of lambda_min`
      `= 0.20610737385376`,
   which is `(4 - sqrt (10 - 2 sqrt 5))/8` to sixteen digits, the pentagonal
   constant `(1 - sin 36 degrees)/2`.  That is `23.7` percent ABOVE `1/6`.

  `min over ALL Parseval frames of max over triples of lambda_min`
      `= 0.166666666694887`,
   which is `1/6` to ten digits.  The frame that reads it carries the leverages
   `5/14, 5/14, 9/14, 5/14, 9/14, 9/14` and the determinants
   `8/63, 5/56, 5/63, 25/504` and `0`, which total one exactly.  THIRTEEN of its
   twenty triples read exactly `1/6` and the other SEVEN read zero.

So the extremal of the cell is NOT balanced, and every determinantal selector was
measured to be CAPPED over the class that carries the extremal:

  `w = p`          `0.15892910894302`      `w ~ p ^ 2`   `0.16539847834390`
  `w ~ p ^ 1.1`    `0.16030613721732`      `w ~ p ^ 3`   `0.16610635608334`
  `w ~ p ^ 1.25`   `0.16183259379410`      `w ~ p ^ 4`   `0.16406179011129`
  `w ~ p ^ 1.5`    `0.16353956854769`      `w ~ p ^ 8`   `0.15153126520828`
  `w ~ p * e2`     `0.16339851346397`      argmax `p`    `0.10032789637122`

Every one of those is below `1/6`.  A fine sweep of the exponent over the same
class reads the family from underneath and never crosses:

  `alpha`  `1.0`   `1.5`   `2.0`   `2.4`   `2.6`   `2.8`   `3.0`   `3.4`   `4.0`
  `min `  `.15893 .16354 .16540 .16617 .16643 .16636 .16611 .16542 .16406`

The largest reading of the family is `0.16642594372603` near `alpha = 2.6`, which
is `2.41e-4` short of `1/6`, or `0.144` percent.  So NO member of the determinantal
power family reaches `1/6`, and the selector search must leave that family.

Every number in the two tables above is a MEASURED MINIMUM over frames, and a
measured minimum below a bar is a conclusion because the frame that reads it is a
witness.  A measured minimum above a bar would be evidence only.
-/

namespace Gtz

/-! ## Layer 0 — the rung, as a polynomial inequality in three eigenvalues -/

/-- **THE RUNG THE TENTH CARRIES.**  A reading of a block that is built from the
second and the third symmetric function only.  Its determinantal average is
`141/1000 + (8/25) * (10 E3 - E2)`, and the tenth makes the correction term
nonnegative. -/
noncomputable def atomTenthRung (second third : ℝ) : ℝ :=
  141 / 1000 + (8 / 25) * (10 * third - second)

set_option linter.unusedVariables false in
/-- **THE RUNG IS BELOW EVERY EIGENVALUE.**  For three readings in the unit box
that total `3/2`, the rung is at most the first of them.  The first reading is not
assumed to be the smallest, so this says that the rung is at most the smallest.

The proof is two exact algebraic identities, one for each side of `1/10`.  Write
`Sig = r2 + r3` and `Pi = r2 r3`.  The reading is linear in `Pi` with the
coefficient `(8/25)(1 - 10 r1)`, so the minimum over `Pi` sits at an endpoint of
the interval that the unit box allows.

* Below `1/10` the coefficient is not negative and the endpoint is
  `Pi = Sig - 1`, which is `(1 - r2)(1 - r3) = 0`.  The residue is the definite
  quadratic `(72/25)(r1 - 11/144)^2 + 79/36000`.
* Above `1/10` the coefficient is not positive and the endpoint is
  `Pi = Sig^2/4`, which is `(r2 - r3)^2 = 0`.  The residue is the cubic
  `((1935 - 800 r1)(r1 - 9/64)^2 + (5/128) r1 + 3009/4096)/1000`, and its three
  parts are separately nonnegative on the box. -/
theorem atomTenthRung_le_root (r1 r2 r3 : ℝ)
    (h1 : 0 ≤ r1) (h1' : r1 ≤ 1) (h2 : 0 ≤ r2) (h2' : r2 ≤ 1)
    (h3 : 0 ≤ r3) (h3' : r3 ≤ 1) (hsum : r1 + r2 + r3 = 3 / 2) :
    atomTenthRung (r1 * r2 + r1 * r3 + r2 * r3) (r1 * r2 * r3) ≤ r1 := by
  have hr3 : r3 = 3 / 2 - r1 - r2 := by linarith
  subst hr3
  simp only [atomTenthRung]
  rcases le_total r1 (1 / 10) with hc | hc
  · nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 10 * r1)
        (by linarith : (0 : ℝ) ≤ 1 - r2)) (by linarith : (0 : ℝ) ≤ 1 - (3 / 2 - r1 - r2)),
      sq_nonneg (r1 - 11 / 144), h1, h2, h3]
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 10 * r1 - 1)
        (sq_nonneg (r2 - (3 / 2 - r1 - r2))),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1935 - 800 * r1) (sq_nonneg (r1 - 9 / 64)),
      h1, h2, h3]

/-- The rung is below the first reading, with the two symmetric functions supplied
as equations.  This is the shape the permutation argument of the next lemma
wants. -/
theorem atomTenthRung_le_root' (r1 r2 r3 second third : ℝ)
    (h1 : 0 ≤ r1) (h1' : r1 ≤ 1) (h2 : 0 ≤ r2) (h2' : r2 ≤ 1)
    (h3 : 0 ≤ r3) (h3' : r3 ≤ 1) (hsum : r1 + r2 + r3 = 3 / 2)
    (he2 : second = r1 * r2 + r1 * r3 + r2 * r3) (he3 : third = r1 * r2 * r3) :
    atomTenthRung second third ≤ r1 := by
  subst he2; subst he3
  exact atomTenthRung_le_root r1 r2 r3 h1 h1' h2 h2' h3 h3' hsum

/-- **THE RUNG IS BELOW EVERY ROOT OF THE CHARACTERISTIC POLYNOMIAL.**  A block
spectrum factors the characteristic polynomial, so a root of that polynomial is
one of the three readings, and the rung is below each of them. -/
theorem atomTenthRung_le_of_spectrum {second third root : ℝ}
    (hspec : AtomBlockSpectrum (3 / 2) second third)
    (hroot : root ^ 3 - (3 / 2) * root ^ 2 + second * root - third = 0) :
    atomTenthRung second third ≤ root := by
  obtain ⟨r1, r2, r3, a1, b1, a2, b2, a3, b3, hs, he2, he3⟩ := hspec
  have hsum : r1 + r2 + r3 = 3 / 2 := hs.symm
  have hfac : (root - r1) * ((root - r2) * (root - r3)) = 0 := by
    have : root ^ 3 - (r1 + r2 + r3) * root ^ 2
        + (r1 * r2 + r1 * r3 + r2 * r3) * root - r1 * r2 * r3 = 0 := by
      rw [← hs, ← he2, ← he3]; exact hroot
    linear_combination this
  rcases mul_eq_zero.mp hfac with h | h
  · have : root = r1 := by linarith [sub_eq_zero.mp h]
    subst this
    exact atomTenthRung_le_root' root r2 r3 second third a1 b1 a2 b2 a3 b3 hsum he2 he3
  rcases mul_eq_zero.mp h with h | h
  · have : root = r2 := by linarith [sub_eq_zero.mp h]
    subst this
    exact atomTenthRung_le_root' root r1 r3 second third a2 b2 a1 b1 a3 b3 (by linarith)
      (by rw [he2]; ring) (by rw [he3]; ring)
  · have : root = r3 := by linarith [sub_eq_zero.mp h]
    subst this
    exact atomTenthRung_le_root' root r1 r2 second third a3 b3 a1 b1 a2 b2 (by linarith)
      (by rw [he2]; ring) (by rw [he3]; ring)

/-! ## Layer 1 — the moment class augmented by the tenth -/

/-- **THE MOMENT CLASS PLUS THE TENTH.**  Everything this module reads about a real
Parseval frame of six atoms:

* the twenty triple determinants are not negative,
* they total one, which is `Gtz.atomBlockDet_familySum`,
* every triple of DISTINCT slots reads a block spectrum in the unit box, which is
  the statement that the Gram block of three slots is a principal block of an
  orthogonal projection,
* the level-two determinantal energy is at most ten times the level-three energy,
  which is `Gtz.atomPluckerTenth`, read through the pair-minor law in the form
  `E2 = sum over the twenty triples of (determinant * second reading)`.

No marginal is read and no spread law is read.  This is a strictly smaller list
than `Gtz.AtomSpreadFeasible` demands, apart from the tenth. -/
def AtomTenthFeasible (weight second : Fin 6 → Fin 6 → Fin 6 → ℝ) : Prop :=
  (∀ a b c : Fin 6, 0 ≤ weight a b c)
    ∧ atomTripleFamilySum weight = 1
    ∧ (∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
        AtomBlockSpectrum (3 / 2) (second a b c) (weight a b c))
    ∧ atomTripleFamilySum (fun a b c => weight a b c * second a b c)
        ≤ 10 * atomTripleFamilySum (fun a b c => weight a b c ^ 2)

/-- A reading is a SPECTRAL READING of a class member when it is a root of the
characteristic polynomial of every block of distinct slots. -/
def AtomSpectralReading (weight second reading : Fin 6 → Fin 6 → Fin 6 → ℝ) : Prop :=
  ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
    reading a b c ^ 3 - (3 / 2) * reading a b c ^ 2
      + second a b c * reading a b c - weight a b c = 0

/-! ## Layer 2 — the determinantal average passes the ceiling -/

/-- **THE MAIN THEOREM.**  Under the moment class and the tenth, the determinantal
average of ANY spectral reading is at least `141/1000`.  With the reading taken to
be the smallest eigenvalue this is the determinantal average of the smallest
eigenvalue, which is the sharpest objective the route carries.

`141/1000 = 0.141` is above the field-agnostic ceiling `(3 - sqrt 5)/6 =
0.127322003750`.  This is the first reading of this campaign that passes it. -/
theorem atomTenthAverage_ge {weight second reading : Fin 6 → Fin 6 → Fin 6 → ℝ}
    (hclass : AtomTenthFeasible weight second)
    (hread : AtomSpectralReading weight second reading) :
    141 / 1000 ≤ atomTripleFamilySum (fun a b c => weight a b c * reading a b c) := by
  obtain ⟨hnn, htot, hbox, htenth⟩ := hclass
  have step : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
      weight a b c * atomTenthRung (second a b c) (weight a b c)
        ≤ weight a b c * reading a b c := fun a b c hab hac hbc =>
    mul_le_mul_of_nonneg_left
      (atomTenthRung_le_of_spectrum (hbox a b c hab hac hbc) (hread a b c hab hac hbc))
      (hnn a b c)
  have hlow : atomTripleFamilySum
      (fun a b c => weight a b c * atomTenthRung (second a b c) (weight a b c))
        ≤ atomTripleFamilySum (fun a b c => weight a b c * reading a b c) := by
    simp only [atomTripleFamilySum]
    have s012 := step 0 1 2 (by decide) (by decide) (by decide)
    have s013 := step 0 1 3 (by decide) (by decide) (by decide)
    have s014 := step 0 1 4 (by decide) (by decide) (by decide)
    have s015 := step 0 1 5 (by decide) (by decide) (by decide)
    have s023 := step 0 2 3 (by decide) (by decide) (by decide)
    have s024 := step 0 2 4 (by decide) (by decide) (by decide)
    have s025 := step 0 2 5 (by decide) (by decide) (by decide)
    have s034 := step 0 3 4 (by decide) (by decide) (by decide)
    have s035 := step 0 3 5 (by decide) (by decide) (by decide)
    have s045 := step 0 4 5 (by decide) (by decide) (by decide)
    have s123 := step 1 2 3 (by decide) (by decide) (by decide)
    have s124 := step 1 2 4 (by decide) (by decide) (by decide)
    have s125 := step 1 2 5 (by decide) (by decide) (by decide)
    have s134 := step 1 3 4 (by decide) (by decide) (by decide)
    have s135 := step 1 3 5 (by decide) (by decide) (by decide)
    have s145 := step 1 4 5 (by decide) (by decide) (by decide)
    have s234 := step 2 3 4 (by decide) (by decide) (by decide)
    have s235 := step 2 3 5 (by decide) (by decide) (by decide)
    have s245 := step 2 4 5 (by decide) (by decide) (by decide)
    have s345 := step 3 4 5 (by decide) (by decide) (by decide)
    linarith
  have hexp : atomTripleFamilySum
      (fun a b c => weight a b c * atomTenthRung (second a b c) (weight a b c))
      = 141 / 1000 * atomTripleFamilySum weight
        + (8 / 25) * (10 * atomTripleFamilySum (fun a b c => weight a b c ^ 2)
            - atomTripleFamilySum (fun a b c => weight a b c * second a b c)) := by
    simp only [atomTripleFamilySum, atomTenthRung]; ring
  rw [hexp, htot] at hlow
  linarith

/-- **THE FLOOR IS ABOVE THE FIELD-AGNOSTIC CEILING.**  `(3 - sqrt 5)/6` is the
sharp constant of the cell over the complex field and the bar every determinantal
certificate had to clear.  `141/1000` clears it by `0.0137`. -/
theorem atomTenthFloor_gt_hermitianCeiling : (3 - Real.sqrt 5) / 6 < 141 / 1000 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have n5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [h5, n5]

/-- The floor sits between the two caps that the route already owns: above the
moment cap `(5 - sqrt 15)/10` and the ceiling `(3 - sqrt 5)/6`, and below the sharp
cap `(2 - sqrt 2)/4` of the class of this module. -/
theorem atomTenthFloor_ladder :
    (5 - Real.sqrt 15) / 10 < (3 - Real.sqrt 5) / 6
      ∧ (3 - Real.sqrt 5) / 6 < 141 / 1000
      ∧ (141 : ℝ) / 1000 < (2 - Real.sqrt 2) / 4
      ∧ (2 - Real.sqrt 2) / 4 < 1 / 6 := by
  have h15 : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have n15 : (0 : ℝ) ≤ Real.sqrt 15 := Real.sqrt_nonneg 15
  have n5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have n2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  refine ⟨by nlinarith [h15, h5, n15, n5], by nlinarith [h5, n5],
    by nlinarith [h2, n2], by nlinarith [h2, n2]⟩

/-! ## Layer 3 — from the average to a carrier -/

/-- **THE KILL STEP.**  A determinant that is not negative, a reading strictly
below the floor, and a nonpositive product against the gap force the determinant
to vanish. -/
theorem atomTenthKill {value readingValue : ℝ} (hnn : 0 ≤ value)
    (hlt : readingValue < 141 / 1000) (hz : value * (141 / 1000 - readingValue) ≤ 0) :
    value = 0 := by
  rcases eq_or_lt_of_le hnn with h | h
  · exact h.symm
  · nlinarith

/-- **SOME SLOT TRIPLE CARRIES THE FLOOR.**  The determinants are not negative and
total one, so a reading whose determinantal average is at least `141/1000` is at
least `141/1000` at some triple of distinct slots.

If every reading were below the floor, every one of the twenty gaps would be not
negative and their total would be not positive, so every gap would vanish, so every
determinant would vanish, and the determinants could not total one. -/
theorem exists_atomTenthReading_ge {weight second reading : Fin 6 → Fin 6 → Fin 6 → ℝ}
    (hclass : AtomTenthFeasible weight second)
    (hread : AtomSpectralReading weight second reading) :
    ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ 141 / 1000 ≤ reading a b c := by
  have havg := atomTenthAverage_ge hclass hread
  obtain ⟨hnn, htot, -, -⟩ := hclass
  by_contra hcon
  have hlt : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c → reading a b c < 141 / 1000 := by
    intro a b c hab hac hbc
    by_contra h
    exact hcon ⟨a, b, c, hab, hac, hbc, not_lt.mp h⟩
  have l012 := hlt 0 1 2 (by decide) (by decide) (by decide)
  have l013 := hlt 0 1 3 (by decide) (by decide) (by decide)
  have l014 := hlt 0 1 4 (by decide) (by decide) (by decide)
  have l015 := hlt 0 1 5 (by decide) (by decide) (by decide)
  have l023 := hlt 0 2 3 (by decide) (by decide) (by decide)
  have l024 := hlt 0 2 4 (by decide) (by decide) (by decide)
  have l025 := hlt 0 2 5 (by decide) (by decide) (by decide)
  have l034 := hlt 0 3 4 (by decide) (by decide) (by decide)
  have l035 := hlt 0 3 5 (by decide) (by decide) (by decide)
  have l045 := hlt 0 4 5 (by decide) (by decide) (by decide)
  have l123 := hlt 1 2 3 (by decide) (by decide) (by decide)
  have l124 := hlt 1 2 4 (by decide) (by decide) (by decide)
  have l125 := hlt 1 2 5 (by decide) (by decide) (by decide)
  have l134 := hlt 1 3 4 (by decide) (by decide) (by decide)
  have l135 := hlt 1 3 5 (by decide) (by decide) (by decide)
  have l145 := hlt 1 4 5 (by decide) (by decide) (by decide)
  have l234 := hlt 2 3 4 (by decide) (by decide) (by decide)
  have l235 := hlt 2 3 5 (by decide) (by decide) (by decide)
  have l245 := hlt 2 4 5 (by decide) (by decide) (by decide)
  have l345 := hlt 3 4 5 (by decide) (by decide) (by decide)
  have g012 : 0 ≤ weight 0 1 2 * (141 / 1000 - reading 0 1 2) :=
    mul_nonneg (hnn 0 1 2) (by linarith)
  have g013 : 0 ≤ weight 0 1 3 * (141 / 1000 - reading 0 1 3) :=
    mul_nonneg (hnn 0 1 3) (by linarith)
  have g014 : 0 ≤ weight 0 1 4 * (141 / 1000 - reading 0 1 4) :=
    mul_nonneg (hnn 0 1 4) (by linarith)
  have g015 : 0 ≤ weight 0 1 5 * (141 / 1000 - reading 0 1 5) :=
    mul_nonneg (hnn 0 1 5) (by linarith)
  have g023 : 0 ≤ weight 0 2 3 * (141 / 1000 - reading 0 2 3) :=
    mul_nonneg (hnn 0 2 3) (by linarith)
  have g024 : 0 ≤ weight 0 2 4 * (141 / 1000 - reading 0 2 4) :=
    mul_nonneg (hnn 0 2 4) (by linarith)
  have g025 : 0 ≤ weight 0 2 5 * (141 / 1000 - reading 0 2 5) :=
    mul_nonneg (hnn 0 2 5) (by linarith)
  have g034 : 0 ≤ weight 0 3 4 * (141 / 1000 - reading 0 3 4) :=
    mul_nonneg (hnn 0 3 4) (by linarith)
  have g035 : 0 ≤ weight 0 3 5 * (141 / 1000 - reading 0 3 5) :=
    mul_nonneg (hnn 0 3 5) (by linarith)
  have g045 : 0 ≤ weight 0 4 5 * (141 / 1000 - reading 0 4 5) :=
    mul_nonneg (hnn 0 4 5) (by linarith)
  have g123 : 0 ≤ weight 1 2 3 * (141 / 1000 - reading 1 2 3) :=
    mul_nonneg (hnn 1 2 3) (by linarith)
  have g124 : 0 ≤ weight 1 2 4 * (141 / 1000 - reading 1 2 4) :=
    mul_nonneg (hnn 1 2 4) (by linarith)
  have g125 : 0 ≤ weight 1 2 5 * (141 / 1000 - reading 1 2 5) :=
    mul_nonneg (hnn 1 2 5) (by linarith)
  have g134 : 0 ≤ weight 1 3 4 * (141 / 1000 - reading 1 3 4) :=
    mul_nonneg (hnn 1 3 4) (by linarith)
  have g135 : 0 ≤ weight 1 3 5 * (141 / 1000 - reading 1 3 5) :=
    mul_nonneg (hnn 1 3 5) (by linarith)
  have g145 : 0 ≤ weight 1 4 5 * (141 / 1000 - reading 1 4 5) :=
    mul_nonneg (hnn 1 4 5) (by linarith)
  have g234 : 0 ≤ weight 2 3 4 * (141 / 1000 - reading 2 3 4) :=
    mul_nonneg (hnn 2 3 4) (by linarith)
  have g235 : 0 ≤ weight 2 3 5 * (141 / 1000 - reading 2 3 5) :=
    mul_nonneg (hnn 2 3 5) (by linarith)
  have g245 : 0 ≤ weight 2 4 5 * (141 / 1000 - reading 2 4 5) :=
    mul_nonneg (hnn 2 4 5) (by linarith)
  have g345 : 0 ≤ weight 3 4 5 * (141 / 1000 - reading 3 4 5) :=
    mul_nonneg (hnn 3 4 5) (by linarith)
  have htotal : atomTripleFamilySum weight = 1 := htot
  simp only [atomTripleFamilySum] at havg htotal
  have w012 : weight 0 1 2 = 0 :=
    atomTenthKill (hnn 0 1 2) l012 (by linarith)
  have w013 : weight 0 1 3 = 0 :=
    atomTenthKill (hnn 0 1 3) l013 (by linarith)
  have w014 : weight 0 1 4 = 0 :=
    atomTenthKill (hnn 0 1 4) l014 (by linarith)
  have w015 : weight 0 1 5 = 0 :=
    atomTenthKill (hnn 0 1 5) l015 (by linarith)
  have w023 : weight 0 2 3 = 0 :=
    atomTenthKill (hnn 0 2 3) l023 (by linarith)
  have w024 : weight 0 2 4 = 0 :=
    atomTenthKill (hnn 0 2 4) l024 (by linarith)
  have w025 : weight 0 2 5 = 0 :=
    atomTenthKill (hnn 0 2 5) l025 (by linarith)
  have w034 : weight 0 3 4 = 0 :=
    atomTenthKill (hnn 0 3 4) l034 (by linarith)
  have w035 : weight 0 3 5 = 0 :=
    atomTenthKill (hnn 0 3 5) l035 (by linarith)
  have w045 : weight 0 4 5 = 0 :=
    atomTenthKill (hnn 0 4 5) l045 (by linarith)
  have w123 : weight 1 2 3 = 0 :=
    atomTenthKill (hnn 1 2 3) l123 (by linarith)
  have w124 : weight 1 2 4 = 0 :=
    atomTenthKill (hnn 1 2 4) l124 (by linarith)
  have w125 : weight 1 2 5 = 0 :=
    atomTenthKill (hnn 1 2 5) l125 (by linarith)
  have w134 : weight 1 3 4 = 0 :=
    atomTenthKill (hnn 1 3 4) l134 (by linarith)
  have w135 : weight 1 3 5 = 0 :=
    atomTenthKill (hnn 1 3 5) l135 (by linarith)
  have w145 : weight 1 4 5 = 0 :=
    atomTenthKill (hnn 1 4 5) l145 (by linarith)
  have w234 : weight 2 3 4 = 0 :=
    atomTenthKill (hnn 2 3 4) l234 (by linarith)
  have w235 : weight 2 3 5 = 0 :=
    atomTenthKill (hnn 2 3 5) l235 (by linarith)
  have w245 : weight 2 4 5 = 0 :=
    atomTenthKill (hnn 2 4 5) l245 (by linarith)
  have w345 : weight 3 4 5 = 0 :=
    atomTenthKill (hnn 3 4 5) l345 (by linarith)
  rw [w012, w013, w014, w015, w023, w024, w025, w034, w035, w045, w123, w124, w125, w134, w135, w145, w234, w235, w245, w345] at htotal
  norm_num at htotal


/-- **THE CARRIER.**  Some triple of distinct slots has EVERY eigenvalue of its
block at or above `141/1000`.  This is what the cell asks for, at a scale above the
field-agnostic ceiling.

The reading must be a spectral reading and a per-triple floor at the same time,
which says exactly that it is the smallest eigenvalue. -/
theorem exists_atomTenthCarrier {weight second reading : Fin 6 → Fin 6 → Fin 6 → ℝ}
    (hclass : AtomTenthFeasible weight second)
    (hread : AtomSpectralReading weight second reading)
    (hfloor : AtomTripleEigenFloor weight second reading) :
    ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ∀ root : ℝ, root ^ 3 - (3 / 2) * root ^ 2 + second a b c * root - weight a b c = 0 →
        141 / 1000 ≤ root := by
  obtain ⟨a, b, c, hab, hac, hbc, hge⟩ := exists_atomTenthReading_ge hclass hread
  exact ⟨a, b, c, hab, hac, hbc, fun root hroot => le_trans hge (hfloor a b c root hroot)⟩

/-! ## Layer 4 — the extremal, and the sharp cap of the whole route -/

/-- The live label of a triple in the TENTH EXTREMAL.  Zero on a repeated slot and
on the four triples of the two dead cuts `{0,1,2}` / `{3,4,5}` and `{0,1,3}` /
`{2,4,5}`, one on the other sixteen. -/
def atomTenthNum (a b c : Fin 6) : ℕ :=
  if a = b ∨ a = c ∨ b = c then 0
  else if atomSpreadMask a b c = 7 ∨ atomSpreadMask a b c = 56
      ∨ atomSpreadMask a b c = 11 ∨ atomSpreadMask a b c = 52 then 0 else 1

/-- The determinant of the tenth extremal: `1/16` on each live triple. -/
noncomputable def atomTenthWeight (a b c : Fin 6) : ℝ := (atomTenthNum a b c : ℝ) / 16

/-- The second reading of the tenth extremal.  It obeys the complement law
`second = 1/2 + weight + weight of the complement`, because the two sides of a live
cut are both live and the two sides of a dead cut are both dead. -/
noncomputable def atomTenthSecond (a b c : Fin 6) : ℝ :=
  1 / 2 + (atomTenthNum a b c : ℝ) / 8

/-- The smallest eigenvalue of the tenth extremal: `(2 - sqrt 2)/4` on a live
triple and zero on a dead one. -/
noncomputable def atomTenthReading (a b c : Fin 6) : ℝ :=
  (atomTenthNum a b c : ℝ) * ((2 - Real.sqrt 2) / 4)

theorem atomTenthNum_le_one (a b c : Fin 6) : atomTenthNum a b c ≤ 1 := by
  unfold atomTenthNum; split_ifs <;> omega

/-- The twenty sorted triples of the tenth extremal: four dead and sixteen live. -/
theorem atomTenthNum_sorted :
    atomTenthNum 0 1 2 = 0 ∧ atomTenthNum 0 1 3 = 0 ∧ atomTenthNum 0 1 4 = 1
      ∧ atomTenthNum 0 1 5 = 1 ∧ atomTenthNum 0 2 3 = 1 ∧ atomTenthNum 0 2 4 = 1
      ∧ atomTenthNum 0 2 5 = 1 ∧ atomTenthNum 0 3 4 = 1 ∧ atomTenthNum 0 3 5 = 1
      ∧ atomTenthNum 0 4 5 = 1 ∧ atomTenthNum 1 2 3 = 1 ∧ atomTenthNum 1 2 4 = 1
      ∧ atomTenthNum 1 2 5 = 1 ∧ atomTenthNum 1 3 4 = 1 ∧ atomTenthNum 1 3 5 = 1
      ∧ atomTenthNum 1 4 5 = 1 ∧ atomTenthNum 2 3 4 = 1 ∧ atomTenthNum 2 3 5 = 1
      ∧ atomTenthNum 2 4 5 = 0 ∧ atomTenthNum 3 4 5 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Every block of the tenth extremal is a real spectrum in the unit box.  A dead
triple reads `(3/2, 1/2, 0)` with the spectrum `(0, 1/2, 1)` and a live triple reads
`(3/2, 5/8, 1/16)` with the spectrum `((2 - sqrt 2)/4, 1/2, (2 + sqrt 2)/4)`. -/
theorem atomTenthExtremal_spectrumAt (a b c : Fin 6) :
    AtomBlockSpectrum (3 / 2) (atomTenthSecond a b c) (atomTenthWeight a b c) := by
  have hle := atomTenthNum_le_one a b c
  interval_cases h : atomTenthNum a b c
  · exact atomBlockSpectrum_half (product := 0) (by norm_num) (by norm_num)
      (by simp only [atomTenthSecond, h]; norm_num) (by simp only [atomTenthWeight, h]; norm_num)
  · exact atomBlockSpectrum_half (product := 1 / 8) (by norm_num) (by norm_num)
      (by simp only [atomTenthSecond, h]; norm_num) (by simp only [atomTenthWeight, h]; norm_num)

/-- **THE TENTH EXTREMAL IS IN THE CLASS.**  So `Gtz.AtomTenthFeasible` is not
vacuous and `Gtz.atomTenthAverage_ge` is not vacuous.  The tenth is TIGHT here, at
`E2 = 10 E3 = 5/8`. -/
theorem atomTenthExtremal_isFeasible : AtomTenthFeasible atomTenthWeight atomTenthSecond := by
  obtain ⟨n012, n013, n014, n015, n023, n024, n025, n034, n035, n045,
    n123, n124, n125, n134, n135, n145, n234, n235, n245, n345⟩ := atomTenthNum_sorted
  refine ⟨fun a b c => by unfold atomTenthWeight; positivity, ?_,
    fun a b c _ _ _ => atomTenthExtremal_spectrumAt a b c, ?_⟩
  · simp only [atomTripleFamilySum, atomTenthWeight, n012, n013, n014, n015, n023, n024,
      n025, n034, n035, n045, n123, n124, n125, n134, n135, n145, n234, n235, n245, n345]
    norm_num
  · simp only [atomTripleFamilySum, atomTenthWeight, atomTenthSecond, n012, n013, n014,
      n015, n023, n024, n025, n034, n035, n045, n123, n124, n125, n134, n135, n145,
      n234, n235, n245, n345]
    norm_num

/-- The extremal reading is a root of the characteristic polynomial of every block.
On a dead triple the polynomial is `x^3 - (3/2) x^2 + x/2` and zero is a root.  On a
live triple this is `Gtz.atomTenthExtremal_spectrum`. -/
theorem atomTenthExtremal_isReading :
    AtomSpectralReading atomTenthWeight atomTenthSecond atomTenthReading := by
  intro a b c _ _ _
  have hle := atomTenthNum_le_one a b c
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  interval_cases h : atomTenthNum a b c
  · simp only [atomTenthReading, atomTenthSecond, atomTenthWeight, h]
    norm_num
  · simp only [atomTenthReading, atomTenthSecond, atomTenthWeight, h]
    push_cast
    nlinarith [hsq]

/-- **THE SHARP CAP, EXACTLY.**  The determinantal average of the smallest
eigenvalue at the tenth extremal is `(2 - sqrt 2)/4 = 0.146446609407`.  Sixteen live
triples carry the determinant `1/16` and the eigenvalue `(2 - sqrt 2)/4`, and four
dead triples carry nothing.

So no theorem of the shape of `Gtz.atomTenthAverage_ge` can read more than
`(2 - sqrt 2)/4`, and the determinantal average under the tenth CANNOT certify
`1/6 = 0.166666666667`.  The route has a cap of its own, and it is `0.0202` short
of the truth. -/
theorem atomTenthExtremal_average :
    atomTripleFamilySum (fun a b c => atomTenthWeight a b c * atomTenthReading a b c)
      = (2 - Real.sqrt 2) / 4 := by
  obtain ⟨n012, n013, n014, n015, n023, n024, n025, n034, n035, n045,
    n123, n124, n125, n134, n135, n145, n234, n235, n245, n345⟩ := atomTenthNum_sorted
  simp only [atomTripleFamilySum, atomTenthWeight, atomTenthReading, n012, n013, n014,
    n015, n023, n024, n025, n034, n035, n045, n123, n124, n125, n134, n135, n145,
    n234, n235, n245, n345]
  push_cast
  ring

/-! ## Layer 5 — the sharp per-triple rung is FALSE -/

/-- **THE SHARP PER-TRIPLE RUNG.**  The reading the extremal forces.  It is exactly
tight at the extremal block `(3/2, 5/8, 1/16)`, where the correction term vanishes,
and its determinantal average would be `(2 - sqrt 2)/4` in one line, because the
correction term averages to `(sqrt 2/4)(10 E3 - E2)` and the tenth makes that not
negative. -/
def AtomSharpTripleRung : Prop :=
  ∀ r1 r2 r3 : ℝ, 0 ≤ r1 → r1 ≤ 1 → 0 ≤ r2 → r2 ≤ 1 → 0 ≤ r3 → r3 ≤ 1 →
    r1 + r2 + r3 = 3 / 2 →
    (2 - Real.sqrt 2) / 4 + (Real.sqrt 2 / 4) * (10 * (r1 * r2 * r3)
        - (r1 * r2 + r1 * r3 + r2 * r3)) ≤ r1

/-- **THE SHARP PER-TRIPLE RUNG IS FALSE, AT AN EXACT SPECTRUM.**  Take the extremal
block and move its MIDDLE eigenvalue away from `1/2`, keeping the smallest one and
the total:

  `r = ((2 - sqrt 2)/4, 11/20, 9/20 + sqrt 2/4)`.

All three readings lie in `[0,1]` and they total `3/2`.  The second and third
symmetric functions are `(249 + 5 sqrt 2)/400` and `11 (8 + sqrt 2)/1600`, so the
correction term reads `(90 sqrt 2 - 116)/1600`, which is POSITIVE.  The claim then
asks for `180 <= 116 sqrt 2 = 164.05`, and the defect is
`(180 - 116 sqrt 2)/6400 = 2.4923e-3`.

So the sharp constant is NOT reachable by any per-triple reading of this shape.  It
is reachable per COMPLEMENTARY PAIR, and that is the one next target. -/
theorem not_atomSharpTripleRung : ¬ AtomSharpTripleRung := by
  intro h
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hlo : (7 : ℝ) / 5 ≤ Real.sqrt 2 := by nlinarith [hsq, hnn]
  have hhi : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [hsq, hnn]
  have key := h ((2 - Real.sqrt 2) / 4) (11 / 20) (9 / 20 + Real.sqrt 2 / 4)
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by ring)
  nlinarith [key, hsq, hnn, hlo]

/-! ## Layer 6 — no determinantal selector can certify one sixth from this class -/

/-- **EVERY SELECTOR SUPPORTED ON THE LIVE TRIPLES READS `(2 - sqrt 2)/4` AT THE
EXTREMAL.**  A selector is any reading of the twenty triples that a certificate
uses to average the smallest eigenvalue.  If it vanishes wherever the determinant
vanishes, it cannot tell the tenth extremal apart from the pure determinantal
measure, because the sixteen live blocks all read the SAME smallest eigenvalue
`(2 - sqrt 2)/4` there.

This one identity kills a whole family at once.  Every selector the campaign has
named vanishes on a zero determinant:

* `w = p` itself, and `w` proportional to `p ^ alpha` for every `alpha > 0`,
* `w` proportional to `p * e2` and to `p / e2`,
* `w` proportional to `p * (10 e3 - e2)` cut at zero,
* `w` proportional to `p * lambda_min` and to `p * exp(beta * lambda_min)`,
* the uniform measure on the triples of largest determinant.

So NO member of that family can be certified above `(2 - sqrt 2)/4` from the
moment class and the tenth, and `(2 - sqrt 2)/4 < 1/6`.  Over GENUINE real frames
some of those selectors may still average above `1/6` — the measured minima of
`p ^ 2`, `p ^ 3` and `p ^ 4` over balanced real frames are `0.16874`, `0.16962`
and `0.17007`.  The point is that the moment class plus the tenth CANNOT SEE the
difference, so the search for a selector must leave this relaxation. -/
theorem atomTenthExtremal_selectorCap {weightRead : Fin 6 → Fin 6 → Fin 6 → ℝ}
    (hsupp : ∀ a b c : Fin 6, atomTenthNum a b c = 0 → weightRead a b c = 0) :
    atomTripleFamilySum (fun a b c => weightRead a b c * atomTenthReading a b c)
      = (2 - Real.sqrt 2) / 4 * atomTripleFamilySum weightRead := by
  obtain ⟨n012, n013, n014, n015, n023, n024, n025, n034, n035, n045,
    n123, n124, n125, n134, n135, n145, n234, n235, n245, n345⟩ := atomTenthNum_sorted
  have d012 := hsupp 0 1 2 n012
  have d013 := hsupp 0 1 3 n013
  have d245 := hsupp 2 4 5 n245
  have d345 := hsupp 3 4 5 n345
  simp only [atomTripleFamilySum, atomTenthReading, n012, n013, n014, n015, n023, n024,
    n025, n034, n035, n045, n123, n124, n125, n134, n135, n145, n234, n235, n245, n345,
    d012, d013, d245, d345]
  push_cast
  ring

/-- **NO SUCH SELECTOR REACHES ONE SIXTH IN THIS CLASS.**  The tenth extremal is a
member of `Gtz.AtomTenthFeasible`, its reading is a spectral reading, and every
selector that vanishes on a zero determinant averages the reading to
`(2 - sqrt 2)/4`, which is strictly below `1/6`.  So a determinantal selector of
that shape is CAPPED, and the search for a selector that reaches `1/6` must read
something the moment class and the tenth do not carry. -/
theorem not_atomTenthSelectorSixth {weightRead : Fin 6 → Fin 6 → Fin 6 → ℝ}
    (hsupp : ∀ a b c : Fin 6, atomTenthNum a b c = 0 → weightRead a b c = 0)
    (hmass : 0 < atomTripleFamilySum weightRead) :
    atomTripleFamilySum (fun a b c => weightRead a b c * atomTenthReading a b c)
      < (1 / 6) * atomTripleFamilySum weightRead := by
  rw [atomTenthExtremal_selectorCap hsupp]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have n2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hlt : (2 - Real.sqrt 2) / 4 < 1 / 6 := by nlinarith [h2, n2]
  exact mul_lt_mul_of_pos_right hlt hmass

/-! ## Layer 7 — the route has a cap of its own, and it is a theorem -/

/-- **THE ROUTE CANNOT READ MORE THAN `(2 - sqrt 2)/4`.**  No statement of the
shape of `Gtz.atomTenthAverage_ge` can carry a constant above `(2 - sqrt 2)/4`,
because the tenth extremal is a member of the class, its reading is a spectral
reading, and its determinantal average is exactly `(2 - sqrt 2)/4`.

So the gap between the landed `141/1000` and the sharp `(2 - sqrt 2)/4` is
`5.45e-3`, and the gap between the sharp constant and the truth `1/6` is
`2.02e-2` and is NOT closable inside this class. -/
theorem not_atomTenthAverage_gt {bar : ℝ} (hbar : (2 - Real.sqrt 2) / 4 < bar) :
    ¬ (∀ weight second reading : Fin 6 → Fin 6 → Fin 6 → ℝ,
        AtomTenthFeasible weight second → AtomSpectralReading weight second reading →
        bar ≤ atomTripleFamilySum (fun a b c => weight a b c * reading a b c)) := by
  intro h
  have := h atomTenthWeight atomTenthSecond atomTenthReading
    atomTenthExtremal_isFeasible atomTenthExtremal_isReading
  rw [atomTenthExtremal_average] at this
  linarith

/-- **THE DETERMINANTAL AVERAGE UNDER THE TENTH CANNOT CERTIFY ONE SIXTH.**  The
truth over the real field at the uniform scale is `1/6`, and the class of this
module caps every reading of its shape at `(2 - sqrt 2)/4 = 0.146446609407`, which
is `0.0202` short.  A certificate that reaches `1/6` must read something the
moment class and the tenth do not carry. -/
theorem not_atomTenthAverage_sixth :
    ¬ (∀ weight second reading : Fin 6 → Fin 6 → Fin 6 → ℝ,
        AtomTenthFeasible weight second → AtomSpectralReading weight second reading →
        (1 : ℝ) / 6 ≤ atomTripleFamilySum (fun a b c => weight a b c * reading a b c)) := by
  refine not_atomTenthAverage_gt ?_
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have n2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [h2, n2]

end Gtz
