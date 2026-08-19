import Gtz.Wave.CornerBracketPlucker
import Gtz.Design.DepthCapAxisParseval
import Gtz.Reduction.PolarPlaneTurn
import Gtz.Quantitative.PhaseFreeNoGo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The sign word of a corank-two corner

The bracket bridge (`Gtz.corner_bracket_bridge`) computes each informative
bracket of a corner from two-inside brackets, and the brief of this round read
its right side as a free sign system.  That reading is wrong: a product of an
EVEN number of brackets is a mixed Gram minor, so every such sign is already a
polynomial in the Gram data.  The realness of a corner does not sit in free
bits.  It sits in one place: over the reals the SQUARE of a mixed minor equals
the product of the two principal minors, while over the complex numbers only an
inequality survives.  This module makes that spendable.

## The transport

Parseval, polarized at two cross axes with a common base atom, gives

  `∑ a, t_a · [b f a] · [b s a]  =  |g_b|² ⟨g_f, g_s⟩ − ⟨g_b, g_f⟩ ⟨g_b, g_s⟩`

(`Gtz.sum_weight_bracket_transport`).  At a corank-two corner the right side
collapses to the single pairing `⟨g_f, g_s⟩`, because the rank-one gap forces
`excess_b · ⟨g_f, g_s⟩ = ⟨g_b, g_f⟩ ⟨g_b, g_s⟩` on the dominator, and the three
inside terms of the sum vanish on repeated slots.  So the co-weighted mixed
minors of one base against the OUTSIDE atoms total the opposite inside pairing,
exactly (`Gtz.corner_compl_bracket_transport`).

## The coupling and the dichotomy

At one outside atom the three base products multiply to
`−([x y d][x z d][y z d])²` (`Gtz.atomBracket_baseProduct_cycle`): an odd number
of the three visible mixed minors is negative, unless the atom is coplanar with
an inside pair.  The corner also forces the three inside pairings to a coherent
sign (`Gtz.corner_inside_tripleProduct_nonneg`).  Squeezing the three transports
against the coupling: if NO base carries an opposite-sign pair of outside mixed
minors, then EVERY outside atom is coplanar with an inside pair
(`Gtz.corner_signWord_dichotomy`).  Contrapositively, one bracket-generic
outside atom hands some base an opposite-sign pair
(`Gtz.corner_exists_oppositePair`), and on such a pair the bridge is a FLOOR:

  `4 |[x y d][x z d]| · |[x y d'][x z d']|  ≤  (1 + lam) [x d d']²`

(`Gtz.corner_oppositePair_bracket_floor`), so the informative triple
`{x, d, d'}` has a strictly positive squared bracket with an explicit lower
bound (`Gtz.corner_informative_bracket_floor`).

## Where the field acts

Every hypothesis above is a Gram polynomial, and the complex corner-tie witness
on record satisfies the transports and the sign hypotheses.  The floor is the
real step: over the reals `([x y d][x z d])² = det G_{xyd} · det G_{xzd}`, the
Cauchy–Schwarz EQUALITY case, while over the complex numbers the visible mixed
minor obeys only `(Re ⟨·,·⟩)² ≤ det · det`.  Read with principal minors on the
right side, the floor FAILS at the complex witness: at base `2` the outside
pairs `{3,4}` and `{3,5}` satisfy the opposite-sign hypothesis and violate the
conclusion (`20.16 < 52.38` and `2.53 < 8.16`), while every real corner obeys
it at every base.  The existential consequence alone does not separate — the
witness satisfies it through its other two bases — so the residual of this
round is the floor at EVERY base, not at one.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. Brackets with a repeated slot vanish -/

/-- The bracket vanishes when the right slot repeats the left slot. -/
theorem tripleBracket_eq_zero_of_left_eq_right (leftVec midVec : Fin 3 → ℝ) :
    tripleBracket leftVec midVec leftVec = 0 := by
  simp only [tripleBracket_eq]; ring

/-- The bracket vanishes when the right slot repeats the middle slot. -/
theorem tripleBracket_eq_zero_of_mid_eq_right (leftVec midVec : Fin 3 → ℝ) :
    tripleBracket leftVec midVec midVec = 0 := by
  simp only [tripleBracket_eq]; ring

/-- The atom bracket vanishes when the right label repeats the left label. -/
theorem atomBracket_right_eq_left (D : WeightedDesign m 3) (leftLabel midLabel : Fin m) :
    atomBracket D leftLabel midLabel leftLabel = 0 := by
  simp only [atomBracket]
  exact tripleBracket_eq_zero_of_left_eq_right _ _

/-- The atom bracket vanishes when the right label repeats the middle label. -/
theorem atomBracket_right_eq_mid (D : WeightedDesign m 3) (leftLabel midLabel : Fin m) :
    atomBracket D leftLabel midLabel midLabel = 0 := by
  simp only [atomBracket]
  exact tripleBracket_eq_zero_of_mid_eq_right _ _

/-! ## 2. The polarized bracket transport -/

/-- **THE POLARIZED BRACKET TRANSPORT.**  Parseval read at the two cross axes of
a common base against two companions: the weighted products of anchored brackets
total the base-conjugated pairing.  The diagonal case `first = second` is the
landed `Gtz.sum_weight_tripleBracket_sq_pair`; the polarized case is the one the
sign system needs, because it pins the SIGNS of the mixed minors and not only
their masses. -/
theorem sum_weight_bracket_transport (D : WeightedDesign m 3)
    (base first second : Fin m) :
    ∑ a, D.weight a * (atomBracket D base first a * atomBracket D base second a)
      = leverageOf (D.atom base) * atomPairing D first second
        - atomPairing D base first * atomPairing D base second := by
  have hpar := dotProduct_eq_sum_weight_mul_pair D
    (crossAxis D base first) (crossAxis D base second)
  have hsum : ∑ a, D.weight a
      * ((D.atom a ⬝ᵥ crossAxis D base first) * (D.atom a ⬝ᵥ crossAxis D base second))
      = ∑ a, D.weight a * (atomBracket D base first a * atomBracket D base second a) :=
    Finset.sum_congr rfl fun a _ => by
      rw [atom_dotProduct_crossAxis, atom_dotProduct_crossAxis]
  rw [hsum] at hpar
  rw [← hpar, crossAxis, crossAxis, bracketNormal_lagrange, leverageOf_eq_dotProduct]
  simp only [atomPairing]

/-! ## 3. The corner collapse of the transport -/

/-- **The rank-one gap ties the excess to the pairings.**  On the dominator the
excess of one inside atom against the opposite pairing equals the product of its
two own pairings.  This is the scalar that collapses the transport at a corner. -/
theorem corner_heavyExcess_mul_pairing (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    heavyExcess D x * atomPairing D y z = atomPairing D x y * atomPairing D x z := by
  have hpos : (0 : ℝ) < 1 + lam := by linarith
  have hex := corner_heavyExcess_axis D C hcard hlam hunit hgap hx
  have hyz' := corner_atomPairing_axis D C hcard hlam hunit hgap hy hz hyz
  have hxy' := corner_atomPairing_axis D C hcard hlam hunit hgap hx hy hxy
  have hxz' := corner_atomPairing_axis D C hcard hlam hunit hgap hx hz hxz
  have hleft : ((1 + lam) * heavyExcess D x) * ((1 + lam) * atomPairing D y z)
      = (lam * (D.atom x ⬝ᵥ u) ^ 2)
        * (lam * ((D.atom y ⬝ᵥ u) * (D.atom z ⬝ᵥ u))) := by rw [hex, hyz']
  have hright : ((1 + lam) * atomPairing D x y) * ((1 + lam) * atomPairing D x z)
      = (lam * ((D.atom x ⬝ᵥ u) * (D.atom y ⬝ᵥ u)))
        * (lam * ((D.atom x ⬝ᵥ u) * (D.atom z ⬝ᵥ u))) := by rw [hxy', hxz']
  have hmatch : (lam * (D.atom x ⬝ᵥ u) ^ 2)
        * (lam * ((D.atom y ⬝ᵥ u) * (D.atom z ⬝ᵥ u)))
      = (lam * ((D.atom x ⬝ᵥ u) * (D.atom y ⬝ᵥ u)))
        * (lam * ((D.atom x ⬝ᵥ u) * (D.atom z ⬝ᵥ u))) := by ring
  have hsq : (1 + lam) ^ 2 * (heavyExcess D x * atomPairing D y z)
      = (1 + lam) ^ 2 * (atomPairing D x y * atomPairing D x z) := by
    linear_combination hleft - hright + hmatch
  exact mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hpos)) hsq

/-- **THE CORNER TRANSPORT.**  At a corank-two corner the co-weighted mixed
minors of one inside base against the OUTSIDE atoms total the opposite inside
pairing, exactly.  The three inside terms of the full transport vanish on
repeated slots, and the rank-one gap absorbs the excess.  This is the mass
equation of the sign word: the visible signs of the outside mixed minors must
assemble the sign of the pairing. -/
theorem corner_compl_bracket_transport (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hC : C = ({x, y, z} : Finset (Fin m)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∑ d ∈ Cᶜ, D.weight d * (atomBracket D x y d * atomBracket D x z d)
      = atomPairing D y z := by
  have hcard : C.card = 3 := by rw [hC]; exact card_triple_eq hxy hxz hyz
  have hx : x ∈ C := by rw [hC]; simp
  have hy : y ∈ C := by rw [hC]; simp
  have hz : z ∈ C := by rw [hC]; simp
  have htotal := sum_weight_bracket_transport D x y z
  have hins := corner_heavyExcess_mul_pairing D C hcard hlam hunit hgap hx hy hz hxy hxz hyz
  have hins' : (leverageOf (D.atom x) - 1) * atomPairing D y z
      = atomPairing D x y * atomPairing D x z := by
    simpa only [heavyExcess] using hins
  have hzero : ∑ a ∈ C, D.weight a * (atomBracket D x y a * atomBracket D x z a) = 0 := by
    rw [hC, sum_triple_eq hxy hxz hyz]
    rw [atomBracket_right_eq_left, atomBracket_right_eq_mid, atomBracket_right_eq_mid]
    ring
  have hsplit := Finset.sum_add_sum_compl C
    (fun a => D.weight a * (atomBracket D x y a * atomBracket D x z a))
  rw [hzero, zero_add, htotal] at hsplit
  rw [hsplit]
  linear_combination hins'

/-! ## 4. The per-atom sign coupling -/

/-- **THE SIGN COUPLING.**  At one probe atom the three base products of
anchored brackets multiply to minus a square: an odd number of the three mixed
minors is negative, unless the probe is coplanar with a base pair.  Pure
bracket antisymmetry, no design hypothesis. -/
theorem atomBracket_baseProduct_cycle (D : WeightedDesign m 3) (x y z a : Fin m) :
    (atomBracket D x y a * atomBracket D x z a)
        * (atomBracket D y x a * atomBracket D y z a)
        * (atomBracket D z x a * atomBracket D z y a)
      = -(atomBracket D x y a * atomBracket D x z a * atomBracket D y z a) ^ 2 := by
  simp only [atomBracket]
  rw [tripleBracket_swapLeft (D.atom y) (D.atom x) (D.atom a),
    tripleBracket_swapLeft (D.atom z) (D.atom x) (D.atom a),
    tripleBracket_swapLeft (D.atom z) (D.atom y) (D.atom a)]
  ring

/-- The three base products at one probe atom are never all of one strict sign. -/
theorem atomBracket_baseProduct_cycle_nonpos (D : WeightedDesign m 3) (x y z a : Fin m) :
    (atomBracket D x y a * atomBracket D x z a)
        * (atomBracket D y x a * atomBracket D y z a)
        * (atomBracket D z x a * atomBracket D z y a) ≤ 0 := by
  rw [atomBracket_baseProduct_cycle]
  exact neg_nonpos.mpr (sq_nonneg _)

/-! ## 5. A positive-weight sum forces its sign onto every term -/

/-- **The half-line lemma.**  A positively weighted sum of pairwise-coherent
values forces the sign of its total onto every term: if no two values disagree
in sign, each value agrees with the total. -/
theorem sum_sign_forced_of_pairwise_nonneg {ι : Type*} {s : Finset ι} {w v : ι → ℝ}
    (hw : ∀ i ∈ s, 0 < w i)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ v i * v j)
    {total : ℝ} (hsum : ∑ i ∈ s, w i * v i = total) (htotal : total ≠ 0) :
    ∀ i ∈ s, 0 ≤ total * v i := by
  intro i0 hi0
  by_contra hneg
  push Not at hneg
  have hv0 : v i0 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hneg
    exact lt_irrefl 0 hneg
  have hall : ∀ j ∈ s, total * (w j * v j) ≤ 0 := by
    intro j hj
    have hpair0 := hpair j hj i0 hi0
    have hkey : (total * v j) * (v i0) ^ 2 ≤ 0 * (v i0) ^ 2 := by
      have hprod : (total * v j) * (v i0) ^ 2 = (total * v i0) * (v j * v i0) := by ring
      rw [zero_mul, hprod]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hneg) hpair0
    have hsq : (0 : ℝ) < (v i0) ^ 2 := by positivity
    have hjle : total * v j ≤ 0 := le_of_mul_le_mul_right hkey hsq
    calc total * (w j * v j) = w j * (total * v j) := by ring
      _ ≤ w j * 0 := mul_le_mul_of_nonneg_left hjle (hw j hj).le
      _ = 0 := mul_zero _
  have hsq : total ^ 2 ≤ 0 := by
    calc total ^ 2 = total * total := sq total
      _ = total * ∑ i ∈ s, w i * v i := by rw [hsum]
      _ = ∑ i ∈ s, total * (w i * v i) := Finset.mul_sum _ _ _
      _ ≤ 0 := Finset.sum_nonpos hall
  exact htotal (sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg total)))

/-! ## 6. The dichotomy -/

/-- **THE SIGN-WORD DICHOTOMY.**  At a corank-two corner with nondegenerate
inside pairings, if no inside base carries an opposite-sign pair of outside
mixed minors, then every outside atom is coplanar with an inside pair.  The
three corner transports force each base's minors onto the sign of its pairing,
the coherent triangle multiplies the three targets to a positive number, and
the per-atom coupling multiplies the three minors to minus a square: the
squeeze kills the square. -/
theorem corner_signWord_dichotomy (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hC : C = ({x, y, z} : Finset (Fin m)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hPyz : atomPairing D y z ≠ 0) (hPxz : atomPairing D x z ≠ 0)
    (hPxy : atomPairing D x y ≠ 0)
    (hbaseX : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D x y d * atomBracket D x z d)
        * (atomBracket D x y d' * atomBracket D x z d'))
    (hbaseY : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D y x d * atomBracket D y z d)
        * (atomBracket D y x d' * atomBracket D y z d'))
    (hbaseZ : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D z x d * atomBracket D z y d)
        * (atomBracket D z x d' * atomBracket D z y d'))
    {d : Fin m} (hd : d ∈ Cᶜ) :
    atomBracket D x y d * atomBracket D x z d * atomBracket D y z d = 0 := by
  have hcard : C.card = 3 := by rw [hC]; exact card_triple_eq hxy hxz hyz
  have hx : x ∈ C := by rw [hC]; simp
  have hy : y ∈ C := by rw [hC]; simp
  have hz : z ∈ C := by rw [hC]; simp
  have hCy : C = ({y, x, z} : Finset (Fin m)) := by
    rw [hC]; ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hCz : C = ({z, x, y} : Finset (Fin m)) := by
    rw [hC]; ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have htX := corner_compl_bracket_transport D C hlam hunit hgap hC hxy hxz hyz
  have htY := corner_compl_bracket_transport D C hlam hunit hgap hCy
    (Ne.symm hxy) hyz hxz
  have htZ := corner_compl_bracket_transport D C hlam hunit hgap hCz
    (Ne.symm hxz) (Ne.symm hyz) hxy
  have hw : ∀ a ∈ Cᶜ, 0 < D.weight a := fun a _ => D.weight_pos a
  have hsX := sum_sign_forced_of_pairwise_nonneg hw hbaseX htX hPyz d hd
  have hsY := sum_sign_forced_of_pairwise_nonneg hw hbaseY htY hPxz d hd
  have hsZ := sum_sign_forced_of_pairwise_nonneg hw hbaseZ htZ hPxy d hd
  have hP := corner_inside_tripleProduct_nonneg D C hcard hlam hunit hgap
    hx hy hz hxy hxz hyz
  have hPne : atomPairing D x y * atomPairing D x z * atomPairing D y z ≠ 0 :=
    mul_ne_zero (mul_ne_zero hPxy hPxz) hPyz
  have hPpos : 0 < atomPairing D x y * atomPairing D x z * atomPairing D y z :=
    lt_of_le_of_ne hP (Ne.symm hPne)
  have hprod : 0 ≤ (atomPairing D y z * (atomBracket D x y d * atomBracket D x z d))
      * ((atomPairing D x z * (atomBracket D y x d * atomBracket D y z d))
        * (atomPairing D x y * (atomBracket D z x d * atomBracket D z y d))) :=
    mul_nonneg hsX (mul_nonneg hsY hsZ)
  have hre : (atomPairing D y z * (atomBracket D x y d * atomBracket D x z d))
      * ((atomPairing D x z * (atomBracket D y x d * atomBracket D y z d))
        * (atomPairing D x y * (atomBracket D z x d * atomBracket D z y d)))
      = (atomPairing D x y * atomPairing D x z * atomPairing D y z)
        * ((atomBracket D x y d * atomBracket D x z d)
          * (atomBracket D y x d * atomBracket D y z d)
          * (atomBracket D z x d * atomBracket D z y d)) := by ring
  rw [hre, atomBracket_baseProduct_cycle] at hprod
  have hTsq : (atomBracket D x y d * atomBracket D x z d * atomBracket D y z d) ^ 2 ≤ 0 := by
    nlinarith [hprod, hPpos]
  exact sq_eq_zero_iff.mp (le_antisymm hTsq (sq_nonneg _))

/-- **A bracket-generic outside atom forces an opposite-sign pair.**  The
contrapositive of the dichotomy: one outside atom that is coplanar with no
inside pair hands some inside base two outside mixed minors of opposite sign. -/
theorem corner_exists_oppositePair (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hC : C = ({x, y, z} : Finset (Fin m)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hPyz : atomPairing D y z ≠ 0) (hPxz : atomPairing D x z ≠ 0)
    (hPxy : atomPairing D x y ≠ 0)
    {d0 : Fin m} (hd0 : d0 ∈ Cᶜ)
    (hT : atomBracket D x y d0 * atomBracket D x z d0 * atomBracket D y z d0 ≠ 0) :
    (∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ,
        (atomBracket D x y d * atomBracket D x z d)
          * (atomBracket D x y d' * atomBracket D x z d') < 0)
      ∨ (∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ,
        (atomBracket D y x d * atomBracket D y z d)
          * (atomBracket D y x d' * atomBracket D y z d') < 0)
      ∨ (∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ,
        (atomBracket D z x d * atomBracket D z y d)
          * (atomBracket D z x d' * atomBracket D z y d') < 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  exact hT (corner_signWord_dichotomy D C hlam hunit hgap hC hxy hxz hyz
    hPyz hPxz hPxy h1 h2 h3 hd0)

/-! ## 7. The floor on an opposite-sign pair -/

/-- An opposite-sign pair has distinct atoms. -/
theorem corner_oppositePair_ne {D : WeightedDesign m 3} {x y z d d' : Fin m}
    (hsign : (atomBracket D x y d * atomBracket D x z d)
      * (atomBracket D x y d' * atomBracket D x z d') < 0) :
    d ≠ d' := by
  intro h
  subst h
  exact absurd hsign (not_lt.mpr (mul_self_nonneg _))

/-- **THE OPPOSITE-SIGN FLOOR.**  On an opposite-sign pair of outside mixed
minors the bracket bridge turns into a floor: the scaled informative bracket
dominates four times the product of the two minor magnitudes.  Over the reals
each magnitude is the geometric mean of two principal Gram minors — the
Cauchy–Schwarz equality case — and the complex corner-tie witness violates
exactly that reading, at base `2` against both of its opposite-sign pairs. -/
theorem corner_oppositePair_bracket_floor (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    {d d' : Fin m}
    (hsign : (atomBracket D x y d * atomBracket D x z d)
      * (atomBracket D x y d' * atomBracket D x z d') < 0) :
    4 * |atomBracket D x y d * atomBracket D x z d|
        * |atomBracket D x y d' * atomBracket D x z d'|
      ≤ (1 + lam) * atomBracket D x d d' ^ 2 := by
  have hbridge := corner_bracket_bridge D hxy hxz hyz hlam hunit hgap d d'
  have habs : 4 * |atomBracket D x y d * atomBracket D x z d|
      * |atomBracket D x y d' * atomBracket D x z d'|
      = -(4 * ((atomBracket D x y d * atomBracket D x z d)
          * (atomBracket D x y d' * atomBracket D x z d'))) := by
    rw [mul_assoc, ← abs_mul, abs_of_neg hsign]
    ring
  rw [habs, hbridge]
  nlinarith [sq_nonneg (atomBracket D x y d * atomBracket D x z d'
    + atomBracket D x y d' * atomBracket D x z d)]

/-- On an opposite-sign pair the informative bracket is strictly positive in
square: the triple of the base and the two outside atoms spans. -/
theorem corner_oppositePair_bracket_pos (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    {d d' : Fin m}
    (hsign : (atomBracket D x y d * atomBracket D x z d)
      * (atomBracket D x y d' * atomBracket D x z d') < 0) :
    0 < (1 + lam) * atomBracket D x d d' ^ 2 := by
  have hfloor := corner_oppositePair_bracket_floor D hxy hxz hyz hlam hunit hgap hsign
  have hMd : atomBracket D x y d * atomBracket D x z d ≠ 0 := by
    intro h
    rw [h, zero_mul] at hsign
    exact lt_irrefl 0 hsign
  have hMd' : atomBracket D x y d' * atomBracket D x z d' ≠ 0 := by
    intro h
    rw [h, mul_zero] at hsign
    exact lt_irrefl 0 hsign
  have hpos : 0 < 4 * |atomBracket D x y d * atomBracket D x z d|
      * |atomBracket D x y d' * atomBracket D x z d'| :=
    mul_pos (mul_pos four_pos (abs_pos.mpr hMd)) (abs_pos.mpr hMd')
  linarith

/-! ## 8. The headline: a spanning informative triple with a floor -/

/-- **THE INFORMATIVE BRACKET FLOOR.**  A corank-two corner with nondegenerate
inside pairings and one bracket-generic outside atom carries an informative
triple — one inside base, two outside atoms — whose squared bracket is
strictly positive, through the opposite-sign floor at that base.  Every
hypothesis is a Gram polynomial and the floor is where the field is spent. -/
theorem corner_informative_bracket_floor (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hC : C = ({x, y, z} : Finset (Fin m)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hPyz : atomPairing D y z ≠ 0) (hPxz : atomPairing D x z ≠ 0)
    (hPxy : atomPairing D x y ≠ 0)
    {d0 : Fin m} (hd0 : d0 ∈ Cᶜ)
    (hT : atomBracket D x y d0 * atomBracket D x z d0 * atomBracket D y z d0 ≠ 0) :
    ∃ e ∈ C, ∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ, d ≠ d'
      ∧ 0 < (1 + lam) * atomBracket D e d d' ^ 2 := by
  have hx : x ∈ C := by rw [hC]; simp
  have hy : y ∈ C := by rw [hC]; simp
  have hz : z ∈ C := by rw [hC]; simp
  have hgapX : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u := by
    rw [← hC]; exact hgap
  have hgapY : subsetSum D ({y, x, z} : Finset (Fin m)) - 1 = lam • atomMatrix u := by
    rw [show ({y, x, z} : Finset (Fin m)) = ({x, y, z} : Finset (Fin m)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
    exact hgapX
  have hgapZ : subsetSum D ({z, x, y} : Finset (Fin m)) - 1 = lam • atomMatrix u := by
    rw [show ({z, x, y} : Finset (Fin m)) = ({x, y, z} : Finset (Fin m)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
    exact hgapX
  rcases corner_exists_oppositePair D C hlam hunit hgap hC hxy hxz hyz
      hPyz hPxz hPxy hd0 hT with
    ⟨d, hd, d', hd', hsign⟩ | ⟨d, hd, d', hd', hsign⟩ | ⟨d, hd, d', hd', hsign⟩
  · exact ⟨x, hx, d, hd, d', hd', corner_oppositePair_ne hsign,
      corner_oppositePair_bracket_pos D hxy hxz hyz hlam hunit hgapX hsign⟩
  · exact ⟨y, hy, d, hd, d', hd', corner_oppositePair_ne hsign,
      corner_oppositePair_bracket_pos D (Ne.symm hxy) hyz hxz hlam hunit hgapY hsign⟩
  · exact ⟨z, hz, d, hd, d', hd', corner_oppositePair_ne hsign,
      corner_oppositePair_bracket_pos D (Ne.symm hxz) (Ne.symm hyz) hxy hlam hunit
        hgapZ hsign⟩

end Gtz
