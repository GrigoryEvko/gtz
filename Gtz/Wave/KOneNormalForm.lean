import Gtz.Wave.KOneBracketLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# The normal form of an anchored pair, and the general bracket law

The stratum's measurement came back EMPTY at both sizes, so the target is
emptiness with a certificate.  This module supplies the exact arena that
certificate has to live in, at GENERAL size `m`, since the kill is not
size-bound.

**THE NORMAL FORM.**  An anchored pair — `S_{yz} w = w` with `w` a unit
vector — is completely determined by two numbers: the wedge
`A = l_y + l_z - 1` and the reading split `beta_y^2 + beta_z^2 = 1`.  The
three Gram entries are then forced:

  `l_y = beta_y^2 + A·beta_z^2` ,   `l_z = beta_z^2 + A·beta_y^2` ,
  `<g_y, g_z> = (1 - A)·beta_y·beta_z` .

The first is the transverse split of `Gtz.pairAnchor_transverse_split`; the
third is `Gtz.pairAnchor_pairing_value`, landed here with a three-term
certificate.  Every scalar of the live pair is a polynomial in `(A, beta)`,
so the sixteen avoiding refusals can be written in those two coordinates.

**THE GENERAL BRACKET LAW** (`Gtz.pairAnchor_bracket_general`).  Dropping the
orthogonality hypothesis of `Gtz.pairAnchor_bracket_master` entirely: for
EVERY vector `g`,

  `[g, g_y, g_z]^2 = A·l_g - <g,g_y>^2 - <g,g_z>^2 - (A - 1)·(g.w)^2` .

The perpendicular case is the vanishing of the last term.  This is exactly
the shape the campaign demands of a closing law — the term that carries the
null reading is the SAME `(A-1)(g.w)^2` that
`Gtz.pairAnchor_det_update` puts in the gap determinant, so bracket and
determinant degenerate together, on the same factor, at the same locus.

**THE SHARP WEIGHT CAP** (`Gtz.kOne_sharp_weight_cap`).  Parseval read at the
transverse probe of the live pair gives

  `A·(t_y·beta_z^2 + t_z·beta_y^2) <= 1` ,

which strictly sharpens `Gtz.kOne_pair_weight_cap_of_null`: the reading
weights `beta_z^2, beta_y^2` sum to one, so the left side dominates
`min(t_y,t_z)·A`.  This is the down-pushing half of the stratum's collision,
in its sharpest available form; the up-pushing half is the strict floor
`A > 1` of `Gtz.kOne_two_lt_leverageSum`.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The pairing value: the pair's normal form closes -/

/-- **THE ANCHORED PAIRING VALUE.**  At an anchored pair the inner product of
the two atoms is forced by the leverages and the readings:

  `<g_y, g_z> = (2 - l_y - l_z)·beta_y·beta_z = (1 - A)·beta_y·beta_z` .

With the transverse split this closes the normal form: every Gram entry of
an anchored pair is a polynomial in the wedge and the reading split. -/
theorem pairAnchor_pairing_value {gy gz w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1) :
    gy ⬝ᵥ gz
      = (2 - leverageOf gy - leverageOf gz) * ((gy ⬝ᵥ w) * (gz ⬝ᵥ w)) := by
  have h1 := pairAnchor_relation_left hanchor
  have h2 := pairAnchor_relation_right hanchor
  have h3 := pairAnchor_readings_sq_sum hanchor hunit
  linear_combination (gz ⬝ᵥ w) * h1 + (gy ⬝ᵥ w) * h2 - (gy ⬝ᵥ gz) * h3

/-- The transverse reading of the second live atom against the first live
atom's transverse probe: `<g_z, g_y> - beta_y·beta_z = -A·beta_y·beta_z`. -/
theorem pairAnchor_cross_transverse {gy gz w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1) :
    (gy ⬝ᵥ gz) - (gy ⬝ᵥ w) * (gz ⬝ᵥ w)
      = -((leverageOf gy + leverageOf gz - 1) * ((gy ⬝ᵥ w) * (gz ⬝ᵥ w))) := by
  have h := pairAnchor_pairing_value hanchor hunit
  linear_combination h

/-! ## 2. The general bracket law -/

/-- **THE GENERAL BRACKET LAW.**  At an anchored pair, for EVERY vector `g`
— no orthogonality to the null direction assumed —

  `[g, g_y, g_z]^2 = (l_y + l_z - 1)·l_g - <g,g_y>^2 - <g,g_z>^2
                       - (l_y + l_z - 2)·(g.w)^2` .

`Gtz.pairAnchor_bracket_master` is the special case `g.w = 0`.  The null
reading enters through the SAME factor `(A-1)(g.w)^2` that carries the gap
determinant in `Gtz.pairAnchor_det_update`. -/
theorem pairAnchor_bracket_general {gy gz g w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1) :
    tripleBracket g gy gz ^ 2
      = (leverageOf gy + leverageOf gz - 1) * leverageOf g
        - (g ⬝ᵥ gy) ^ 2 - (g ⬝ᵥ gz) ^ 2
        - (leverageOf gy + leverageOf gz - 2) * (g ⬝ᵥ w) ^ 2 := by
  have h1 := pairAnchor_relation_left hanchor
  have h2 := pairAnchor_relation_right hanchor
  have h3 := pairAnchor_readings_sq_sum hanchor hunit
  have hgw : g ⬝ᵥ w
      = (gy ⬝ᵥ w) * (g ⬝ᵥ gy) + (gz ⬝ᵥ w) * (g ⬝ᵥ gz) := by
    have h : g ⬝ᵥ ((gy ⬝ᵥ w) • gy + (gz ⬝ᵥ w) • gz) = g ⬝ᵥ w := by
      rw [pairAnchor_resolve hanchor]
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul] at h
    linear_combination -h
  rw [tripleBracket_sq_gram, hgw]
  simp only [dotProduct_comm gz g]
  linear_combination
    ((g ⬝ᵥ gy) ^ 2 * (gy ⬝ᵥ w) + 2 * (g ⬝ᵥ gy) * (g ⬝ᵥ gz) * (gz ⬝ᵥ w)
        - (g ⬝ᵥ gz) ^ 2 * (gy ⬝ᵥ w)
        + (gy ⬝ᵥ w) * leverageOf g * leverageOf gz
        - (gy ⬝ᵥ w) * leverageOf g
        - (gz ⬝ᵥ w) * leverageOf g * (gy ⬝ᵥ gz)) * h1
    + (-((g ⬝ᵥ gy) ^ 2 * (gz ⬝ᵥ w)) + 2 * (g ⬝ᵥ gy) * (g ⬝ᵥ gz) * (gy ⬝ᵥ w)
        + (g ⬝ᵥ gz) ^ 2 * (gz ⬝ᵥ w)
        - (gy ⬝ᵥ w) * leverageOf g * (gy ⬝ᵥ gz)
        + (gz ⬝ᵥ w) * leverageOf g * leverageOf gy
        - (gz ⬝ᵥ w) * leverageOf g) * h2
    + ((g ⬝ᵥ gy) ^ 2 * leverageOf gz - (g ⬝ᵥ gy) ^ 2
        - 2 * (g ⬝ᵥ gy) * (g ⬝ᵥ gz) * (gy ⬝ᵥ gz)
        + (g ⬝ᵥ gz) ^ 2 * leverageOf gy - (g ⬝ᵥ gz) ^ 2
        - leverageOf g * leverageOf gy * leverageOf gz
        + leverageOf g * leverageOf gy + leverageOf g * leverageOf gz
        + leverageOf g * (gy ⬝ᵥ gz) ^ 2 - leverageOf g) * h3

/-! ## 3. The sharp weight cap -/

/-- **THE SHARP WEIGHT CAP.**  Parseval read at the transverse probe of the
live pair:

  `(l_y + l_z - 1)·(t_y·beta_z^2 + t_z·beta_y^2) <= 1` .

Since `beta_y^2 + beta_z^2 = 1`, the bracket on the left dominates
`min(t_y,t_z)`, so this strictly sharpens
`Gtz.kOne_pair_weight_cap_of_null`.  It is the down-pushing half of the
stratum's collision, against the strict floor `l_y + l_z > 2`. -/
theorem kOne_sharp_weight_cap {m : ℕ} (D : WeightedDesign m 3)
    {y z : Fin m} (hyz : y ≠ z)
    {w : Fin 3 → ℝ}
    (hanchor : (atomMatrix (D.atom y) + atomMatrix (D.atom z)) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1)
    (hT : 0 < leverageOf (D.atom y) - (D.atom y ⬝ᵥ w) ^ 2) :
    (leverageOf (D.atom y) + leverageOf (D.atom z) - 1)
        * (D.weight y * (D.atom z ⬝ᵥ w) ^ 2
          + D.weight z * (D.atom y ⬝ᵥ w) ^ 2) ≤ 1 := by
  classical
  set A : ℝ := leverageOf (D.atom y) + leverageOf (D.atom z) - 1 with hA
  set by' : ℝ := D.atom y ⬝ᵥ w with hby
  set bz' : ℝ := D.atom z ⬝ᵥ w with hbz
  set probe : Fin 3 → ℝ := D.atom y - by' • w with hprobe
  have hsplit := pairAnchor_transverse_split hanchor hunit
  have hTval : leverageOf (D.atom y) - by' ^ 2 = A * bz' ^ 2 := hsplit
  -- the three readings of the probe
  have hyp : D.atom y ⬝ᵥ probe = A * bz' ^ 2 := by
    rw [hprobe, dotProduct_sub, dotProduct_smul, smul_eq_mul, ← hTval,
      leverageOf_eq_dotProduct]
    ring
  have hzp : D.atom z ⬝ᵥ probe = -(A * (by' * bz')) := by
    have hcross := pairAnchor_cross_transverse hanchor hunit
    rw [hprobe, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      dotProduct_comm (D.atom z) (D.atom y)]
    linear_combination hcross
  have hpp : probe ⬝ᵥ probe = A * bz' ^ 2 := by
    rw [hprobe]
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hunit, mul_one]
    rw [dotProduct_comm w (D.atom y), ← hTval, leverageOf_eq_dotProduct]
    ring
  -- Parseval at the probe, restricted to the live pair
  have hpar := parseval_probe_form D probe
  rw [hpp] at hpar
  have hpair : D.weight y * (D.atom y ⬝ᵥ probe) ^ 2
      + D.weight z * (D.atom z ⬝ᵥ probe) ^ 2 ≤ A * bz' ^ 2 := by
    rw [← hpar]
    have hstep : ∑ c ∈ ({y, z} : Finset (Fin m)),
          D.weight c * (D.atom c ⬝ᵥ probe) ^ 2
        ≤ ∑ c, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun c _ _ => mul_nonneg (D.weight_pos c).le (sq_nonneg _))
    rwa [Finset.sum_insert (by simp [hyz]), Finset.sum_singleton] at hstep
  rw [hyp, hzp] at hpair
  -- divide by the strictly positive transverse mass
  have hTpos : 0 < A * bz' ^ 2 := by rw [← hTval]; exact hT
  nlinarith [hpair, hTpos]

/-- The sharp cap at a `K1` dominator, with the transverse positivity
supplied by the stratum. -/
theorem kOne_sharp_weight_cap_of_null (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin 6)) w)
    (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0)
    (hbz : D.atom z ⬝ᵥ w ≠ 0) :
    (leverageOf (D.atom y) + leverageOf (D.atom z) - 1)
        * (D.weight y * (D.atom z ⬝ᵥ w) ^ 2
          + D.weight z * (D.atom y ⬝ᵥ w) ^ 2) ≤ 1 :=
  kOne_sharp_weight_cap D hyz
    (kOne_pairAnchor D hxy hxz hyz hdominates hline.2.1 hax) hunit
    (kOne_transverse_pos D hxy hxz hyz hdominates hline hunit hax hbz)

end Gtz
