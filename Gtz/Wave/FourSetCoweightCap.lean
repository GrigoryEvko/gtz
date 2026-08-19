import Gtz.Wave.FourSetTraceFloor
import Gtz.Wave.CornerBracketPlucker
import Gtz.Wave.CornerGapWindow
import Gtz.Design.TwoFamilyTightFrame
import Gtz.Design.StressFreeNormalizer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The four-set coweight cap, and the death of the zero-pairing corner

`Gtz.fourSet_leverage_ge_one` reads a tie at a strictly dominating four-set:
every member atom reads the inverse gap at least at one.  This module weights
those readings.  For any nonnegative coefficients `w` with
`Σ_{a∈F} w_a • g_a g_aᵀ ⪯ S_F − 1`, the weighted readings are the trace of the
inverse gap against the comparison matrix, and that trace is at most
`tr((S_F−1)⁻¹ (S_F−1)) = 3`.  So the coefficients total at most three
(`Gtz.tie_fourSet_coweight_cap`): a tie caps every Loewner-dominated
coweighting of a strictly dominating four-set.

## The kill

At a corank-two corner whose second and third inside atoms read the gap axis
at zero, the inside frame is rigid: those two atoms are unit and orthogonal to
each other and to the axis, and the first inside atom is the axis itself,
stretched to the full axis mass (`Gtz.corner_axisOrthogonal_inside_frame`).
Take the four-set `F = {x} ∪ Cᶜ` of the axis atom and the three outside atoms.
Parseval makes its gap positive definite outright — with no tie hypothesis
(`Gtz.corner_axisOrthogonal_fourSet_posDef`) — and supplies the comparison

  `c_x • G_x + Σ_d (c_d − o·t_d) • G_d ⪯ S_F − 1`,  `o = t_y/c_y + t_z/c_z`,

where `c_a = 1 − t_a` are the coweights.  The cap forces
`c_x ≤ (t₁+t₂+t₃)(1 + o)`, which unwinds through `Σ t = 1` to a negative total
of positive weights.  So a `(6,3)` tie has no corank-two corner with two inside
atoms orthogonal to the axis (`Gtz.corner_twoAxisZero_absurd`) — planar or
not, primitive or not — and hence none with all three inside pairings zero
(`Gtz.corner_zeroPairings_absurd`).  This empties the stratum of the corner
where the sign-word dichotomy of `Gtz.corner_signWord_dichotomy` is silent
because every pairing hypothesis fails: the stratum that carries
`Gtz.ledgerFoil`.

## Where the size and the field sit

The four-set `{e} ∪ Cᶜ` has four atoms exactly at `6 = 3 + 3`, and the four
refusals the cap consumes are the complement triple and the three one-inside
triples through `e` — informative refusals all.  At `(5,3)` the same set has
three atoms and the mechanism is empty.  Every step transports to Hermitian
atoms, so this stratum is empty over both fields; the complex corner-tie
witness on record carries three nonzero pairings and never enters it.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. Two weights of a six-atom design total less than one -/

/-- Two distinct weights of a six-atom design total strictly less than one:
the four remaining weights are positive. -/
theorem sixWeight_pair_lt_one (D : WeightedDesign 6 3) {a b : Fin 6}
    (hab : a ≠ b) : D.weight a + D.weight b < 1 := by
  classical
  have hbmem : b ∈ (univ : Finset (Fin 6)).erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
  have hsplit : ∑ c, D.weight c
      = D.weight a + (D.weight b + ∑ c ∈ ((univ : Finset (Fin 6)).erase a).erase b,
          D.weight c) := by
    rw [Finset.add_sum_erase _ _ hbmem, Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have hcard : (((univ : Finset (Fin 6)).erase a).erase b).card = 4 := by
    rw [Finset.card_erase_of_mem hbmem, Finset.card_erase_of_mem (Finset.mem_univ a)]
    simp
  have hpos : 0 < ∑ c ∈ ((univ : Finset (Fin 6)).erase a).erase b, D.weight c := by
    refine Finset.sum_pos (fun c _ => D.weight_pos c) ?_
    rw [← Finset.card_pos, hcard]
    norm_num
  have hone := D.weight_sum_one
  rw [hsplit] at hone
  linarith

/-! ## 2. The four-set coweight cap -/

/-- **THE FOUR-SET COWEIGHT CAP.**  At a tie, a strictly dominating four-set
caps every nonnegative coweighting of its own atoms that its gap dominates in
the Loewner order: the coefficients total at most three.  Each member atom
reads the inverse gap at least at one, the weighted readings are a trace
against the comparison matrix, and that trace is at most the trace of the
identity. -/
theorem tie_fourSet_coweight_cap (D : WeightedDesign m 3) (htie : IsTie D)
    (F : Finset (Fin m)) (hF : F.card = 4)
    (hPD : (subsetSum D F - 1).PosDef) (w : Fin m → ℝ)
    (hw : ∀ a ∈ F, 0 ≤ w a)
    (hM : ((subsetSum D F - 1)
      - ∑ a ∈ F, w a • atomMatrix (D.atom a)).PosSemidef) :
    ∑ a ∈ F, w a ≤ 3 := by
  classical
  set B : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hB
  have hdet : IsUnit B.det := isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  have hInvPsd : (B⁻¹).PosSemidef := hPD.inv.posSemidef
  have hstep1 : ∑ a ∈ F, w a
      ≤ ∑ a ∈ F, w a * (D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a)) := by
    refine Finset.sum_le_sum fun a ha => ?_
    have hr := fourSet_leverage_ge_one D htie F hF hPD ha
    calc w a = w a * 1 := (mul_one _).symm
      _ ≤ w a * (D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a)) :=
          mul_le_mul_of_nonneg_left hr (hw a ha)
  have hstep2 : ∑ a ∈ F, w a * (D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a))
      = Matrix.trace (B⁻¹ * ∑ a ∈ F, w a • atomMatrix (D.atom a)) := by
    rw [Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_smul_comm, Matrix.trace_smul, trace_mul_atomMatrix, smul_eq_mul]
  have hthree : Matrix.trace (B⁻¹ * B) = 3 := by
    rw [Matrix.nonsing_inv_mul B hdet, Matrix.trace_one]
    norm_num
  have hMB : (∑ a ∈ F, w a • atomMatrix (D.atom a))
      + (B - ∑ a ∈ F, w a • atomMatrix (D.atom a)) = B := by abel
  have hsplit := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ
    => Matrix.trace (B⁻¹ * M)) hMB.symm
  simp only [Matrix.mul_add, Matrix.trace_add] at hsplit
  have hnonneg : 0 ≤ Matrix.trace
      (B⁻¹ * (B - ∑ a ∈ F, w a • atomMatrix (D.atom a))) :=
    trace_mul_nonneg_of_posSemidef hInvPsd hM
  linarith

/-! ## 3. An orthonormal triple resolves the identity -/

/-- **The resolution of the identity.**  Three orthonormal vectors of `ℝ³`
have atom sum one: their row matrix satisfies `R Rᵀ = 1`, hence `Rᵀ R = 1`,
and the latter is the atom sum. -/
theorem atomMatrix_orthonormal_resolution {u v w : Fin 3 → ℝ}
    (huu : u ⬝ᵥ u = 1) (hvv : v ⬝ᵥ v = 1) (hww : w ⬝ᵥ w = 1)
    (huv : u ⬝ᵥ v = 0) (huw : u ⬝ᵥ w = 0) (hvw : v ⬝ᵥ w = 0) :
    atomMatrix u + atomMatrix v + atomMatrix w = 1 := by
  set R : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![u, v, w] with hR
  have hrow : ∀ i j : Fin 3, (R * Rᵀ) i j = (![u, v, w] i) ⬝ᵥ (![u, v, w] j) := by
    intro i j
    rw [Matrix.mul_apply]
    have hterm : ∀ k : Fin 3, R i k * Rᵀ k j = ![u, v, w] i k * ![u, v, w] j k := by
      intro k
      rw [Matrix.transpose_apply, hR]
      rfl
    rw [Finset.sum_congr rfl fun k _ => hterm k]
    rfl
  have hRRT : R * Rᵀ = 1 := by
    ext i j
    rw [hrow i j]
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.one_apply_eq,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.one_apply_ne,
        ne_eq, Fin.reduceEq, not_false_eq_true] <;>
      first
        | exact huu | exact hvv | exact hww | exact huv | exact huw | exact hvw
        | (rw [dotProduct_comm]; assumption)
  have hRTR : Rᵀ * R = 1 := mul_eq_one_comm.mp hRRT
  have hsum : Rᵀ * R = atomMatrix u + atomMatrix v + atomMatrix w := by
    rw [transpose_mul_self_eq_sum_rows R, Fin.sum_univ_three]
    rfl
  rw [← hsum, hRTR]

/-- The resolution read at one vector: the three squared readings total the
squared length. -/
theorem read_sq_orthonormal_resolution {u v w : Fin 3 → ℝ}
    (huu : u ⬝ᵥ u = 1) (hvv : v ⬝ᵥ v = 1) (hww : w ⬝ᵥ w = 1)
    (huv : u ⬝ᵥ v = 0) (huw : u ⬝ᵥ w = 0) (hvw : v ⬝ᵥ w = 0)
    (zv : Fin 3 → ℝ) :
    (u ⬝ᵥ zv) ^ 2 + (v ⬝ᵥ zv) ^ 2 + (w ⬝ᵥ zv) ^ 2 = zv ⬝ᵥ zv := by
  have hres := atomMatrix_orthonormal_resolution huu hvv hww huv huw hvw
  have hread := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => zv ⬝ᵥ (M *ᵥ zv)) hres
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.one_mulVec] at hread
  rw [show atomMatrix u = Matrix.vecMulVec u u from rfl,
    show atomMatrix v = Matrix.vecMulVec v v from rfl,
    show atomMatrix w = Matrix.vecMulVec w w from rfl,
    quadForm_atomMatrix, quadForm_atomMatrix, quadForm_atomMatrix] at hread
  exact hread

/-! ## 4. The inside frame of the zero-pairing corner -/

/-- **The inside frame is rigid.**  At a corank-two corner whose second and
third inside atoms read the gap axis at zero, those two atoms are unit and
mutually orthogonal, and the first inside atom is the axis scaled by the full
axis mass: `g_x = a_x • u` with `a_x² = 1 + lam`. -/
theorem corner_axisOrthogonal_inside_frame (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hay : D.atom y ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u = 0) :
    D.atom x = (D.atom x ⬝ᵥ u) • u
      ∧ (D.atom x ⬝ᵥ u) ^ 2 = 1 + lam
      ∧ D.atom y ⬝ᵥ D.atom y = 1 ∧ D.atom z ⬝ᵥ D.atom z = 1
      ∧ D.atom y ⬝ᵥ D.atom z = 0 := by
  have hone : (0 : ℝ) < 1 + lam := by linarith
  have hcard : ({x, y, z} : Finset (Fin m)).card = 3 := card_triple_eq hxy hxz hyz
  have hx : x ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hy : y ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hz : z ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hmass := corner_axis_mass D ({x, y, z} : Finset (Fin m)) hunit hgap
  rw [sum_triple_eq hxy hxz hyz, hay, haz] at hmass
  have haxsq : (D.atom x ⬝ᵥ u) ^ 2 = 1 + lam := by nlinarith [hmass]
  have hexX := corner_heavyExcess_axis D _ hcard hlam hunit hgap hx
  simp only [heavyExcess] at hexX
  rw [haxsq, show leverageOf (D.atom x) = D.atom x ⬝ᵥ D.atom x from
    (dotProduct_self_eq_sum_sq (D.atom x)).symm] at hexX
  have hlevX : D.atom x ⬝ᵥ D.atom x = 1 + lam := by
    have hcancel := mul_left_cancel₀ (ne_of_gt hone)
      (show (1 + lam) * (D.atom x ⬝ᵥ D.atom x - 1) = (1 + lam) * lam by
        linarith [hexX])
    linarith
  have hxu : D.atom x = (D.atom x ⬝ᵥ u) • u := by
    have hzero : (D.atom x - (D.atom x ⬝ᵥ u) • u) ⬝ᵥ (D.atom x - (D.atom x ⬝ᵥ u) • u)
        = 0 := by
      rw [dotProduct_sub, sub_dotProduct, sub_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_dotProduct, dotProduct_smul, hunit,
        dotProduct_comm u (D.atom x)]
      simp only [smul_eq_mul]
      rw [hlevX]
      nlinarith [haxsq]
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hzero)
  have hexY := corner_heavyExcess_axis D _ hcard hlam hunit hgap hy
  simp only [heavyExcess] at hexY
  rw [hay, show leverageOf (D.atom y) = D.atom y ⬝ᵥ D.atom y from
    (dotProduct_self_eq_sum_sq (D.atom y)).symm] at hexY
  have hlevY : D.atom y ⬝ᵥ D.atom y = 1 := by
    have hcancel := mul_left_cancel₀ (ne_of_gt hone)
      (show (1 + lam) * (D.atom y ⬝ᵥ D.atom y - 1) = (1 + lam) * 0 by
        rw [mul_zero]
        nlinarith [hexY])
    linarith
  have hexZ := corner_heavyExcess_axis D _ hcard hlam hunit hgap hz
  simp only [heavyExcess] at hexZ
  rw [haz, show leverageOf (D.atom z) = D.atom z ⬝ᵥ D.atom z from
    (dotProduct_self_eq_sum_sq (D.atom z)).symm] at hexZ
  have hlevZ : D.atom z ⬝ᵥ D.atom z = 1 := by
    have hcancel := mul_left_cancel₀ (ne_of_gt hone)
      (show (1 + lam) * (D.atom z ⬝ᵥ D.atom z - 1) = (1 + lam) * 0 by
        rw [mul_zero]
        nlinarith [hexZ])
    linarith
  have hpairYZ := corner_atomPairing_axis D _ hcard hlam hunit hgap hy hz hyz
  rw [hay] at hpairYZ
  have hYZ : D.atom y ⬝ᵥ D.atom z = 0 := by
    have hzero : (1 + lam) * atomPairing D y z = 0 := by
      rw [hpairYZ]
      ring
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (ne_of_gt hone)
    · simpa only [atomPairing] using h
  exact ⟨hxu, haxsq, hlevY, hlevZ, hYZ⟩

/-! ## 5. The quadratic form of a subset gap, and the corner Parseval split -/

/-- The quadratic form of a subset gap: the squared readings of the member
atoms minus the squared length. -/
theorem quadForm_subsetSum_sub_one (D : WeightedDesign m 3) (F : Finset (Fin m))
    (zv : Fin 3 → ℝ) :
    zv ⬝ᵥ ((subsetSum D F - 1) *ᵥ zv)
      = ∑ a ∈ F, (D.atom a ⬝ᵥ zv) ^ 2 - zv ⬝ᵥ zv := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, subsetSum,
    Matrix.sum_mulVec, dotProduct_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show atomMatrix (D.atom a) = Matrix.vecMulVec (D.atom a) (D.atom a) from rfl,
    quadForm_atomMatrix]

/-- The Parseval reading split at a corner: the weighted squared readings of
the three inside atoms plus those of the outside total the squared length. -/
theorem parseval_read_corner_split (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (zv : Fin 3 → ℝ) :
    D.weight x * (D.atom x ⬝ᵥ zv) ^ 2 + D.weight y * (D.atom y ⬝ᵥ zv) ^ 2
        + D.weight z * (D.atom z ⬝ᵥ zv) ^ 2
        + ∑ d ∈ ({x, y, z} : Finset (Fin m))ᶜ, D.weight d * (D.atom d ⬝ᵥ zv) ^ 2
      = zv ⬝ᵥ zv := by
  have htotal := sum_weight_read_sq D zv
  rw [← Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin m))
    (fun a => D.weight a * (D.atom a ⬝ᵥ zv) ^ 2), sum_triple_eq hxy hxz hyz] at htotal
  linarith

/-! ## 6. The four-set of the zero-pairing corner dominates strictly -/

/-- **The four-set of the axis atom and the outside dominates strictly, with
no tie hypothesis.**  Parseval leaves the outside enough coweighted mass to
beat the two orthogonal unit inside atoms in every direction, and the axis
atom covers the axis. -/
theorem corner_axisOrthogonal_fourSet_posDef (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hay : D.atom y ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u = 0) :
    (subsetSum D (insert x (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef := by
  classical
  obtain ⟨hxu, haxsq, hlevY, hlevZ, hYZ⟩ :=
    corner_axisOrthogonal_inside_frame D hxy hxz hyz hlam hunit hgap hay haz
  have hone : (0 : ℝ) < 1 + lam := by linarith
  have hcardC : ({x, y, z} : Finset (Fin 6)).card = 3 := card_triple_eq hxy hxz hyz
  obtain ⟨d1, d2, d3, h12, h13, h23, hCc⟩ :=
    Finset.card_eq_three.mp
      (card_compl_eq_three_of_card_eq_three _ hcardC)
  have hxC : x ∈ ({x, y, z} : Finset (Fin 6)) := by simp
  have hxCc : x ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hmemd : ∀ d ∈ ({x, y, z} : Finset (Fin 6))ᶜ, d ≠ x ∧ d ≠ y ∧ d ≠ z := by
    intro d hd
    have := Finset.mem_compl.mp hd
    refine ⟨fun h => this ?_, fun h => this ?_, fun h => this ?_⟩ <;> simp [h]
  have hd1 : d1 ∈ ({x, y, z} : Finset (Fin 6))ᶜ := by rw [hCc]; simp
  have hd2 : d2 ∈ ({x, y, z} : Finset (Fin 6))ᶜ := by rw [hCc]; simp
  have hd3 : d3 ∈ ({x, y, z} : Finset (Fin 6))ᶜ := by rw [hCc]; simp
  -- the axis reading of the axis atom
  have hreadX : ∀ zv : Fin 3 → ℝ,
      (D.atom x ⬝ᵥ zv) ^ 2 = (1 + lam) * (u ⬝ᵥ zv) ^ 2 := by
    intro zv
    rw [hxu, smul_dotProduct, smul_eq_mul, mul_pow, haxsq]
  -- the axis weight cap
  have htx : D.weight x * (1 + lam) ≤ 1 := by
    have htotal := sum_weight_read_sq D u
    have hxterm : D.weight x * (D.atom x ⬝ᵥ u) ^ 2
        ≤ ∑ a, D.weight a * (D.atom a ⬝ᵥ u) ^ 2 :=
      Finset.single_le_sum (f := fun a => D.weight a * (D.atom a ⬝ᵥ u) ^ 2)
        (fun a _ => mul_nonneg (D.weight_pos a).le (sq_nonneg _))
        (Finset.mem_univ x)
    rw [htotal, hunit, haxsq] at hxterm
    linarith
  -- the outside coweight floor
  set rho : ℝ := min ((1 - D.weight d1) / D.weight d1)
      (min ((1 - D.weight d2) / D.weight d2) ((1 - D.weight d3) / D.weight d3))
    with hrho
  have hodds : ∀ d ∈ ({x, y, z} : Finset (Fin 6))ᶜ, ∀ e : Fin 6, e ≠ d →
      D.weight e < ((1 - D.weight d) / D.weight d) * (1 - D.weight e) := by
    intro d hd e hed
    have hdpos := D.weight_pos d
    have hde := sixWeight_pair_lt_one D (Ne.symm hed)
    have hec : (0 : ℝ) < 1 - D.weight e := by linarith [D.weight_pos d]
    rw [div_mul_eq_mul_div, lt_div_iff₀ hdpos]
    nlinarith [hde, D.weight_pos e, hdpos]
  have hrho_pairs : D.weight y < rho * (1 - D.weight y)
      ∧ D.weight z < rho * (1 - D.weight z) := by
    have hy1 := hodds d1 hd1 y (fun h => (hmemd d1 hd1).2.1 h.symm)
    have hy2 := hodds d2 hd2 y (fun h => (hmemd d2 hd2).2.1 h.symm)
    have hy3 := hodds d3 hd3 y (fun h => (hmemd d3 hd3).2.1 h.symm)
    have hz1 := hodds d1 hd1 z (fun h => (hmemd d1 hd1).2.2 h.symm)
    have hz2 := hodds d2 hd2 z (fun h => (hmemd d2 hd2).2.2 h.symm)
    have hz3 := hodds d3 hd3 z (fun h => (hmemd d3 hd3).2.2 h.symm)
    have hycpos : (0 : ℝ) < 1 - D.weight y := by
      have := sixWeight_pair_lt_one D hxy
      linarith [D.weight_pos x]
    have hzcpos : (0 : ℝ) < 1 - D.weight z := by
      have := sixWeight_pair_lt_one D hxz
      linarith [D.weight_pos x]
    constructor
    · rw [hrho]
      rcases min_cases ((1 - D.weight d1) / D.weight d1)
        (min ((1 - D.weight d2) / D.weight d2) ((1 - D.weight d3) / D.weight d3)) with
        ⟨heq, _⟩ | ⟨heq, _⟩
      · rw [heq]; exact hy1
      · rw [heq]
        rcases min_cases ((1 - D.weight d2) / D.weight d2)
          ((1 - D.weight d3) / D.weight d3) with ⟨heq2, _⟩ | ⟨heq2, _⟩
        · rw [heq2]; exact hy2
        · rw [heq2]; exact hy3
    · rw [hrho]
      rcases min_cases ((1 - D.weight d1) / D.weight d1)
        (min ((1 - D.weight d2) / D.weight d2) ((1 - D.weight d3) / D.weight d3)) with
        ⟨heq, _⟩ | ⟨heq, _⟩
      · rw [heq]; exact hz1
      · rw [heq]
        rcases min_cases ((1 - D.weight d2) / D.weight d2)
          ((1 - D.weight d3) / D.weight d3) with ⟨heq2, _⟩ | ⟨heq2, _⟩
        · rw [heq2]; exact hz2
        · rw [heq2]; exact hz3
  have hrhod : ∀ d ∈ ({x, y, z} : Finset (Fin 6))ᶜ,
      rho * D.weight d ≤ 1 - D.weight d := by
    intro d hd
    have hdpos := D.weight_pos d
    have hle : rho ≤ (1 - D.weight d) / D.weight d := by
      rw [hCc] at hd
      rcases Finset.mem_insert.mp hd with h | h
      · rw [h, hrho]; exact min_le_left _ _
      · rcases Finset.mem_insert.mp h with h' | h'
        · rw [h', hrho]; exact le_trans (min_le_right _ _) (min_le_left _ _)
        · rw [Finset.mem_singleton.mp h', hrho]
          exact le_trans (min_le_right _ _) (min_le_right _ _)
    calc rho * D.weight d ≤ ((1 - D.weight d) / D.weight d) * D.weight d :=
          mul_le_mul_of_nonneg_right hle hdpos.le
      _ = 1 - D.weight d := div_mul_cancel₀ _ (ne_of_gt hdpos)
  have hrhopos : 0 < rho := by
    have hbase : ∀ d ∈ ({x, y, z} : Finset (Fin 6))ᶜ,
        (0 : ℝ) < (1 - D.weight d) / D.weight d := by
      intro d hd
      have := sixWeight_pair_lt_one D (hmemd d hd).1
      exact div_pos (by linarith [D.weight_pos x]) (D.weight_pos d)
    rw [hrho]
    exact lt_min (hbase d1 hd1) (lt_min (hbase d2 hd2) (hbase d3 hd3))
  -- positive definiteness through the quadratic form
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one D _), fun zv hzv => ?_⟩
  rw [star_trivial, quadForm_subsetSum_sub_one,
    Finset.sum_insert hxCc, hCc, sum_triple_eq h12 h13 h23]
  have hpar := parseval_read_corner_split D hxy hxz hyz zv
  rw [hCc, sum_triple_eq h12 h13 h23] at hpar
  have hres := read_sq_orthonormal_resolution hunit hlevY hlevZ
    (by rw [dotProduct_comm]; exact hay) (by rw [dotProduct_comm]; exact haz) hYZ zv
  have hZpos : 0 < zv ⬝ᵥ zv := dotProduct_self_pos hzv
  have hreadXz := hreadX zv
  set Su : ℝ := (u ⬝ᵥ zv) ^ 2 with hSu
  set Sy : ℝ := (D.atom y ⬝ᵥ zv) ^ 2 with hSy
  set Sz : ℝ := (D.atom z ⬝ᵥ zv) ^ 2 with hSz
  set S1 : ℝ := (D.atom d1 ⬝ᵥ zv) ^ 2 with hS1
  set S2 : ℝ := (D.atom d2 ⬝ᵥ zv) ^ 2 with hS2
  set S3 : ℝ := (D.atom d3 ⬝ᵥ zv) ^ 2 with hS3
  have hSunn : 0 ≤ Su := sq_nonneg _
  have hSynn : 0 ≤ Sy := sq_nonneg _
  have hSznn : 0 ≤ Sz := sq_nonneg _
  have hd1b : rho * (D.weight d1 * S1) ≤ (1 - D.weight d1) * S1 := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hrhod d1 hd1) (sq_nonneg _)
  have hd2b : rho * (D.weight d2 * S2) ≤ (1 - D.weight d2) * S2 := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hrhod d2 hd2) (sq_nonneg _)
  have hd3b : rho * (D.weight d3 * S3) ≤ (1 - D.weight d3) * S3 := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hrhod d3 hd3) (sq_nonneg _)
  -- the exact decomposition of the quadratic form
  have hkey : (D.atom x ⬝ᵥ zv) ^ 2 + (S1 + (S2 + S3)) - zv ⬝ᵥ zv
      = ((1 - D.weight x) * (1 + lam) * Su
          + rho * ((1 - D.weight x * (1 + lam)) * Su)
          + (rho * (1 - D.weight y) - D.weight y) * Sy
          + (rho * (1 - D.weight z) - D.weight z) * Sz)
        + (((1 - D.weight d1) * S1 - rho * (D.weight d1 * S1))
          + (((1 - D.weight d2) * S2 - rho * (D.weight d2 * S2))
            + ((1 - D.weight d3) * S3 - rho * (D.weight d3 * S3)))) := by
    have hmass : D.weight d1 * S1 + (D.weight d2 * S2 + D.weight d3 * S3)
        = zv ⬝ᵥ zv - D.weight x * ((1 + lam) * Su) - D.weight y * Sy
          - D.weight z * Sz := by
      rw [hreadXz] at hpar
      linarith [hpar]
    linear_combination hreadXz + (1 + rho) * hmass - rho * hres
  rw [hkey]
  have hcx : (0 : ℝ) < 1 - D.weight x := by
    have := sixWeight_pair_lt_one D hxy
    linarith [D.weight_pos y]
  have h1mtx : (0 : ℝ) ≤ 1 - D.weight x * (1 + lam) := by linarith [htx]
  have hcy := hrho_pairs.1
  have hcz := hrho_pairs.2
  have hout : 0 ≤ ((1 - D.weight d1) * S1 - rho * (D.weight d1 * S1))
      + (((1 - D.weight d2) * S2 - rho * (D.weight d2 * S2))
        + ((1 - D.weight d3) * S3 - rho * (D.weight d3 * S3))) := by
    linarith [hd1b, hd2b, hd3b]
  have hcase : 0 < Su ∨ 0 < Sy ∨ 0 < Sz := by
    by_contra hcon
    push Not at hcon
    linarith [hres, hZpos, hcon.1, hcon.2.1, hcon.2.2]
  have hp2 : 0 ≤ rho * ((1 - D.weight x * (1 + lam)) * Su) :=
    mul_nonneg hrhopos.le (mul_nonneg h1mtx hSunn)
  have hp3 : 0 ≤ (rho * (1 - D.weight y) - D.weight y) * Sy :=
    mul_nonneg (by linarith [hcy]) hSynn
  have hp4 : 0 ≤ (rho * (1 - D.weight z) - D.weight z) * Sz :=
    mul_nonneg (by linarith [hcz]) hSznn
  have hp1 : 0 ≤ (1 - D.weight x) * (1 + lam) * Su :=
    mul_nonneg (mul_nonneg hcx.le hone.le) hSunn
  rcases hcase with hpos | hpos | hpos
  · have : 0 < (1 - D.weight x) * (1 + lam) * Su := mul_pos (mul_pos hcx hone) hpos
    linarith [hout, hp2, hp3, hp4]
  · have : 0 < (rho * (1 - D.weight y) - D.weight y) * Sy :=
      mul_pos (by linarith [hcy]) hpos
    linarith [hout, hp1, hp2, hp4]
  · have : 0 < (rho * (1 - D.weight z) - D.weight z) * Sz :=
      mul_pos (by linarith [hcz]) hpos
    linarith [hout, hp1, hp2, hp3]

/-! ## 7. The kill: two inside atoms orthogonal to the axis -/

/-- **A tie has no corank-two corner with two inside atoms orthogonal to the
axis.**  The four-set of the axis atom and the outside dominates strictly, and
the coweight cap of its four readings contradicts the positivity of the
weights.  No planarity, no primitivity and no nondegeneracy is consumed. -/
theorem corner_twoAxisZero_absurd (D : WeightedDesign 6 3) (htie : IsTie D)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hay : D.atom y ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u = 0) : False := by
  classical
  obtain ⟨hxu, haxsq, hlevY, hlevZ, hYZ⟩ :=
    corner_axisOrthogonal_inside_frame D hxy hxz hyz hlam hunit hgap hay haz
  have hone : (0 : ℝ) < 1 + lam := by linarith
  have hcardC : ({x, y, z} : Finset (Fin 6)).card = 3 := card_triple_eq hxy hxz hyz
  obtain ⟨d1, d2, d3, h12, h13, h23, hCc⟩ :=
    Finset.card_eq_three.mp (card_compl_eq_three_of_card_eq_three _ hcardC)
  have hxC : x ∈ ({x, y, z} : Finset (Fin 6)) := by simp
  have hxCc : x ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hmemd : ∀ d ∈ ({x, y, z} : Finset (Fin 6))ᶜ, d ≠ x ∧ d ≠ y ∧ d ≠ z := by
    intro d hd
    have := Finset.mem_compl.mp hd
    refine ⟨fun h => this ?_, fun h => this ?_, fun h => this ?_⟩ <;> simp [h]
  have hd1 : d1 ∈ ({x, y, z} : Finset (Fin 6))ᶜ := by rw [hCc]; simp
  have hd2 : d2 ∈ ({x, y, z} : Finset (Fin 6))ᶜ := by rw [hCc]; simp
  have hd3 : d3 ∈ ({x, y, z} : Finset (Fin 6))ᶜ := by rw [hCc]; simp
  -- the four-set
  set F : Finset (Fin 6) := insert x (({x, y, z} : Finset (Fin 6))ᶜ) with hF
  have hFcard : F.card = 4 := by
    rw [hF, Finset.card_insert_of_notMem hxCc, Finset.card_compl, hcardC]
    simp
  have hPD : (subsetSum D F - 1).PosDef :=
    corner_axisOrthogonal_fourSet_posDef D hxy hxz hyz hlam hunit hgap hay haz
  -- the coweighting: the odds total of the two orthogonal inside atoms
  have hycpos : (0 : ℝ) < 1 - D.weight y := by
    have := sixWeight_pair_lt_one D hxy
    linarith [D.weight_pos x]
  have hzcpos : (0 : ℝ) < 1 - D.weight z := by
    have := sixWeight_pair_lt_one D hxz
    linarith [D.weight_pos x]
  set odds : ℝ := max (D.weight y / (1 - D.weight y)) (D.weight z / (1 - D.weight z))
    with hodds
  have hoddsnn : 0 ≤ odds :=
    le_trans (div_nonneg (D.weight_pos y).le hycpos.le) (le_max_left _ _)
  have hoddsy : D.weight y ≤ odds * (1 - D.weight y) := by
    have h1 : (D.weight y / (1 - D.weight y)) * (1 - D.weight y) = D.weight y :=
      div_mul_cancel₀ _ (ne_of_gt hycpos)
    calc D.weight y = (D.weight y / (1 - D.weight y)) * (1 - D.weight y) := h1.symm
      _ ≤ odds * (1 - D.weight y) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hycpos.le
  have hoddsz : D.weight z ≤ odds * (1 - D.weight z) := by
    have h1 : (D.weight z / (1 - D.weight z)) * (1 - D.weight z) = D.weight z :=
      div_mul_cancel₀ _ (ne_of_gt hzcpos)
    calc D.weight z = (D.weight z / (1 - D.weight z)) * (1 - D.weight z) := h1.symm
      _ ≤ odds * (1 - D.weight z) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hzcpos.le
  -- the coefficient function
  set w : Fin 6 → ℝ := fun a =>
    if a = x then 1 - D.weight x else (1 - D.weight a) - odds * D.weight a with hw
  have hwx : w x = 1 - D.weight x := by rw [hw]; simp
  have hwd : ∀ d ∈ ({x, y, z} : Finset (Fin 6))ᶜ,
      w d = (1 - D.weight d) - odds * D.weight d := by
    intro d hd
    rw [hw]
    simp [(hmemd d hd).1]
  -- nonnegativity of the coefficients on F
  have hwnn : ∀ a ∈ F, 0 ≤ w a := by
    intro a ha
    rw [hF] at ha
    rcases Finset.mem_insert.mp ha with h | h
    · rw [h, hwx]
      have := sixWeight_pair_lt_one D hxy
      linarith [D.weight_pos y]
    · rw [hwd a h]
      have hdy := sixWeight_pair_lt_one D (a := a) (b := y) fun hde =>
        (hmemd a h).2.1 hde
      have hdz := sixWeight_pair_lt_one D (a := a) (b := z) fun hde =>
        (hmemd a h).2.2 hde
      have hda := D.weight_pos a
      -- both odds candidates sit below the coweight ratio of `a`
      have hkey : odds * D.weight a ≤ 1 - D.weight a := by
        rw [hodds]
        rcases max_cases (D.weight y / (1 - D.weight y))
          (D.weight z / (1 - D.weight z)) with ⟨heq, _⟩ | ⟨heq, _⟩ <;> rw [heq]
        · rw [div_mul_eq_mul_div, div_le_iff₀ hycpos]
          nlinarith [hdy, D.weight_pos y, hda]
        · rw [div_mul_eq_mul_div, div_le_iff₀ hzcpos]
          nlinarith [hdz, D.weight_pos z, hda]
      linarith
  -- the Loewner comparison
  have hM : ((subsetSum D F - 1)
      - ∑ a ∈ F, w a • atomMatrix (D.atom a)).PosSemidef := by
    have hsym : ((subsetSum D F - 1) - ∑ a ∈ F, w a • atomMatrix (D.atom a))ᵀ
        = (subsetSum D F - 1) - ∑ a ∈ F, w a • atomMatrix (D.atom a) := by
      rw [Matrix.transpose_sub, transpose_subsetSum_sub_one, Matrix.transpose_sum]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Matrix.transpose_smul]
      congr 1
      exact (transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom a)).1)
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hsym, fun zv => ?_⟩
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, quadForm_subsetSum_sub_one,
      Matrix.sum_mulVec, dotProduct_sum]
    have hquadw : ∀ a : Fin 6, zv ⬝ᵥ ((w a • atomMatrix (D.atom a)) *ᵥ zv)
        = w a * (D.atom a ⬝ᵥ zv) ^ 2 := by
      intro a
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        show atomMatrix (D.atom a) = Matrix.vecMulVec (D.atom a) (D.atom a) from rfl,
        quadForm_atomMatrix]
    rw [Finset.sum_congr rfl fun a _ => hquadw a]
    rw [hF, Finset.sum_insert hxCc, Finset.sum_insert hxCc, hCc,
      sum_triple_eq h12 h13 h23, sum_triple_eq h12 h13 h23,
      hwx, hwd d1 hd1, hwd d2 hd2, hwd d3 hd3]
    have hpar := parseval_read_corner_split D hxy hxz hyz zv
    rw [hCc, sum_triple_eq h12 h13 h23] at hpar
    have hres := read_sq_orthonormal_resolution hunit hlevY hlevZ
      (by rw [dotProduct_comm]; exact hay) (by rw [dotProduct_comm]; exact haz) hYZ zv
    have hreadXz : (D.atom x ⬝ᵥ zv) ^ 2 = (1 + lam) * (u ⬝ᵥ zv) ^ 2 := by
      rw [hxu, smul_dotProduct, smul_eq_mul, mul_pow, haxsq]
    have htx : D.weight x * (1 + lam) ≤ 1 := by
      have htotal := sum_weight_read_sq D u
      have hxterm : D.weight x * (D.atom x ⬝ᵥ u) ^ 2
          ≤ ∑ a, D.weight a * (D.atom a ⬝ᵥ u) ^ 2 :=
        Finset.single_le_sum (f := fun a => D.weight a * (D.atom a ⬝ᵥ u) ^ 2)
          (fun a _ => mul_nonneg (D.weight_pos a).le (sq_nonneg _))
          (Finset.mem_univ x)
      rw [htotal, hunit, haxsq] at hxterm
      linarith
    set Su : ℝ := (u ⬝ᵥ zv) ^ 2 with hSuDef
    set Sy : ℝ := (D.atom y ⬝ᵥ zv) ^ 2 with hSyDef
    set Sz : ℝ := (D.atom z ⬝ᵥ zv) ^ 2 with hSzDef
    have hmass : D.weight d1 * ((D.atom d1 ⬝ᵥ zv) ^ 2)
        + (D.weight d2 * ((D.atom d2 ⬝ᵥ zv) ^ 2)
          + D.weight d3 * ((D.atom d3 ⬝ᵥ zv) ^ 2))
        = zv ⬝ᵥ zv - D.weight x * ((1 + lam) * Su) - D.weight y * Sy
          - D.weight z * Sz := by
      rw [hreadXz] at hpar
      linarith [hpar]
    have hkey : ((D.atom x ⬝ᵥ zv) ^ 2
          + ((D.atom d1 ⬝ᵥ zv) ^ 2 + ((D.atom d2 ⬝ᵥ zv) ^ 2 + (D.atom d3 ⬝ᵥ zv) ^ 2))
          - zv ⬝ᵥ zv)
        - ((1 - D.weight x) * (D.atom x ⬝ᵥ zv) ^ 2
          + ((1 - D.weight d1 - odds * D.weight d1) * (D.atom d1 ⬝ᵥ zv) ^ 2
            + ((1 - D.weight d2 - odds * D.weight d2) * (D.atom d2 ⬝ᵥ zv) ^ 2
              + (1 - D.weight d3 - odds * D.weight d3) * (D.atom d3 ⬝ᵥ zv) ^ 2)))
        = odds * ((1 - D.weight x * (1 + lam)) * Su)
          + (odds * (1 - D.weight y) - D.weight y) * Sy
          + (odds * (1 - D.weight z) - D.weight z) * Sz := by
      linear_combination D.weight x * hreadXz + (1 + odds) * hmass
        - odds * hres
    have hterm1 : 0 ≤ odds * ((1 - D.weight x * (1 + lam)) * Su) :=
      mul_nonneg hoddsnn (mul_nonneg (by linarith [htx]) (sq_nonneg _))
    have hterm2 : 0 ≤ (odds * (1 - D.weight y) - D.weight y) * Sy :=
      mul_nonneg (by linarith [hoddsy]) (sq_nonneg _)
    have hterm3 : 0 ≤ (odds * (1 - D.weight z) - D.weight z) * Sz :=
      mul_nonneg (by linarith [hoddsz]) (sq_nonneg _)
    linarith [hkey, hterm1, hterm2, hterm3]
  -- the cap fires
  have hcap := tie_fourSet_coweight_cap D htie F hFcard hPD w hwnn hM
  rw [hF, Finset.sum_insert hxCc, hCc, sum_triple_eq h12 h13 h23,
    hwx, hwd d1 hd1, hwd d2 hd2, hwd d3 hd3] at hcap
  -- the weight total
  have htot : D.weight x + D.weight y + D.weight z
      + (D.weight d1 + (D.weight d2 + D.weight d3)) = 1 := by
    have := D.weight_sum_one
    rw [← Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin 6)) D.weight,
      sum_triple_eq hxy hxz hyz, hCc, sum_triple_eq h12 h13 h23] at this
    linarith
  -- the contradiction: the cap forces a negative total of positive weights
  set ty := D.weight y
  set tz := D.weight z
  set tx := D.weight x
  set t1 := D.weight d1
  set t2 := D.weight d2
  set t3 := D.weight d3
  have hcap2 : ((1 - tx) + ((1 - t1 - odds * t1) + ((1 - t2 - odds * t2)
      + (1 - t3 - odds * t3)))) ≤ 3 := hcap
  have htau : t1 + t2 + t3 = 1 - tx - ty - tz := by linarith [htot]
  have hcap3 : (1 - tx) - (t1 + t2 + t3) ≤ odds * (t1 + t2 + t3) := by
    nlinarith [hcap2]
  have hposx := D.weight_pos x
  have hposy := D.weight_pos y
  have hposz := D.weight_pos z
  rcases max_cases (ty / (1 - ty)) (tz / (1 - tz)) with ⟨heq, _⟩ | ⟨heq, _⟩ <;>
    rw [hodds, heq] at hcap3
  · have h5 := mul_le_mul_of_nonneg_right hcap3 hycpos.le
    have h6 : (ty / (1 - ty) * (t1 + t2 + t3)) * (1 - ty) = ty * (t1 + t2 + t3) := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt hycpos)]
    rw [h6] at h5
    nlinarith [h5, htau, hposz, mul_pos hposx hposy]
  · have h5 := mul_le_mul_of_nonneg_right hcap3 hzcpos.le
    have h6 : (tz / (1 - tz) * (t1 + t2 + t3)) * (1 - tz) = tz * (t1 + t2 + t3) := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt hzcpos)]
    rw [h6] at h5
    nlinarith [h5, htau, hposy, mul_pos hposx hposz]

/-! ## 8. The stratum: all inside pairings zero -/

/-- **THE ZERO-PAIRING STRATUM OF THE CORNER IS EMPTY.**  A `(6,3)` tie has no
corank-two corner with a positive gap scale whose three inside pairings all
vanish.  The pairings are axis products, so two of the three inside atoms read
the axis at zero, and the four-set cap closes that configuration. -/
theorem corner_zeroPairings_absurd (D : WeightedDesign 6 3) (htie : IsTie D)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hPxy : atomPairing D x y = 0) (hPxz : atomPairing D x z = 0)
    (hPyz : atomPairing D y z = 0) : False := by
  have hcard : ({x, y, z} : Finset (Fin 6)).card = 3 := card_triple_eq hxy hxz hyz
  have hx : x ∈ ({x, y, z} : Finset (Fin 6)) := by simp
  have hy : y ∈ ({x, y, z} : Finset (Fin 6)) := by simp
  have hz : z ∈ ({x, y, z} : Finset (Fin 6)) := by simp
  have haxes : ∀ (e f : Fin 6), e ∈ ({x, y, z} : Finset (Fin 6))
      → f ∈ ({x, y, z} : Finset (Fin 6)) → e ≠ f → atomPairing D e f = 0
      → (D.atom e ⬝ᵥ u) * (D.atom f ⬝ᵥ u) = 0 := by
    intro e f he hf hef hP
    have := corner_atomPairing_axis D _ hcard hlam.le hunit hgap he hf hef
    rw [hP, mul_zero] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h (ne_of_gt hlam)
    · exact h
  have hxy' := haxes x y hx hy hxy hPxy
  have hxz' := haxes x z hx hz hxz hPxz
  have hyz' := haxes y z hy hz hyz hPyz
  by_cases hax : D.atom x ⬝ᵥ u = 0
  · by_cases hay : D.atom y ⬝ᵥ u = 0
    · -- x and y orthogonal: the axis carrier is z
      have hgap' : subsetSum D ({z, x, y} : Finset (Fin 6)) - 1
          = lam • atomMatrix u := by
        rw [show ({z, x, y} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) from by
          ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
        exact hgap
      exact corner_twoAxisZero_absurd D htie (Ne.symm hxz) (Ne.symm hyz) hxy
        hlam.le hunit hgap' hax hay
    · -- y carries the axis: x and z orthogonal
      have haz : D.atom z ⬝ᵥ u = 0 := by
        rcases mul_eq_zero.mp hyz' with h | h
        · exact absurd h hay
        · exact h
      have hgap' : subsetSum D ({y, x, z} : Finset (Fin 6)) - 1
          = lam • atomMatrix u := by
        rw [show ({y, x, z} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) from by
          ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
        exact hgap
      exact corner_twoAxisZero_absurd D htie (Ne.symm hxy) hyz hxz
        hlam.le hunit hgap' hax haz
  · -- x carries the axis: y and z orthogonal
    have hay : D.atom y ⬝ᵥ u = 0 := by
      rcases mul_eq_zero.mp hxy' with h | h
      · exact absurd h hax
      · exact h
    have haz : D.atom z ⬝ᵥ u = 0 := by
      rcases mul_eq_zero.mp hxz' with h | h
      · exact absurd h hax
      · exact h
    exact corner_twoAxisZero_absurd D htie hxy hxz hyz hlam.le hunit hgap hay haz

end Gtz
