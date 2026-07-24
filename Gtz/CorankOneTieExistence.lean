/-
# Corank-one ties exist over every weight vector

`isTie_iff_leverage_identity` cuts the corank-one tie locus out of the `(k+1, k)` designs
by `k+1` closed equations. It leaves open whether that locus is inhabited anywhere. This
file shows it is inhabited EVERYWHERE: for every `t` with `t_c > 0` and `Σ t_c = 1` there
is a `(k+1, k)` design carrying exactly those weights which is an exact tie
(`exists_isTie_of_weights`). Together the two statements say the corank-one tie stratum
is a SECTION over the open weight simplex — the weights are free, the leverages are then
forced (`leverage_of_isTie`), and no weight vector is missed.

So `tetraDesign` and `sharpDesign` are not special: they are the uniform point and one
non-uniform point of a stratum that meets every weight vector.

The construction is Naimark's chart run backwards. Write `u_c = √t_c · g_c`; Parseval
says the `k × (k+1)` matrix with those columns is a co-isometry, so `P = UᵀU` is a
rank-`k` projector with `P_cc = t_c ℓ_c`, and the leverage identity says exactly that its
complement `I − P` — necessarily a rank-one projector — has diagonal `(1 − t_c)/k`. A
rank-one projector is `p pᵀ` for a unit vector, so the design is pinned by

    p_c = √((1 − t_c)/k),      Σ_c p_c² = Σ_c (1 − t_c)/k = k/k = 1,

the normalisation holding automatically. `U` is then any orthonormal basis of `p^⊥`, and
Householder supplies one: with `v = p − e_0` the reflection `H = 1 − v vᵀ/(1 − p_0)` is
symmetric and involutive and carries `e_0` to `p`, so its remaining `k` columns are an
orthonormal basis of `p^⊥`. The atoms are those columns rescaled by `1/√t_c`.

Both halves of the design's data are read off `H` by splitting a row or column pairing at
index `0`: the columns `1..k` are orthonormal (Parseval) and the rows pair to
`δ_{cd} − p_c p_d` (the leverages).
-/
import Mathlib
import Gtz.Basic
import Gtz.Sanity
import Gtz.LeverageBound
import Gtz.ResidueDissolution
import Gtz.CorankOneTieCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {k : ℕ}

/-! ### Two helpers -/

/-- **A calibrated reflection is involutive**: `1 − a·(v vᵀ)` squares to `1` exactly when
`a·⟨v,v⟩ = 2`. The two cross terms and the rank-one square cancel. -/
theorem reflection_mul_self {size : ℕ} (coefficient : ℝ) (reflector : Fin size → ℝ)
    (hcalibrated : coefficient * (reflector ⬝ᵥ reflector) = 2) :
    (1 - coefficient • Matrix.vecMulVec reflector reflector)
        * (1 - coefficient • Matrix.vecMulVec reflector reflector) = 1 := by
  set outer := Matrix.vecMulVec reflector reflector with houter
  have hsquare : outer * outer = (reflector ⬝ᵥ reflector) • outer := by
    rw [houter, vecMulVec_mul_vecMulVec]
  have hexpand : ∀ base : Matrix (Fin size) (Fin size) ℝ,
      (1 - base) * (1 - base) = 1 - base - base + base * base := by
    intro base
    noncomm_ring
  have hdouble : (coefficient • outer) * (coefficient • outer)
      = coefficient • outer + coefficient • outer := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsquare, smul_smul, ← add_smul]
    congr 1
    rw [mul_assoc, hcalibrated]
    ring
  rw [hexpand, hdouble]
  abel

/-- Undoing the `1/√t` rescaling of two coordinates. -/
theorem weight_mul_div_sqrt_pair {scale first second : ℝ} (hscale : 0 < scale) :
    scale * (first / Real.sqrt scale * (second / Real.sqrt scale)) = first * second := by
  have hne : scale ≠ 0 := ne_of_gt hscale
  have hsplit : first / Real.sqrt scale * (second / Real.sqrt scale)
      = first * second / scale := by
    rw [div_mul_div_comm, Real.mul_self_sqrt hscale.le]
  rw [hsplit]
  field_simp

/-! ### The weight vector is interior -/

/-- On the open simplex with at least two atoms every weight is below one. -/
theorem weight_lt_one_of_simplex {weight : Fin (k + 1) → ℝ} (hk : 1 ≤ k)
    (hpos : ∀ c, 0 < weight c) (hsum : ∑ c, weight c = 1) (c : Fin (k + 1)) :
    weight c < 1 := by
  obtain ⟨other, hother⟩ := Fintype.exists_ne_of_one_lt_card
    (by simp only [Fintype.card_fin]; omega) c
  have hlt : weight c < ∑ d, weight d :=
    Finset.single_lt_sum hother (Finset.mem_univ c) (Finset.mem_univ other)
      (hpos other) (fun d _ _ => (hpos d).le)
  rwa [hsum] at hlt

/-! ### The defect profile `p_c = √((1 − t_c)/k)` -/

/-- The corank-one defect profile: the unit vector whose rank-one projector is the
complement of a corank-one design's Gram projector. -/
noncomputable def tieDefect (weight : Fin (k + 1) → ℝ) (c : Fin (k + 1)) : ℝ :=
  Real.sqrt ((1 - weight c) / (k : ℝ))

theorem tieDefect_sq {weight : Fin (k + 1) → ℝ} (hk : 1 ≤ k)
    (hlt : ∀ c, weight c < 1) (c : Fin (k + 1)) :
    tieDefect weight c ^ 2 = (1 - weight c) / (k : ℝ) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  exact Real.sq_sqrt (div_nonneg (by linarith [hlt c]) hkpos.le)

theorem tieDefect_pos {weight : Fin (k + 1) → ℝ} (hk : 1 ≤ k)
    (hlt : ∀ c, weight c < 1) (c : Fin (k + 1)) : 0 < tieDefect weight c := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  exact Real.sqrt_pos.mpr (div_pos (by linarith [hlt c]) hkpos)

/-- **The defect profile is automatically a unit vector**: the corank-one normalisation
`Σ_c (1 − t_c) = k` is exactly what makes `Σ_c p_c² = 1`. -/
theorem sum_tieDefect_sq {weight : Fin (k + 1) → ℝ} (hk : 1 ≤ k)
    (hlt : ∀ c, weight c < 1) (hsum : ∑ c, weight c = 1) :
    ∑ c, tieDefect weight c ^ 2 = 1 := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hcollapse : ((k : ℝ) + 1) - 1 = (k : ℝ) := by ring
  rw [Finset.sum_congr rfl fun c _ => tieDefect_sq hk hlt c, ← Finset.sum_div,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    hsum, nsmul_eq_mul, mul_one]
  push_cast
  rw [hcollapse, div_self (ne_of_gt hkpos)]

/-- The head entry of the defect profile is below one: the profile is a unit vector with
another strictly positive entry. -/
theorem tieDefect_head_lt_one {weight : Fin (k + 1) → ℝ} (hk : 1 ≤ k)
    (hlt : ∀ c, weight c < 1) (hsum : ∑ c, weight c = 1) :
    tieDefect weight 0 < 1 := by
  have hother : ((⟨0, hk⟩ : Fin k).succ : Fin (k + 1)) ≠ 0 := Fin.succ_ne_zero _
  have hotherPos : 0 < tieDefect weight ((⟨0, hk⟩ : Fin k).succ) ^ 2 := by
    have := tieDefect_pos hk hlt ((⟨0, hk⟩ : Fin k).succ)
    positivity
  have hheadSq : tieDefect weight 0 ^ 2 < ∑ c, tieDefect weight c ^ 2 :=
    Finset.single_lt_sum hother (Finset.mem_univ 0) (Finset.mem_univ _) hotherPos
      (fun d _ _ => sq_nonneg _)
  rw [sum_tieDefect_sq hk hlt hsum] at hheadSq
  nlinarith [tieDefect_pos hk hlt (0 : Fin (k + 1)), hheadSq]

/-! ### The Householder reflector carrying `e_0` to the defect profile -/

/-- The reflector `v = p − e_0`. -/
noncomputable def tieReflector (weight : Fin (k + 1) → ℝ) (c : Fin (k + 1)) : ℝ :=
  tieDefect weight c - (if c = 0 then 1 else 0)

theorem tieReflector_head (weight : Fin (k + 1) → ℝ) :
    tieReflector weight 0 = tieDefect weight 0 - 1 := by
  rw [tieReflector, if_pos rfl]

/-- `|v|² = 2(1 − p_0)`: the reflector's squared length, in the form that cancels the
scaling in the reflection. -/
theorem tieReflector_normSq {weight : Fin (k + 1) → ℝ} (hk : 1 ≤ k)
    (hlt : ∀ c, weight c < 1) (hsum : ∑ c, weight c = 1) :
    tieReflector weight ⬝ᵥ tieReflector weight = 2 * (1 - tieDefect weight 0) := by
  have hexpand : ∀ c : Fin (k + 1),
      tieReflector weight c * tieReflector weight c
        = tieDefect weight c ^ 2
          - (if c = 0 then 2 * tieDefect weight 0 - 1 else 0) := by
    intro c
    rw [tieReflector]
    by_cases hc : c = 0
    · subst hc; rw [if_pos rfl, if_pos rfl]; ring
    · rw [if_neg hc, if_neg hc]; ring
  rw [dotProduct, Finset.sum_congr rfl fun c _ => hexpand c, Finset.sum_sub_distrib,
    sum_tieDefect_sq hk hlt hsum, Finset.sum_ite_eq' Finset.univ (0 : Fin (k + 1)),
    if_pos (Finset.mem_univ _)]
  ring

/-! ### The Householder reflection -/

/-- The Householder reflection `H = 1 − v vᵀ/(1 − p_0)`: symmetric, involutive, and
carrying `e_0` to the defect profile. -/
noncomputable def tieHouseholder (weight : Fin (k + 1) → ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  1 - (1 - tieDefect weight 0)⁻¹
    • Matrix.vecMulVec (tieReflector weight) (tieReflector weight)

theorem tieHouseholder_apply (weight : Fin (k + 1) → ℝ) (c d : Fin (k + 1)) :
    tieHouseholder weight c d
      = (if c = d then (1 : ℝ) else 0)
        - (1 - tieDefect weight 0)⁻¹ * (tieReflector weight c * tieReflector weight d) := by
  rw [tieHouseholder]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]

theorem tieHouseholder_symm (weight : Fin (k + 1) → ℝ) (c d : Fin (k + 1)) :
    tieHouseholder weight c d = tieHouseholder weight d c := by
  rw [tieHouseholder_apply, tieHouseholder_apply]
  by_cases hc : c = d
  · rw [hc]
  · rw [if_neg hc, if_neg (Ne.symm hc)]
    ring

/-- **The reflection is involutive.** `v vᵀ v vᵀ = |v|² · v vᵀ` and `|v|² = 2(1 − p_0)`
cancel the two copies of the scaling exactly. -/
theorem tieHouseholder_mul_self {weight : Fin (k + 1) → ℝ} (hk : 1 ≤ k)
    (hlt : ∀ c, weight c < 1) (hsum : ∑ c, weight c = 1) :
    tieHouseholder weight * tieHouseholder weight = 1 := by
  have hheadLt : tieDefect weight 0 < 1 := tieDefect_head_lt_one hk hlt hsum
  have hgapNe : (1 : ℝ) - tieDefect weight 0 ≠ 0 := by linarith
  rw [tieHouseholder]
  refine reflection_mul_self _ _ ?_
  rw [tieReflector_normSq hk hlt hsum]
  field_simp

/-- **The reflection carries `e_0` to the defect profile**: its column `0` is `p`. -/
theorem tieHouseholder_head {weight : Fin (k + 1) → ℝ} (hk : 1 ≤ k)
    (hlt : ∀ c, weight c < 1) (hsum : ∑ c, weight c = 1) (c : Fin (k + 1)) :
    tieHouseholder weight c 0 = tieDefect weight c := by
  have hheadLt : tieDefect weight 0 < 1 := tieDefect_head_lt_one hk hlt hsum
  have hgapNe : (1 : ℝ) - tieDefect weight 0 ≠ 0 := by linarith
  have hcollapse : (1 - tieDefect weight 0)⁻¹ * tieReflector weight 0 = -1 := by
    rw [tieReflector_head,
      show tieDefect weight 0 - 1 = -(1 - tieDefect weight 0) from by ring,
      mul_neg, inv_mul_cancel₀ hgapNe]
  have hreflectAt : tieReflector weight c
      = tieDefect weight c - (if c = 0 then (1 : ℝ) else 0) := rfl
  rw [tieHouseholder_apply, hreflectAt,
    show (1 - tieDefect weight 0)⁻¹
        * ((tieDefect weight c - (if c = 0 then (1 : ℝ) else 0)) * tieReflector weight 0)
      = ((1 - tieDefect weight 0)⁻¹ * tieReflector weight 0)
        * (tieDefect weight c - (if c = 0 then (1 : ℝ) else 0)) from by ring,
    hcollapse]
  ring

/-! ### The two pairings that carry the design's data -/

/-- **Columns `1..k` of the reflection are orthonormal** — this is Parseval for the
constructed design. -/
theorem tieHouseholder_column_pairing {weight : Fin (k + 1) → ℝ} (hk : 1 ≤ k)
    (hlt : ∀ c, weight c < 1) (hsum : ∑ c, weight c = 1) (row col : Fin k) :
    ∑ c, tieHouseholder weight c row.succ * tieHouseholder weight c col.succ
      = if row = col then (1 : ℝ) else 0 := by
  have hinvolutive := tieHouseholder_mul_self hk hlt hsum
  calc ∑ c, tieHouseholder weight c row.succ * tieHouseholder weight c col.succ
      = ∑ c, tieHouseholder weight row.succ c * tieHouseholder weight c col.succ :=
        Finset.sum_congr rfl fun c _ => by rw [tieHouseholder_symm weight row.succ c]
    _ = (tieHouseholder weight * tieHouseholder weight) row.succ col.succ :=
        (Matrix.mul_apply).symm
    _ = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) row.succ col.succ := by
        rw [hinvolutive]
    _ = if row = col then (1 : ℝ) else 0 := by
        rw [Matrix.one_apply]
        by_cases hrow : row = col
        · rw [hrow, if_pos rfl, if_pos rfl]
        · rw [if_neg hrow, if_neg (fun hEq : row.succ = col.succ => hrow (Fin.succ_inj.mp hEq))]

/-- **Rows of the reflection pair to `δ_{cd} − p_c p_d` off the head column** — this is
the leverage half of the constructed design. -/
theorem tieHouseholder_tail_pairing {weight : Fin (k + 1) → ℝ} (hk : 1 ≤ k)
    (hlt : ∀ c, weight c < 1) (hsum : ∑ c, weight c = 1) (c d : Fin (k + 1)) :
    ∑ i : Fin k, tieHouseholder weight c i.succ * tieHouseholder weight d i.succ
      = (if c = d then (1 : ℝ) else 0) - tieDefect weight c * tieDefect weight d := by
  have hinvolutive := tieHouseholder_mul_self hk hlt hsum
  have hrow : ∑ e, tieHouseholder weight c e * tieHouseholder weight d e
      = if c = d then (1 : ℝ) else 0 := by
    calc ∑ e, tieHouseholder weight c e * tieHouseholder weight d e
        = ∑ e, tieHouseholder weight c e * tieHouseholder weight e d :=
          Finset.sum_congr rfl fun e _ => by rw [tieHouseholder_symm weight d e]
      _ = (tieHouseholder weight * tieHouseholder weight) c d := (Matrix.mul_apply).symm
      _ = if c = d then (1 : ℝ) else 0 := by rw [hinvolutive, Matrix.one_apply]
  rw [Fin.sum_univ_succ, tieHouseholder_head hk hlt hsum, tieHouseholder_head hk hlt hsum]
    at hrow
  linarith [hrow]

/-! ### The design -/

/-- The atoms of the tie at a prescribed weight vector: the reflection's columns `1..k`,
each rescaled by `1/√t_c`. -/
noncomputable def simplexTieAtom (weight : Fin (k + 1) → ℝ) (c : Fin (k + 1))
    (i : Fin k) : ℝ :=
  tieHouseholder weight c i.succ / Real.sqrt (weight c)

/-- **The tie at a prescribed weight vector.** -/
noncomputable def simplexTieDesign (weight : Fin (k + 1) → ℝ) (hk : 1 ≤ k)
    (hpos : ∀ c, 0 < weight c) (hsum : ∑ c, weight c = 1) : WeightedDesign (k + 1) k where
  atom := simplexTieAtom weight
  weight := weight
  weight_pos := hpos
  weight_sum_one := hsum
  isParseval := by
    have hlt : ∀ c, weight c < 1 := weight_lt_one_of_simplex hk hpos hsum
    ext row col
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      smul_eq_mul, Matrix.one_apply]
    have hterm : ∀ c : Fin (k + 1),
        weight c * (simplexTieAtom weight c row * simplexTieAtom weight c col)
          = tieHouseholder weight c row.succ * tieHouseholder weight c col.succ :=
      fun c => weight_mul_div_sqrt_pair (hpos c)
    rw [Finset.sum_congr rfl fun c _ => hterm c]
    exact tieHouseholder_column_pairing hk hlt hsum row col

theorem simplexTieDesign_weight (weight : Fin (k + 1) → ℝ) (hk : 1 ≤ k)
    (hpos : ∀ c, 0 < weight c) (hsum : ∑ c, weight c = 1) :
    (simplexTieDesign weight hk hpos hsum).weight = weight := rfl

/-- The weighted leverage of a constructed atom is the reflection's row pairing with
itself off the head column. -/
theorem weight_mul_leverage_simplexTieAtom {weight : Fin (k + 1) → ℝ}
    {c : Fin (k + 1)} (hpos : 0 < weight c) :
    weight c * leverageOf (simplexTieAtom weight c)
      = ∑ i : Fin k, tieHouseholder weight c i.succ * tieHouseholder weight c i.succ := by
  rw [leverageOf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [simplexTieAtom, sq]
  exact weight_mul_div_sqrt_pair hpos

/-- **The construction lands on the tie locus**: its leverages satisfy the corank-one
identity at every atom, by construction rather than by computation with coordinates. -/
theorem simplexTieDesign_leverage_identity (weight : Fin (k + 1) → ℝ) (hk : 1 ≤ k)
    (hpos : ∀ c, 0 < weight c) (hsum : ∑ c, weight c = 1) (c : Fin (k + 1)) :
    (k : ℝ) * (simplexTieDesign weight hk hpos hsum).weight c
        * leverageOf ((simplexTieDesign weight hk hpos hsum).atom c)
      = ((k : ℝ) - 1) + (simplexTieDesign weight hk hpos hsum).weight c := by
  have hlt : ∀ d, weight d < 1 := weight_lt_one_of_simplex hk hpos hsum
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hpair := tieHouseholder_tail_pairing hk hlt hsum c c
  rw [if_pos rfl] at hpair
  have hdefect : tieDefect weight c * tieDefect weight c = (1 - weight c) / (k : ℝ) := by
    rw [← sq]
    exact tieDefect_sq hk hlt c
  have hkey : weight c * leverageOf (simplexTieAtom weight c) = 1 - (1 - weight c) / (k : ℝ) := by
    rw [weight_mul_leverage_simplexTieAtom (hpos c), hpair, hdefect]
  show (k : ℝ) * weight c * leverageOf (simplexTieAtom weight c) = ((k : ℝ) - 1) + weight c
  calc (k : ℝ) * weight c * leverageOf (simplexTieAtom weight c)
      = (k : ℝ) * (weight c * leverageOf (simplexTieAtom weight c)) := by ring
    _ = (k : ℝ) * (1 - (1 - weight c) / (k : ℝ)) := by rw [hkey]
    _ = ((k : ℝ) - 1) + weight c := by field_simp; ring

theorem simplexTieDesign_isTie (weight : Fin (k + 1) → ℝ) (hk : 1 ≤ k)
    (hpos : ∀ c, 0 < weight c) (hsum : ∑ c, weight c = 1) :
    IsTie (simplexTieDesign weight hk hpos hsum) :=
  (isTie_iff_leverage_identity hk _).mpr
    (simplexTieDesign_leverage_identity weight hk hpos hsum)

/-! ### The stratum -/

/-- **Corank-one ties exist over every weight vector.** Together with
`isTie_iff_leverage_identity` this pins the corank-one tie stratum completely: it is a
section over the open weight simplex — every weight vector carries a tie, and a design
with those weights is a tie exactly when its leverages sit on the identity. -/
theorem exists_isTie_of_weights (hk : 1 ≤ k) (weight : Fin (k + 1) → ℝ)
    (hpos : ∀ c, 0 < weight c) (hsum : ∑ c, weight c = 1) :
    ∃ D : WeightedDesign (k + 1) k, D.weight = weight ∧ IsTie D :=
  ⟨simplexTieDesign weight hk hpos hsum, rfl, simplexTieDesign_isTie weight hk hpos hsum⟩

/-- At a corank-one tie the leverages are not merely constrained but DETERMINED by the
weights: `ℓ_c = ((k − 1) + t_c)/(k t_c)`. -/
theorem leverage_of_isTie (hk : 1 ≤ k) (D : WeightedDesign (k + 1) k) (htie : IsTie D)
    (c : Fin (k + 1)) :
    leverageOf (D.atom c) = (((k : ℝ) - 1) + D.weight c) / ((k : ℝ) * D.weight c) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hprod : (0 : ℝ) < (k : ℝ) * D.weight c := mul_pos hkpos (D.weight_pos c)
  have hidentity := (isTie_iff_leverage_identity hk D).mp htie c
  rw [eq_div_iff (ne_of_gt hprod)]
  linarith [hidentity]

/-- **The corank-one tie stratum, both halves.** The equations cut it out, and it meets
every point of the open weight simplex. -/
theorem corank_one_tie_stratum (hk : 1 ≤ k) :
    (∀ D : WeightedDesign (k + 1) k, IsTie D
        ↔ ∀ c, (k : ℝ) * D.weight c * leverageOf (D.atom c) = ((k : ℝ) - 1) + D.weight c)
      ∧ (∀ weight : Fin (k + 1) → ℝ, (∀ c, 0 < weight c) → ∑ c, weight c = 1 →
          ∃ D : WeightedDesign (k + 1) k, D.weight = weight ∧ IsTie D) :=
  ⟨fun D => isTie_iff_leverage_identity hk D, fun weight hpos hsum =>
    exists_isTie_of_weights hk weight hpos hsum⟩

/-- The uniform point of the stratum, at every rank: the regular-simplex tie. -/
theorem exists_isTie_uniform (hk : 1 ≤ k) :
    ∃ D : WeightedDesign (k + 1) k,
      (∀ c, D.weight c = 1 / ((k : ℝ) + 1)) ∧ IsTie D := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hne : (k : ℝ) + 1 ≠ 0 := by positivity
  obtain ⟨D, hweight, htie⟩ := exists_isTie_of_weights hk (fun _ => 1 / ((k : ℝ) + 1))
    (fun _ => by positivity)
    (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp)
  exact ⟨D, fun c => by rw [hweight], htie⟩

end Gtz
