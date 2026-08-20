import Gtz.Wave.OppositeHornCount

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The bracket budget of a corank-two corner

The opposite-sign floor buys a LOWER bound on one informative bracket.  To spend
it one needs the RESOURCE: how much informative bracket mass a corner owns.
This module computes that mass exactly, in closed form, in the corner scalars.

Write `C = {x,y,z}` for the dominator, `e_a` for the heavy excesses and `P_ab`
for the pairings.  The three anchored bracket families
`ξ_d = [xyd]`, `η_d = [xzd]`, `ζ_d = [yzd]` read over the complement carry a
weighted Gram whose SIX entries are all corner scalars:

  `Σ_{d ∈ Cᶜ} t_d·ξ_d²   = 1 + e_x + e_y − t_z(1+λ)`   (`corner_compl_bracket_sq_sum`)
  `Σ_{d ∈ Cᶜ} t_d·ξ_dη_d = P_yz`                        (landed transport)
  `Σ_{d ∈ Cᶜ} t_d·ξ_dζ_d = −P_xz`                       (`corner_compl_bracket_mixed_xy`)
  `Σ_{d ∈ Cᶜ} t_d·η_dζ_d = P_xy`                        (`corner_compl_bracket_mixed_xz`)

and the diagonal law is the same statement at the three label pairs.  The
inside atoms contribute exactly one term, `t_z·[xyz]² = t_z(1+λ)`, because two
of the three inside brackets vanish on repeated slots.

Two exact consequences follow at `(6,3)`, where the complement is a TRIPLE and
the three-slot Lagrange and Cauchy–Binet identities are available.

* **THE INFORMATIVE BRACKET BUDGET** (`corner_informative_bracket_budget`,
  closed form `corner_informative_bracket_budget_closed`):

    `(1+λ)·Σ_{{d,d'}⊂Cᶜ} t_dt_{d'}[x d d']²
       = (1 + e_x + e_y − t_z(1+λ))·(1 + e_x + e_z − t_y(1+λ)) − e_ye_z` .

  The Lagrange defect of the two anchored families at base `x` IS the weighted
  informative bracket mass at that base, through the landed bracket bridge.
  The corner owns a fixed amount of informative bracket, and it is a polynomial
  in seven scalars.

* **THE OUTSIDE GRAM DETERMINANT** (`corner_outside_gram_det`,
  `corner_outside_gram_det_nonneg`):  Cauchy–Binet at three slots turns the
  determinant of that Gram into `t₄t₅t₆` times a square, so

    `A_xy·A_xz·A_yz ≥ 2e_xe_ye_z + A_xy e_xe_y + A_xz e_xe_z + A_yz e_ye_z`

  at EVERY corank-two corner, with the defect exactly the squared bracket
  determinant of the complement.

The payoff is `corner_oppositePair_budget_bound`: the opposite-sign floor and
the budget collide in pure corner scalars,

  `4·t_dt_{d'}·|M^x_d|·|M^x_{d'}| ≤ A_xy·A_xz − P_yz²` ,

and by `Gtz.corner_generic_two_oppositePairs` this fires at TWO distinct inside
bases (`corner_two_oppositePair_budget_bounds`).  That is the first quantitative
real-only law of the opposite horn: over `ℂ` the same bracket bridge only gives
the difference of the two minor magnitudes, and the factor four is lost.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. Two three-slot algebra identities -/

/-- **LAGRANGE AT THREE WEIGHTED SLOTS.**  The Cauchy–Schwarz defect of two
weighted three-slot families is the weighted sum of their squared `2×2`
minors. -/
theorem lagrange_three (t1 t2 t3 a1 a2 a3 b1 b2 b3 : ℝ) :
    (t1 * a1 ^ 2 + t2 * a2 ^ 2 + t3 * a3 ^ 2)
        * (t1 * b1 ^ 2 + t2 * b2 ^ 2 + t3 * b3 ^ 2)
      - (t1 * (a1 * b1) + t2 * (a2 * b2) + t3 * (a3 * b3)) ^ 2
      = t1 * t2 * (a1 * b2 - a2 * b1) ^ 2
        + t1 * t3 * (a1 * b3 - a3 * b1) ^ 2
        + t2 * t3 * (a2 * b3 - a3 * b2) ^ 2 := by
  ring

/-- **CAUCHY–BINET AT THREE WEIGHTED SLOTS.**  The determinant of the weighted
Gram of three three-slot families is the weight product times the squared
determinant of the family matrix. -/
theorem det_weightedGram_three {t1 t2 t3 a1 a2 a3 b1 b2 b3 c1 c2 c3
    g11 g22 g33 g12 g13 g23 : ℝ}
    (h11 : g11 = t1 * a1 ^ 2 + t2 * a2 ^ 2 + t3 * a3 ^ 2)
    (h22 : g22 = t1 * b1 ^ 2 + t2 * b2 ^ 2 + t3 * b3 ^ 2)
    (h33 : g33 = t1 * c1 ^ 2 + t2 * c2 ^ 2 + t3 * c3 ^ 2)
    (h12 : g12 = t1 * (a1 * b1) + t2 * (a2 * b2) + t3 * (a3 * b3))
    (h13 : g13 = t1 * (a1 * c1) + t2 * (a2 * c2) + t3 * (a3 * c3))
    (h23 : g23 = t1 * (b1 * c1) + t2 * (b2 * c2) + t3 * (b3 * c3)) :
    g11 * g22 * g33 + 2 * (g12 * g13 * g23)
        - g11 * g23 ^ 2 - g22 * g13 ^ 2 - g33 * g12 ^ 2
      = t1 * t2 * t3
        * (a1 * (b2 * c3 - b3 * c2) - a2 * (b1 * c3 - b3 * c1)
          + a3 * (b1 * c2 - b2 * c1)) ^ 2 := by
  subst h11; subst h22; subst h33; subst h12; subst h13; subst h23
  ring

/-- Swapping the two anchor slots negates an anchored bracket. -/
theorem atomBracket_swapLeft_neg (D : WeightedDesign m 3) (a b c : Fin m) :
    atomBracket D b a c = -atomBracket D a b c := by
  simp only [atomBracket]
  exact tripleBracket_swapLeft (D.atom b) (D.atom a) (D.atom c)

/-! ## 2. The outside bracket Gram of a corner -/

/-- The pairing of an atom with itself is one plus its heavy excess. -/
theorem atomPairing_self_eq (D : WeightedDesign m 3) (a : Fin m) :
    atomPairing D a a = 1 + heavyExcess D a := by
  simp only [atomPairing, heavyExcess, leverageOf_eq_dotProduct]
  ring

/-- **THE DIAGONAL OF THE OUTSIDE BRACKET GRAM.**  The weighted square mass of
one anchored bracket family over the complement is a corner scalar:

  `Σ_{d ∈ Cᶜ} t_d·[x y d]² = 1 + e_x + e_y − t_z(1+λ)` .

Parseval supplies the total, the inside slots contribute only the dominator
bracket, and the rank-one gap turns the pair minor into the excess product. -/
theorem corner_compl_bracket_sq_sum (D : WeightedDesign m 3) {x y z : Fin m}
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d * atomBracket D x y d ^ 2
      = 1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam) := by
  classical
  have hcard : ({x, y, z} : Finset (Fin m)).card = 3 := card_triple_eq hxy hxz hyz
  have hx : x ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hy : y ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have htotal := sum_weight_bracket_transport D x y y
  have hzero : ∑ a ∈ ({x, y, z} : Finset (Fin m)),
      D.weight a * (atomBracket D x y a * atomBracket D x y a)
      = D.weight z * atomBracket D x y z ^ 2 := by
    rw [sum_triple_eq hxy hxz hyz, atomBracket_right_eq_left,
      atomBracket_right_eq_mid]
    ring
  have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin m))
    (fun a => D.weight a * (atomBracket D x y a * atomBracket D x y a))
  rw [hzero, htotal] at hsplit
  have hconv : ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight d * atomBracket D x y d ^ 2
      = ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d * (atomBracket D x y d * atomBracket D x y d) :=
    Finset.sum_congr rfl fun d _ => by ring
  have hminor := corner_inside_pairMinor_eq_zero D ({x, y, z} : Finset (Fin m))
    hcard hlam hunit hgap hx hy hxy
  have hbr := corner_atomBracket_sq D hxy hxz hyz hlam hunit hgap
  have hlev : leverageOf (D.atom x) = 1 + heavyExcess D x := by
    simp only [heavyExcess]; ring
  have hPyy := atomPairing_self_eq D y
  rw [hconv]
  have hgoal : D.weight z * atomBracket D x y z ^ 2
      + ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d * (atomBracket D x y d * atomBracket D x y d)
      = leverageOf (D.atom x) * atomPairing D y y
        - atomPairing D x y * atomPairing D x y := hsplit
  rw [hPyy, hlev, hbr] at hgoal
  have hsq : atomPairing D x y * atomPairing D x y
      = heavyExcess D x * heavyExcess D y := by
    linear_combination -hminor
  rw [hsq] at hgoal
  linarith [hgoal]

/-- **THE `x`-MIXED ENTRY.**  `Σ_{d ∈ Cᶜ} t_d·[x y d]·[y z d] = −P_xz`. -/
theorem corner_compl_bracket_mixed_xy (D : WeightedDesign m 3) {x y z : Fin m}
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d * (atomBracket D x y d * atomBracket D y z d)
      = -atomPairing D x z := by
  classical
  have hcard : ({x, y, z} : Finset (Fin m)).card = 3 := card_triple_eq hxy hxz hyz
  have hx : x ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hy : y ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hz : z ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have htotal := sum_weight_bracket_transport D y x z
  have hflip : ∀ a : Fin m, D.weight a * (atomBracket D y x a * atomBracket D y z a)
      = -(D.weight a * (atomBracket D x y a * atomBracket D y z a)) := by
    intro a
    rw [atomBracket_swapLeft_neg D x y a]
    ring
  have hzero : ∑ a ∈ ({x, y, z} : Finset (Fin m)),
      D.weight a * (atomBracket D y x a * atomBracket D y z a) = 0 := by
    rw [sum_triple_eq hxy hxz hyz]
    simp [atomBracket_right_eq_left, atomBracket_right_eq_mid]
  have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin m))
    (fun a => D.weight a * (atomBracket D y x a * atomBracket D y z a))
  rw [hzero, htotal, zero_add] at hsplit
  have hcompl : ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight d * (atomBracket D y x d * atomBracket D y z d)
      = -∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d * (atomBracket D x y d * atomBracket D y z d) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun d _ => hflip d
  rw [hcompl] at hsplit
  have hmul := corner_heavyExcess_mul_pairing D ({x, y, z} : Finset (Fin m))
    hcard hlam hunit hgap hy hx hz (Ne.symm hxy) hyz hxz
  have hlev : leverageOf (D.atom y) = 1 + heavyExcess D y := by
    simp only [heavyExcess]; ring
  have hyx : atomPairing D y x = atomPairing D x y := atomPairing_comm D y x
  rw [hlev, hyx] at hsplit
  rw [hyx] at hmul
  linarith [hsplit, hmul]

/-- **THE `z`-MIXED ENTRY.**  `Σ_{d ∈ Cᶜ} t_d·[x z d]·[y z d] = P_xy`. -/
theorem corner_compl_bracket_mixed_xz (D : WeightedDesign m 3) {x y z : Fin m}
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d * (atomBracket D x z d * atomBracket D y z d)
      = atomPairing D x y := by
  classical
  have hcard : ({x, y, z} : Finset (Fin m)).card = 3 := card_triple_eq hxy hxz hyz
  have hx : x ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hy : y ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hz : z ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have htotal := sum_weight_bracket_transport D z x y
  have hflip : ∀ a : Fin m, D.weight a * (atomBracket D z x a * atomBracket D z y a)
      = D.weight a * (atomBracket D x z a * atomBracket D y z a) := by
    intro a
    rw [atomBracket_swapLeft_neg D x z a, atomBracket_swapLeft_neg D y z a]
    ring
  have hzero : ∑ a ∈ ({x, y, z} : Finset (Fin m)),
      D.weight a * (atomBracket D z x a * atomBracket D z y a) = 0 := by
    rw [sum_triple_eq hxy hxz hyz]
    simp [atomBracket_right_eq_left, atomBracket_right_eq_mid]
  have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin m))
    (fun a => D.weight a * (atomBracket D z x a * atomBracket D z y a))
  rw [hzero, htotal, zero_add] at hsplit
  have hcompl : ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight d * (atomBracket D z x d * atomBracket D z y d)
      = ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d * (atomBracket D x z d * atomBracket D y z d) :=
    Finset.sum_congr rfl fun d _ => hflip d
  rw [hcompl] at hsplit
  have hmul := corner_heavyExcess_mul_pairing D ({x, y, z} : Finset (Fin m))
    hcard hlam hunit hgap hz hx hy (Ne.symm hxz) (Ne.symm hyz) hxy
  have hlev : leverageOf (D.atom z) = 1 + heavyExcess D z := by
    simp only [heavyExcess]; ring
  have hzx : atomPairing D z x = atomPairing D x z := atomPairing_comm D z x
  have hzy : atomPairing D z y = atomPairing D y z := atomPairing_comm D z y
  rw [hlev, hzx, hzy] at hsplit
  rw [hzx, hzy] at hmul
  linarith [hsplit, hmul]

/-! ## 3. The informative bracket budget at `(6,3)` -/

/-- **THE INFORMATIVE BRACKET BUDGET.**  At `(6,3)` the weighted informative
bracket mass of one inside base is the Lagrange defect of the two anchored
families at that base:

  `(1+λ)·Σ_{{d,d'}⊂Cᶜ} t_dt_{d'}[x d d']² = A_xy·A_xz − P_yz²` .

Each squared informative bracket is a squared `2×2` minor of the two families
through the landed bracket bridge, and Lagrange totals the minors. -/
theorem corner_informative_bracket_budget (D : WeightedDesign 6 3)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    {x y z d4 d5 d6 : Fin 6}
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ) = {d4, d5, d6}) :
    (1 + lam) * (D.weight d4 * D.weight d5 * atomBracket D x d4 d5 ^ 2
        + D.weight d4 * D.weight d6 * atomBracket D x d4 d6 ^ 2
        + D.weight d5 * D.weight d6 * atomBracket D x d5 d6 ^ 2)
      = (∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
            D.weight d * atomBracket D x y d ^ 2)
          * (∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
            D.weight d * atomBracket D x z d ^ 2)
        - atomPairing D y z ^ 2 := by
  classical
  have hd4 : d4 ∉ ({d5, d6} : Finset (Fin 6)) := by simp [h45, h46]
  have hd5 : d5 ∉ ({d6} : Finset (Fin 6)) := by simp [h56]
  have hexp : ∀ f : Fin 6 → ℝ,
      ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), f d = f d4 + f d5 + f d6 := by
    intro f
    rw [hcompl, Finset.sum_insert hd4, Finset.sum_insert hd5,
      Finset.sum_singleton, add_assoc]
  have htrans := corner_compl_bracket_transport D ({x, y, z} : Finset (Fin 6))
    hlam hunit hgap rfl hxy hxz hyz
  rw [hexp] at htrans
  rw [hexp (fun d => D.weight d * atomBracket D x y d ^ 2),
    hexp (fun d => D.weight d * atomBracket D x z d ^ 2)]
  have hbr45 := corner_bracket_bridge D hxy hxz hyz hlam hunit hgap d4 d5
  have hbr46 := corner_bracket_bridge D hxy hxz hyz hlam hunit hgap d4 d6
  have hbr56 := corner_bracket_bridge D hxy hxz hyz hlam hunit hgap d5 d6
  have hlag := lagrange_three (D.weight d4) (D.weight d5) (D.weight d6)
    (atomBracket D x y d4) (atomBracket D x y d5) (atomBracket D x y d6)
    (atomBracket D x z d4) (atomBracket D x z d5) (atomBracket D x z d6)
  rw [← htrans]
  linear_combination -hlag + D.weight d4 * D.weight d5 * hbr45
    + D.weight d4 * D.weight d6 * hbr46 + D.weight d5 * D.weight d6 * hbr56

/-- **THE BUDGET IN CLOSED FORM.**  The informative bracket mass of a base is a
polynomial in the three heavy excesses, the three inside weights and the corner
scale. -/
theorem corner_informative_bracket_budget_closed (D : WeightedDesign 6 3)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    {x y z d4 d5 d6 : Fin 6}
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ) = {d4, d5, d6}) :
    (1 + lam) * (D.weight d4 * D.weight d5 * atomBracket D x d4 d5 ^ 2
        + D.weight d4 * D.weight d6 * atomBracket D x d4 d6 ^ 2
        + D.weight d5 * D.weight d6 * atomBracket D x d5 d6 ^ 2)
      = (1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam))
          * (1 + heavyExcess D x + heavyExcess D z - D.weight y * (1 + lam))
        - heavyExcess D y * heavyExcess D z := by
  have hbud := corner_informative_bracket_budget D hlam hunit hgap hxy hxz hyz
    h45 h46 h56 hcompl
  have hAxy := corner_compl_bracket_sq_sum D hlam hunit hgap hxy hxz hyz
  have hgapXZ : subsetSum D ({x, z, y} : Finset (Fin 6)) - 1
      = lam • atomMatrix u := by
    rw [show ({x, z, y} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
    exact hgap
  have hAxz := corner_compl_bracket_sq_sum D hlam hunit hgapXZ hxz hxy
    (Ne.symm hyz)
  have hcomplXZ : (({x, z, y} : Finset (Fin 6))ᶜ) = (({x, y, z} : Finset (Fin 6))ᶜ) := by
    rw [show ({x, z, y} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
  rw [hcomplXZ] at hAxz
  have hminor := corner_inside_pairMinor_eq_zero D ({x, y, z} : Finset (Fin 6))
    (card_triple_eq hxy hxz hyz) hlam hunit hgap (by simp) (by simp) hyz
  rw [hAxy, hAxz] at hbud
  linear_combination hbud + hminor

/-! ## 4. The outside Gram determinant -/

/-- **THE OUTSIDE GRAM DETERMINANT.**  Cauchy–Binet at the three complement
slots turns the determinant of the outside bracket Gram into the weight product
times a square. -/
theorem corner_outside_gram_det (D : WeightedDesign 6 3)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    {x y z d4 d5 d6 : Fin 6}
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ) = {d4, d5, d6}) :
    (1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam))
        * (1 + heavyExcess D x + heavyExcess D z - D.weight y * (1 + lam))
        * (1 + heavyExcess D y + heavyExcess D z - D.weight x * (1 + lam))
      - 2 * (heavyExcess D x * heavyExcess D y * heavyExcess D z)
      - (1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam))
        * (heavyExcess D x * heavyExcess D y)
      - (1 + heavyExcess D x + heavyExcess D z - D.weight y * (1 + lam))
        * (heavyExcess D x * heavyExcess D z)
      - (1 + heavyExcess D y + heavyExcess D z - D.weight x * (1 + lam))
        * (heavyExcess D y * heavyExcess D z)
      = D.weight d4 * D.weight d5 * D.weight d6
        * (atomBracket D x y d4
              * (atomBracket D x z d5 * atomBracket D y z d6
                - atomBracket D x z d6 * atomBracket D y z d5)
            - atomBracket D x y d5
              * (atomBracket D x z d4 * atomBracket D y z d6
                - atomBracket D x z d6 * atomBracket D y z d4)
            + atomBracket D x y d6
              * (atomBracket D x z d4 * atomBracket D y z d5
                - atomBracket D x z d5 * atomBracket D y z d4)) ^ 2 := by
  classical
  have hd4 : d4 ∉ ({d5, d6} : Finset (Fin 6)) := by simp [h45, h46]
  have hd5 : d5 ∉ ({d6} : Finset (Fin 6)) := by simp [h56]
  have hexp : ∀ f : Fin 6 → ℝ,
      ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), f d = f d4 + f d5 + f d6 := by
    intro f
    rw [hcompl, Finset.sum_insert hd4, Finset.sum_insert hd5,
      Finset.sum_singleton, add_assoc]
  -- the six Gram entries
  have hgapXZ : subsetSum D ({x, z, y} : Finset (Fin 6)) - 1
      = lam • atomMatrix u := by
    rw [show ({x, z, y} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
    exact hgap
  have hgapYZ : subsetSum D ({y, z, x} : Finset (Fin 6)) - 1
      = lam • atomMatrix u := by
    rw [show ({y, z, x} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
    exact hgap
  have hcomplXZ : (({x, z, y} : Finset (Fin 6))ᶜ)
      = (({x, y, z} : Finset (Fin 6))ᶜ) := by
    rw [show ({x, z, y} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
  have hcomplYZ : (({y, z, x} : Finset (Fin 6))ᶜ)
      = (({x, y, z} : Finset (Fin 6))ᶜ) := by
    rw [show ({y, z, x} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
  have hAxy := corner_compl_bracket_sq_sum D hlam hunit hgap hxy hxz hyz
  have hAxz := corner_compl_bracket_sq_sum D hlam hunit hgapXZ hxz hxy
    (Ne.symm hyz)
  have hAyz := corner_compl_bracket_sq_sum D hlam hunit hgapYZ hyz
    (Ne.symm hxy) (Ne.symm hxz)
  rw [hcomplXZ] at hAxz
  rw [hcomplYZ] at hAyz
  have htrans := corner_compl_bracket_transport D ({x, y, z} : Finset (Fin 6))
    hlam hunit hgap rfl hxy hxz hyz
  have hmixXY := corner_compl_bracket_mixed_xy D hlam hunit hgap hxy hxz hyz
  have hmixXZ := corner_compl_bracket_mixed_xz D hlam hunit hgap hxy hxz hyz
  rw [hexp] at hAxy hAxz hAyz htrans hmixXY hmixXZ
  -- the pair minors of the rank-one gap
  have hcard : ({x, y, z} : Finset (Fin 6)).card = 3 := card_triple_eq hxy hxz hyz
  have hmXY := corner_inside_pairMinor_eq_zero D ({x, y, z} : Finset (Fin 6))
    hcard hlam hunit hgap (by simp) (by simp) hxy
  have hmXZ := corner_inside_pairMinor_eq_zero D ({x, y, z} : Finset (Fin 6))
    hcard hlam hunit hgap (by simp) (by simp) hxz
  have hmYZ := corner_inside_pairMinor_eq_zero D ({x, y, z} : Finset (Fin 6))
    hcard hlam hunit hgap (by simp) (by simp) hyz
  have hmul := corner_heavyExcess_mul_pairing D ({x, y, z} : Finset (Fin 6))
    hcard hlam hunit hgap (by simp) (by simp) (by simp) hxy hxz hyz
  have hcb := det_weightedGram_three (t1 := D.weight d4) (t2 := D.weight d5)
    (t3 := D.weight d6)
    (a1 := atomBracket D x y d4) (a2 := atomBracket D x y d5)
    (a3 := atomBracket D x y d6)
    (b1 := atomBracket D x z d4) (b2 := atomBracket D x z d5)
    (b3 := atomBracket D x z d6)
    (c1 := atomBracket D y z d4) (c2 := atomBracket D y z d5)
    (c3 := atomBracket D y z d6)
    hAxy.symm hAxz.symm hAyz.symm htrans.symm hmixXY.symm hmixXZ.symm
  -- the triple product of pairings is the product of the excesses
  have htriple : atomPairing D x y * atomPairing D x z * atomPairing D y z
      = heavyExcess D x * heavyExcess D y * heavyExcess D z := by
    have h1 : heavyExcess D x * atomPairing D y z ^ 2
        = atomPairing D x y * atomPairing D x z * atomPairing D y z := by
      rw [← hmul]; ring
    rw [← h1, ← hmYZ]; ring
  linear_combination hcb
    - (1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam)) * hmXY
    - (1 + heavyExcess D x + heavyExcess D z - D.weight y * (1 + lam)) * hmXZ
    - (1 + heavyExcess D y + heavyExcess D z - D.weight x * (1 + lam)) * hmYZ
    + 2 * htriple

/-- **THE OUTSIDE GRAM INEQUALITY.**  Every corank-two corner of a `(6,3)`
design obeys a cubic inequality in its three heavy excesses, its three inside
weights and its scale, with equality exactly when the complement triple is
coplanar. -/
theorem corner_outside_gram_det_nonneg (D : WeightedDesign 6 3)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    {x y z d4 d5 d6 : Fin 6}
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ) = {d4, d5, d6}) :
    2 * (heavyExcess D x * heavyExcess D y * heavyExcess D z)
        + (1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam))
          * (heavyExcess D x * heavyExcess D y)
        + (1 + heavyExcess D x + heavyExcess D z - D.weight y * (1 + lam))
          * (heavyExcess D x * heavyExcess D z)
        + (1 + heavyExcess D y + heavyExcess D z - D.weight x * (1 + lam))
          * (heavyExcess D y * heavyExcess D z)
      ≤ (1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam))
        * (1 + heavyExcess D x + heavyExcess D z - D.weight y * (1 + lam))
        * (1 + heavyExcess D y + heavyExcess D z - D.weight x * (1 + lam)) := by
  have hdet := corner_outside_gram_det D hlam hunit hgap hxy hxz hyz h45 h46 h56
    hcompl
  have hpos : 0 ≤ D.weight d4 * D.weight d5 * D.weight d6
      * (atomBracket D x y d4
            * (atomBracket D x z d5 * atomBracket D y z d6
              - atomBracket D x z d6 * atomBracket D y z d5)
          - atomBracket D x y d5
            * (atomBracket D x z d4 * atomBracket D y z d6
              - atomBracket D x z d6 * atomBracket D y z d4)
          + atomBracket D x y d6
            * (atomBracket D x z d4 * atomBracket D y z d5
              - atomBracket D x z d5 * atomBracket D y z d4)) ^ 2 := by
    have h4 := D.weight_pos d4
    have h5 := D.weight_pos d5
    have h6 := D.weight_pos d6
    positivity
  linarith [hdet, hpos]

/-! ## 5. The floor–budget collision -/

/-- One informative pair never exceeds the whole budget of its base. -/
theorem corner_informative_pair_le_budget (D : WeightedDesign 6 3)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    {x y z d4 d5 d6 : Fin 6}
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ) = {d4, d5, d6}) :
    (1 + lam) * (D.weight d4 * D.weight d5 * atomBracket D x d4 d5 ^ 2)
      ≤ (1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam))
          * (1 + heavyExcess D x + heavyExcess D z - D.weight y * (1 + lam))
        - heavyExcess D y * heavyExcess D z := by
  have hbud := corner_informative_bracket_budget_closed D hlam hunit hgap
    hxy hxz hyz h45 h46 h56 hcompl
  have h46' : 0 ≤ D.weight d4 * D.weight d6 * atomBracket D x d4 d6 ^ 2 := by
    have := D.weight_pos d4
    have := D.weight_pos d6
    positivity
  have h56' : 0 ≤ D.weight d5 * D.weight d6 * atomBracket D x d5 d6 ^ 2 := by
    have := D.weight_pos d5
    have := D.weight_pos d6
    positivity
  nlinarith [hbud, h46', h56', hlam]

/-- **THE FLOOR–BUDGET COLLISION.**  An opposite-sign pair of outside mixed
minors at an inside base is priced by the budget of that base, in pure corner
scalars:

  `4·t_dt_{d'}·|M^x_d|·|M^x_{d'}| ≤ A_xy·A_xz − P_yz²` .

The left side is real-only — over `ℂ` the bracket bridge gives only the
DIFFERENCE of the two minor magnitudes and the factor four collapses — and the
right side is a polynomial in the corner scalars. -/
theorem corner_oppositePair_budget_bound (D : WeightedDesign 6 3)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    {x y z d4 d5 d6 : Fin 6}
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ) = {d4, d5, d6})
    (hsign : (atomBracket D x y d4 * atomBracket D x z d4)
      * (atomBracket D x y d5 * atomBracket D x z d5) < 0) :
    4 * (D.weight d4 * D.weight d5)
        * (|atomBracket D x y d4 * atomBracket D x z d4|
          * |atomBracket D x y d5 * atomBracket D x z d5|)
      ≤ (1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam))
          * (1 + heavyExcess D x + heavyExcess D z - D.weight y * (1 + lam))
        - heavyExcess D y * heavyExcess D z := by
  have hfloor := corner_oppositePair_bracket_floor D hxy hxz hyz hlam hunit hgap
    hsign
  have hpair := corner_informative_pair_le_budget D hlam hunit hgap hxy hxz hyz
    h45 h46 h56 hcompl
  have hw : 0 < D.weight d4 * D.weight d5 :=
    mul_pos (D.weight_pos d4) (D.weight_pos d5)
  have h1 := mul_le_mul_of_nonneg_left hfloor hw.le
  have h2 : 4 * (D.weight d4 * D.weight d5)
      * (|atomBracket D x y d4 * atomBracket D x z d4|
        * |atomBracket D x y d5 * atomBracket D x z d5|)
      ≤ (1 + lam) * (D.weight d4 * D.weight d5
        * atomBracket D x d4 d5 ^ 2) := by nlinarith [h1]
  linarith [h2, hpair]

/-- **THE COUNT AND THE BUDGET TOGETHER.**  A corank-two corner with
nondegenerate inside pairings and bracket-generic outside atoms pays the
floor–budget price at TWO distinct inside bases: the count law
`Gtz.corner_generic_two_oppositePairs` supplies two opposite-sign pairs at
different bases, and each is capped by its own budget. -/
theorem corner_two_oppositePair_budget_bounds (D : WeightedDesign 6 3)
    (C : Finset (Fin 6))
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    {x y z : Fin 6} (hC : C = ({x, y, z} : Finset (Fin 6)))
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hPyz : atomPairing D y z ≠ 0) (hPxz : atomPairing D x z ≠ 0)
    (hPxy : atomPairing D x y ≠ 0)
    (hgen : ∀ d ∈ Cᶜ, atomBracket D x y d * atomBracket D x z d
      * atomBracket D y z d ≠ 0) :
    ∃ e ∈ C, ∃ e' ∈ C, e ≠ e'
      ∧ (∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ, d ≠ d'
          ∧ 0 < (1 + lam) * atomBracket D e d d' ^ 2)
      ∧ (∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ, d ≠ d'
          ∧ 0 < (1 + lam) * atomBracket D e' d d' ^ 2) :=
  corner_two_informative_bracket_floors D C hlam hunit hgap hC hxy hxz hyz
    hPyz hPxz hPxy hgen

end Gtz
