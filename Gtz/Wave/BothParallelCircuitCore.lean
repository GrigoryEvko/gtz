import Gtz.Wave.SupportTwoClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The both-parallel circuit core — the scalar certificate chain

The circuit branch of closure five carries a positive label alive at
exactly the two single atoms.  This module lands the full scalar
certificate as pure real lemmas.  The datum module instantiates each
hypothesis from the landed projection laws.

The chain:

1. The circuit tight rows price the cross entry and balance the masses.
2. The signed components collapse the idempotency entries.
3. The row squares and the cross entry price the pair leak.
4. A zero leak kills both shifted diagonals.
5. A nonzero leak forces the claw: the opposite sides align.
6. The single relation, the pair relation, and the cross relation
   combine with the weight sum into an empty weight window.

Entry names: `g1 = gap(a1, b)`, `g2 = gap(a1, d)`, `h1 = gap(b, c1)`,
`h2 = gap(c1, d)`, `gb2 = gap(a2, b)`, `gd2 = gap(a2, d)`,
`hb2 = gap(b, c2)`, `hd2 = gap(c2, d)`, `gbd = gap(b, d)`.  The scalars
`m, n` are the shifted diagonals `gap(b,b) - G, gap(d,d) - G`.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.circuit_scalar_kill` — **THE SCALAR CAPSTONE.**
* `Gtz.circuit_weight_clash` — **THE EMPTY WEIGHT WINDOW.**
* `Gtz.circuit_claw` — **THE OPPOSITE-SIDE ALIGNMENT.**
* `Gtz.circuit_newone_scalar`, `Gtz.circuit_spade_scalar`,
  `Gtz.circuit_cross_scalar` — the three scalar relations.

## Vacuity

The lemmas are unconditional real arithmetic.
-/

namespace Gtz

/-! ## Layer 1 — the circuit row prices -/

/-- The two circuit tight rows price the squared cross entry as the
product of the two shifted diagonals. -/
theorem circuit_cross_sq {mB nD gbd eb ed : ℝ}
    (hR1 : mB * eb + gbd * ed = 0) (hR2 : gbd * eb + nD * ed = 0)
    (hed : ed ≠ 0) :
    gbd ^ 2 = mB * nD := by
  have hcancel : (gbd ^ 2 - mB * nD) * ed = 0 := by
    linear_combination gbd * hR1 - mB * hR2
  rcases mul_eq_zero.mp hcancel with hcase | hcase
  · linarith [hcase]
  · exact absurd hcase hed

/-- The two circuit tight rows balance the two coordinate masses. -/
theorem circuit_kappa {mB nD gbd eb ed : ℝ}
    (hR1 : mB * eb + gbd * ed = 0) (hR2 : gbd * eb + nD * ed = 0) :
    mB * eb ^ 2 = nD * ed ^ 2 := by
  linear_combination eb * hR1 - ed * hR2

/-- The cross entry is nonzero on the circuit branch. -/
theorem circuit_gbd_ne_zero {mB gbd eb ed : ℝ}
    (hR1 : mB * eb + gbd * ed = 0)
    (hmB : 0 < mB) (heb : eb ≠ 0) :
    gbd ≠ 0 := by
  intro hzero
  rw [hzero] at hR1
  have hprod : mB * eb = 0 := by linarith
  rcases mul_eq_zero.mp hprod with hcase | hcase
  · exact absurd hcase (ne_of_gt hmB)
  · exact absurd hcase heb

/-! ## Layer 2 — the sign extraction -/

/-- Equal squares split into a sign: the second value is a unit multiple
of the first. -/
theorem sign_of_sq_eq {x y : ℝ} (hsq : x ^ 2 = y ^ 2) :
    ∃ signVal : ℝ, signVal ^ 2 = 1 ∧ y = signVal * x := by
  have hcancel : (y - x) * (y + x) = 0 := by linear_combination -hsq
  rcases mul_eq_zero.mp hcancel with hcase | hcase
  · exact ⟨1, by norm_num, by linarith⟩
  · exact ⟨-1, by norm_num, by linarith⟩

/-! ## Layer 3 — the leak price -/

/-- **THE LEAK PRICE.**  The collapsed row square, the collapsed cross
entry, the annihilated third row, and the circuit tight row price the
pair leak through the shifted diagonals.  The same lemma serves the
second single atom with the roles swapped. -/
theorem circuit_leak_price {mB nD G wb wd : ℝ}
    {g1 g2 h1 h2 gbd eb ed : ℝ}
    (hRS : 2 * g1 ^ 2 + 2 * h1 ^ 2 + gbd ^ 2
      = (mB + G + wb) * (1 - (mB + G + wb)))
    (hX0 : 2 * g1 * g2 + 2 * h1 * h2
      = gbd * (1 - (mB + G + wb) - (nD + G + wd)))
    (hZ : g1 * eb + g2 * ed = 0)
    (hR1 : mB * eb + gbd * ed = 0)
    (hSq : gbd ^ 2 = mB * nD) :
    2 * h1 * (h1 * eb + h2 * ed)
      = eb * ((G + wb) * (1 - mB - G - wb) + mB * (G + wd)) := by
  linear_combination eb * hRS + ed * hX0 - 2 * g1 * hZ
    + (1 - (mB + G + wb) - (nD + G + wd)) * hR1 - eb * hSq

/-- The diagonal window: the row square with a positive cross product
pins the diagonal entry strictly inside the unit interval. -/
theorem circuit_diag_window {mB nD G wb : ℝ} {g1 h1 gbd : ℝ}
    (hRS : 2 * g1 ^ 2 + 2 * h1 ^ 2 + gbd ^ 2
      = (mB + G + wb) * (1 - (mB + G + wb)))
    (hSq : gbd ^ 2 = mB * nD) (hmB : 0 < mB) (hnD : 0 < nD) :
    0 < mB + G + wb ∧ mB + G + wb < 1 := by
  have hpos : 0 < (mB + G + wb) * (1 - (mB + G + wb)) := by
    nlinarith [sq_nonneg g1, sq_nonneg h1, mul_pos hmB hnD]
  constructor
  · nlinarith [hpos]
  · nlinarith [hpos]

/-- **THE ZERO-LEAK COLLAPSE.**  A vanishing leak kills both shifted
weights: the leak price degenerates, and the sign structure refuses
every other exit. -/
theorem circuit_zero_leak {mB G wb wd : ℝ} {h1 h2 eb ed : ℝ}
    (hprice : 2 * h1 * (h1 * eb + h2 * ed)
      = eb * ((G + wb) * (1 - mB - G - wb) + mB * (G + wd)))
    (htau : h1 * eb + h2 * ed = 0) (heb : eb ≠ 0)
    (hdb : 0 ≤ G + wb) (hdd : 0 ≤ G + wd) (hmB : 0 < mB)
    (hPbb : mB + G + wb < 1) :
    G + wb = 0 ∧ G + wd = 0 := by
  rw [htau, mul_zero] at hprice
  have hbracket : (G + wb) * (1 - mB - G - wb) + mB * (G + wd) = 0 := by
    rcases mul_eq_zero.mp hprice.symm with hcase | hcase
    · exact absurd hcase heb
    · exact hcase
  have hone : 0 ≤ (G + wb) * (1 - mB - G - wb) :=
    mul_nonneg hdb (by linarith)
  have htwo : 0 ≤ mB * (G + wd) := mul_nonneg hmB.le hdd
  have hdd0 : G + wd = 0 := by
    have hzero : mB * (G + wd) = 0 := by linarith
    rcases mul_eq_zero.mp hzero with hcase | hcase
    · exact absurd hcase (ne_of_gt hmB)
    · exact hcase
  refine ⟨?_, hdd0⟩
  have hzero : (G + wb) * (1 - mB - G - wb) = 0 := by
    rw [hdd0, mul_zero] at hbracket
    linarith
  rcases mul_eq_zero.mp hzero with hcase | hcase
  · exact hcase
  · linarith

/-! ## Layer 4 — the claw -/

/-- **THE CLAW.**  A nonzero leak aligns the opposite-side coordinates:
the two leak prices eliminate the leak, the scale balance and the mass
balance square the comparison, and the sign windows resolve the root. -/
theorem circuit_claw {mB nD G wb wd : ℝ}
    {h1 h2 eb ed c1 d1 cB dD : ℝ}
    (hpriceB : 2 * h1 * (h1 * eb + h2 * ed)
      = eb * ((G + wb) * (1 - mB - G - wb) + mB * (G + wd)))
    (hpriceD : 2 * h2 * (h1 * eb + h2 * ed)
      = ed * ((G + wd) * (1 - nD - G - wd) + nD * (G + wb)))
    (hRowC : 2 * c1 * h1 = -(mB * cB))
    (hRowD : 2 * d1 * h2 = -(nD * dD))
    (hS5 : nD * dD ^ 2 * c1 ^ 2 = mB * cB ^ 2 * d1 ^ 2)
    (hkap : mB * eb ^ 2 = nD * ed ^ 2)
    (hdb : 0 ≤ G + wb) (hdd : 0 ≤ G + wd)
    (hmB : 0 < mB) (hnD : 0 < nD)
    (hPbb : mB + G + wb ≤ 1) (hPdd : nD + G + wd ≤ 1)
    (htau : h1 * eb + h2 * ed ≠ 0)
    (hd1 : d1 ≠ 0) (hcB : cB ≠ 0) (hed : ed ≠ 0) :
    dD * c1 * eb = cB * d1 * ed := by
  set tau := h1 * eb + h2 * ed with htaudef
  set Fb := (G + wb) * (1 - mB - G - wb) + mB * (G + wd) with hFbdef
  set Fd := (G + wd) * (1 - nD - G - wd) + nD * (G + wb) with hFddef
  have hstarB : c1 * eb * Fb = -(mB * cB * tau) := by
    linear_combination tau * hRowC - c1 * hpriceB
  have hstarD : d1 * ed * Fd = -(nD * dD * tau) := by
    linear_combination tau * hRowD - d1 * hpriceD
  have hstst : nD * dD * (c1 * eb * Fb) = mB * cB * (d1 * ed * Fd) := by
    rw [hstarB, hstarD]
    ring
  have hFbSign : 0 ≤ Fb := by
    rw [hFbdef]
    have hone := mul_nonneg hdb (by linarith : (0:ℝ) ≤ 1 - mB - G - wb)
    nlinarith [mul_nonneg hmB.le hdd]
  have hFdSign : 0 ≤ Fd := by
    rw [hFddef]
    have hone := mul_nonneg hdd (by linarith : (0:ℝ) ≤ 1 - nD - G - wd)
    nlinarith [mul_nonneg hnD.le hdb]
  have hFbNe : Fb ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hstarB
    have hprod : mB * cB * tau = 0 := by linarith
    rcases mul_eq_zero.mp hprod with hcase | hcase
    · rcases mul_eq_zero.mp hcase with hcase' | hcase'
      · exact absurd hcase' (ne_of_gt hmB)
      · exact absurd hcase' hcB
    · exact absurd hcase htau
  have hsq : (nD * Fb) ^ 2 = (mB * Fd) ^ 2 := by
    have hone : (nD * dD * (c1 * eb * Fb)) ^ 2
        = (mB * cB * (d1 * ed * Fd)) ^ 2 := by rw [hstst]
    have htwo : mB * (nD * dD * (c1 * eb * Fb)) ^ 2
        = mB * (mB * cB * (d1 * ed * Fd)) ^ 2 := by rw [hone]
    have hthree : nD * ed ^ 2 * (dD ^ 2 * c1 ^ 2) * (nD * Fb) ^ 2
        = mB * (mB * cB * (d1 * ed * Fd)) ^ 2 := by
      linear_combination htwo - dD ^ 2 * c1 ^ 2 * (nD * Fb) ^ 2 * hkap
    have hfour : ed ^ 2 * mB * cB ^ 2 * d1 ^ 2 * (nD * Fb) ^ 2
        = ed ^ 2 * mB * cB ^ 2 * d1 ^ 2 * (mB * Fd) ^ 2 := by
      linear_combination hthree - ed ^ 2 * (nD * Fb) ^ 2 * hS5
    have hfactor : ed ^ 2 * mB * cB ^ 2 * d1 ^ 2 ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hed)
        (ne_of_gt hmB)) (pow_ne_zero 2 hcB)) (pow_ne_zero 2 hd1)
    calc (nD * Fb) ^ 2
        = ed ^ 2 * mB * cB ^ 2 * d1 ^ 2 * (nD * Fb) ^ 2
          / (ed ^ 2 * mB * cB ^ 2 * d1 ^ 2) := by
          field_simp
      _ = ed ^ 2 * mB * cB ^ 2 * d1 ^ 2 * (mB * Fd) ^ 2
          / (ed ^ 2 * mB * cB ^ 2 * d1 ^ 2) := by rw [hfour]
      _ = (mB * Fd) ^ 2 := by field_simp
  have hlin : nD * Fb = mB * Fd := by
    have hprod : (nD * Fb - mB * Fd) * (nD * Fb + mB * Fd) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hprod with hcase | hcase
    · linarith
    · have hbn : 0 ≤ nD * Fb := mul_nonneg hnD.le hFbSign
      have hbm : 0 ≤ mB * Fd := mul_nonneg hmB.le hFdSign
      have hzb : nD * Fb = 0 := by linarith
      have hzm : mB * Fd = 0 := by linarith
      rw [hzb, hzm]
  have hkill : nD * Fb * (dD * c1 * eb - cB * d1 * ed) = 0 := by
    linear_combination hstst - cB * d1 * ed * hlin
  rcases mul_eq_zero.mp hkill with hcase | hcase
  · rcases mul_eq_zero.mp hcase with hcase' | hcase'
    · exact absurd hcase' (ne_of_gt hnD)
    · exact absurd hcase' hFbNe
  · linarith

/-! ## Layer 5 — the single-side pin -/

/-- The annihilated third row pins the fourth coordinate against the
circuit data: the solved form of the same-side pin. -/
theorem circuit_aD_value {mB nD eb ed p1 r1 aD bB : ℝ}
    (hZc : mB * eb * p1 * bB + nD * ed * r1 * aD = 0)
    (hnDv : nD * ed ^ 2 = mB * eb ^ 2)
    (hmB : mB ≠ 0) (heb : eb ≠ 0) :
    aD * eb * r1 = -(p1 * bB * ed) := by
  have hcancel : (aD * eb * r1 + p1 * bB * ed) * (mB * eb) = 0 := by
    linear_combination ed * hZc - r1 * aD * hnDv
  rcases mul_eq_zero.mp hcancel with hcase | hcase
  · linarith
  · rcases mul_eq_zero.mp hcase with hcase' | hcase'
    · exact absurd hcase' hmB
    · exact absurd hcase' heb

/-! ## Layer 6 — the three scalar relations -/

/-- **THE CROSS RELATION.**  The collapsed cross entry with the four row
laws and the solved coordinate values reads the difference of the two
pair excesses. -/
theorem circuit_cross_scalar {mB nD G wb wd : ℝ}
    {g1 g2 h1 h2 gbd : ℝ} {p1 r1 aD bB c1 d1 cB dD eb ed : ℝ}
    (hX0 : 2 * g1 * g2 + 2 * h1 * h2
      = gbd * (1 - (mB + G + wb) - (nD + G + wd)))
    (hRowB : 2 * r1 * g1 = -(mB * bB))
    (hRowA : 2 * p1 * g2 = -(nD * aD))
    (hRowC : 2 * c1 * h1 = -(mB * cB))
    (hRowD : 2 * d1 * h2 = -(nD * dD))
    (hnDv : nD * ed ^ 2 = mB * eb ^ 2)
    (hgbd : gbd * ed = -(mB * eb))
    (haD : aD * eb * r1 = -(p1 * bB * ed))
    (hdD : dD * c1 * eb = cB * d1 * ed)
    (hp1 : p1 ≠ 0) (hd1 : d1 ≠ 0) (heb : eb ≠ 0) (hmB : mB ≠ 0) :
    mB * (c1 ^ 2 * bB ^ 2 - r1 ^ 2 * cB ^ 2)
      = 2 * r1 ^ 2 * c1 ^ 2 * (1 - (mB + G + wb) - (nD + G + wd)) := by
  have h4g : 4 * r1 * p1 * (g1 * g2) = mB * bB * (nD * aD) := by
    linear_combination (2 * p1 * g2) * hRowB - mB * bB * hRowA
  have h4h : 4 * c1 * d1 * (h1 * h2) = mB * cB * (nD * dD) := by
    linear_combination (2 * d1 * h2) * hRowC - mB * cB * hRowD
  have hstar : mB * nD * (aD * bB * c1 * d1 + cB * dD * r1 * p1)
      = 2 * r1 * p1 * c1 * d1
        * (gbd * (1 - (mB + G + wb) - (nD + G + wd))) := by
    linear_combination 2 * r1 * p1 * c1 * d1 * hX0 - c1 * d1 * h4g
      - r1 * p1 * h4h
  have hbig : mB * eb ^ 2 * p1 * d1
      * (mB * (c1 ^ 2 * bB ^ 2 - r1 ^ 2 * cB ^ 2)
        - 2 * r1 ^ 2 * c1 ^ 2
          * (1 - (mB + G + wb) - (nD + G + wd))) = 0 := by
    linear_combination (-(eb * r1 * c1 * ed)) * hstar
      + mB * nD * bB * c1 ^ 2 * d1 * ed * haD
      + mB * nD * cB * p1 * r1 ^ 2 * ed * hdD
      - mB * p1 * d1 * (bB ^ 2 * c1 ^ 2 - cB ^ 2 * r1 ^ 2) * hnDv
      - 2 * p1 * r1 ^ 2 * c1 ^ 2 * d1 * eb
        * (1 - (mB + G + wb) - (nD + G + wd)) * hgbd
  have hfac : mB * eb ^ 2 * p1 * d1 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hmB (pow_ne_zero 2 heb)) hp1) hd1
  rcases mul_eq_zero.mp hbig with hcase | hcase
  · exact absurd hcase hfac
  · linarith

/-- **THE SPADE RELATION.**  The two carrier-column idempotency entries
at the first co-pair atom, cleared of the cross block by the signed
components, collapse through the row laws, the branch values, and the
carrier tight row into the co-pair weight relation. -/
theorem circuit_spade_scalar {m n G wb wc1 wd : ℝ}
    {g1 g2 gb2 gd2 h1 h2 hb2 hd2 gbd gcc1 gc12 X11 X21 : ℝ}
    {p1 r1 aD bB c1 c2 d1 cB dD eb ed sa sc : ℝ}
    (hIdmBC1 : g1 * X11 + gb2 * X21 + (m + G + wb) * h1
      + h1 * (gcc1 + wc1) + hb2 * gc12 + gbd * h2 = h1)
    (hIdmC1D : X11 * g2 + X21 * gd2 + h1 * gbd + (gcc1 + wc1) * h2
      + gc12 * hd2 + h2 * (n + G + wd) = h2)
    (hTightC1 : h1 * cB + gcc1 * c1 + gc12 * c2 = G * c1)
    (hRowB : 2 * r1 * g1 = -(m * bB)) (hRowA : 2 * p1 * g2 = -(n * aD))
    (hRowC : 2 * c1 * h1 = -(m * cB)) (hRowD : 2 * d1 * h2 = -(n * dD))
    (hgb2 : gb2 = sa * g1) (hgd2 : gd2 = sa * g2)
    (hhb2 : hb2 = sc * h1) (hhd2 : hd2 = sc * h2) (hc2 : c2 = sc * c1)
    (hR1 : m * eb + gbd * ed = 0) (hR2 : gbd * eb + n * ed = 0)
    (hkap : m * eb ^ 2 = n * ed ^ 2)
    (haD : aD * eb * r1 = -(p1 * bB * ed))
    (hdD : dD * c1 * eb = cB * d1 * ed)
    (hm : 0 < m) (hn : 0 < n)
    (hp1 : p1 ≠ 0) (hbB : bB ≠ 0) (hcB : cB ≠ 0) (hd1 : d1 ≠ 0)
    (heb : eb ≠ 0) (hed : ed ≠ 0) :
    c1 ^ 2 * ((G + wb) + (G + wd) - 2 * (1 - wc1 - G)) + m * cB ^ 2 = 0 := by
  have hcomb : g2 * h1 * ((m + G + wb) + gcc1 + wc1 - 1)
      - g1 * h2 * ((n + G + wd) + gcc1 + wc1 - 1)
      + sc * gc12 * (g2 * h1 - g1 * h2)
      + gbd * (g2 * h2 - g1 * h1) = 0 := by
    linear_combination g2 * hIdmBC1 - g1 * hIdmC1D - g2 * X21 * hgb2
      - g2 * gc12 * hhb2 + g1 * X21 * hgd2 + g1 * gc12 * hhd2
  have hprodStep : m * n * aD * cB * r1 * d1
        * ((m + G + wb) + gcc1 + wc1 - 1)
      - m * n * bB * dD * p1 * c1 * ((n + G + wd) + gcc1 + wc1 - 1)
      + m * n * sc * gc12 * (aD * cB * r1 * d1 - bB * dD * p1 * c1)
      + gbd * (n ^ 2 * aD * dD * r1 * c1
        - m ^ 2 * bB * cB * p1 * d1) = 0 := by
    linear_combination 4 * p1 * r1 * c1 * d1 * hcomb
      - (((m + G + wb) + gcc1 + wc1 - 1) + sc * gc12) * r1 * d1
        * (2 * c1 * h1) * hRowA
      + (((m + G + wb) + gcc1 + wc1 - 1) + sc * gc12) * r1 * d1
        * n * aD * hRowC
      + (((n + G + wd) + gcc1 + wc1 - 1) + sc * gc12) * p1 * c1
        * (2 * d1 * h2) * hRowB
      - (((n + G + wd) + gcc1 + wc1 - 1) + sc * gc12) * p1 * c1
        * m * bB * hRowD
      - gbd * r1 * c1 * (2 * d1 * h2) * hRowA
      + gbd * r1 * c1 * n * aD * hRowD
      + gbd * p1 * d1 * (2 * c1 * h1) * hRowB
      - gbd * p1 * d1 * m * bB * hRowC
  have hbranchStep : m * n * p1 * bB * cB * d1
      * (eb * ed * (((m + G + wb) + gcc1 + wc1 - 1)
          + ((n + G + wd) + gcc1 + wc1 - 1))
        + 2 * sc * gc12 * eb * ed + gbd * (eb ^ 2 + ed ^ 2)) = 0 := by
    linear_combination (-(eb ^ 2)) * hprodStep
      + m * n * cB * d1 * (((m + G + wb) + gcc1 + wc1 - 1) + sc * gc12)
        * eb * haD
      - m * n * bB * p1 * (((n + G + wd) + gcc1 + wc1 - 1) + sc * gc12)
        * eb * hdD
      + gbd * n ^ 2 * (aD * eb * r1) * hdD
      + gbd * n ^ 2 * (cB * d1 * ed) * haD
      - gbd * p1 * bB * cB * d1 * (m - n) * hkap
  have hcoreStep : m * n * p1 * bB * cB * d1 * eb * ed
      * ((((m + G + wb) + gcc1 + wc1 - 1)
          + ((n + G + wd) + gcc1 + wc1 - 1))
        + 2 * sc * gc12 - (m + n)) = 0 := by
    linear_combination hbranchStep
      - m * n * p1 * bB * cB * d1 * (eb * hR2 + ed * hR1)
  have hfac : m * n * p1 * bB * cB * d1 * eb * ed ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (ne_of_gt hm) (ne_of_gt hn)) hp1) hbB)
      hcB) hd1) heb) hed
  have hafter : (((m + G + wb) + gcc1 + wc1 - 1)
      + ((n + G + wd) + gcc1 + wc1 - 1)) + 2 * sc * gc12 - (m + n) = 0 := by
    rcases mul_eq_zero.mp hcoreStep with hcase | hcase
    · exact absurd hcase hfac
    · exact hcase
  linear_combination c1 ^ 2 * hafter - 2 * c1 * hTightC1
    + 2 * c1 * gc12 * hc2 + cB * hRowC

/-- **THE NEW-ONE RELATION.**  The two single-column idempotency entries
at the first pair atom, cleared of the cross block by the signed
components, collapse through the row laws, the branch values, and the
carrier tight row into the pair weight relation. -/
theorem circuit_newone_scalar {m n G wa1 wb wd : ℝ}
    {g1 g2 gb2 gd2 h1 h2 hb2 hd2 gbd gaa1 ga12 X11 X12 : ℝ}
    {p1 r1 r2 aD bB c1 d1 cB dD eb ed sa sc : ℝ}
    (hIdmA1B : (gaa1 + wa1) * g1 + ga12 * gb2 + g1 * (m + G + wb)
      + X11 * h1 + X12 * hb2 + g2 * gbd = g1)
    (hIdmA1D : (gaa1 + wa1) * g2 + ga12 * gd2 + g1 * gbd + X11 * h2
      + X12 * hd2 + g2 * (n + G + wd) = g2)
    (hTightB1 : gaa1 * r1 + ga12 * r2 + g1 * bB = G * r1)
    (hRowB : 2 * r1 * g1 = -(m * bB)) (hRowA : 2 * p1 * g2 = -(n * aD))
    (hRowC : 2 * c1 * h1 = -(m * cB)) (hRowD : 2 * d1 * h2 = -(n * dD))
    (hgb2 : gb2 = sa * g1) (hgd2 : gd2 = sa * g2)
    (hhb2 : hb2 = sc * h1) (hhd2 : hd2 = sc * h2) (hr2 : r2 = sa * r1)
    (hR1 : m * eb + gbd * ed = 0) (hR2 : gbd * eb + n * ed = 0)
    (hkap : m * eb ^ 2 = n * ed ^ 2)
    (haD : aD * eb * r1 = -(p1 * bB * ed))
    (hdD : dD * c1 * eb = cB * d1 * ed)
    (hm : 0 < m) (hn : 0 < n)
    (hp1 : p1 ≠ 0) (hbB : bB ≠ 0) (hcB : cB ≠ 0) (hd1 : d1 ≠ 0)
    (heb : eb ≠ 0) (hed : ed ≠ 0) :
    r1 ^ 2 * (2 * wa1 + 4 * G + 2 * m + 2 * n + wb + wd - 2)
      + m * bB ^ 2 = 0 := by
  have hcomb : h2 * g1 * ((gaa1 + wa1 + sa * ga12 - 1) + (m + G + wb))
      - h1 * g2 * ((gaa1 + wa1 + sa * ga12 - 1) + (n + G + wd))
      + gbd * (g2 * h2 - g1 * h1) = 0 := by
    linear_combination h2 * hIdmA1B - h1 * hIdmA1D - h2 * ga12 * hgb2
      - h2 * X12 * hhb2 + h1 * ga12 * hgd2 + h1 * X12 * hhd2
  have hprodStep : m * n * bB * dD * p1 * c1
        * ((gaa1 + wa1 + sa * ga12 - 1) + (m + G + wb))
      - m * n * aD * cB * r1 * d1
        * ((gaa1 + wa1 + sa * ga12 - 1) + (n + G + wd))
      + gbd * (n ^ 2 * aD * dD * r1 * c1
        - m ^ 2 * bB * cB * p1 * d1) = 0 := by
    linear_combination 4 * p1 * r1 * c1 * d1 * hcomb
      - ((gaa1 + wa1 + sa * ga12 - 1) + (m + G + wb)) * p1 * c1
        * (2 * d1 * h2) * hRowB
      + ((gaa1 + wa1 + sa * ga12 - 1) + (m + G + wb)) * p1 * c1
        * m * bB * hRowD
      + ((gaa1 + wa1 + sa * ga12 - 1) + (n + G + wd)) * r1 * d1
        * (2 * c1 * h1) * hRowA
      - ((gaa1 + wa1 + sa * ga12 - 1) + (n + G + wd)) * r1 * d1
        * n * aD * hRowC
      - gbd * r1 * c1 * (2 * d1 * h2) * hRowA
      + gbd * r1 * c1 * n * aD * hRowD
      + gbd * p1 * d1 * (2 * c1 * h1) * hRowB
      - gbd * p1 * d1 * m * bB * hRowC
  have hbranchStep : m * n * p1 * bB * cB * d1
      * (eb * ed * (2 * (gaa1 + wa1 + sa * ga12 - 1)
          + (m + G + wb) + (n + G + wd))
        - gbd * (eb ^ 2 + ed ^ 2)) = 0 := by
    linear_combination eb ^ 2 * hprodStep
      - m * n * bB * p1 * ((gaa1 + wa1 + sa * ga12 - 1) + (m + G + wb))
        * eb * hdD
      + m * n * cB * d1 * ((gaa1 + wa1 + sa * ga12 - 1) + (n + G + wd))
        * eb * haD
      - gbd * n ^ 2 * (aD * eb * r1) * hdD
      - gbd * n ^ 2 * (cB * d1 * ed) * haD
      + gbd * p1 * bB * cB * d1 * (m - n) * hkap
  have hcoreStep : m * n * p1 * bB * cB * d1 * eb * ed
      * (2 * (gaa1 + wa1 + sa * ga12 - 1)
        + (m + G + wb) + (n + G + wd) + m + n) = 0 := by
    linear_combination hbranchStep
      + m * n * p1 * bB * cB * d1 * (eb * hR2 + ed * hR1)
  have hfac : m * n * p1 * bB * cB * d1 * eb * ed ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (ne_of_gt hm) (ne_of_gt hn)) hp1) hbB)
      hcB) hd1) heb) hed
  have hafter : 2 * (gaa1 + wa1 + sa * ga12 - 1)
      + (m + G + wb) + (n + G + wd) + m + n = 0 := by
    rcases mul_eq_zero.mp hcoreStep with hcase | hcase
    · exact absurd hcase hfac
    · exact hcase
  linear_combination r1 ^ 2 * hafter - 2 * r1 * hTightB1
    + 2 * r1 * ga12 * hr2 + bB * hRowB

/-! ## Layer 7 — the weight clash -/

/-- **THE EMPTY WEIGHT WINDOW.**  The two single relations, the two pair
relations, the cross relation, and the weight sum force the weights into
an empty window when the value is negative. -/
theorem circuit_weight_clash {mB nD G : ℝ}
    {wa1 wa2 wb wc1 wc2 wd : ℝ} {r1 bB c1 cB : ℝ}
    (hNa1 : r1 ^ 2 * (2 * wa1 + 4 * G + 2 * mB + 2 * nD + wb + wd - 2)
      + mB * bB ^ 2 = 0)
    (hNa2 : r1 ^ 2 * (2 * wa2 + 4 * G + 2 * mB + 2 * nD + wb + wd - 2)
      + mB * bB ^ 2 = 0)
    (hSc1 : c1 ^ 2 * ((G + wb) + (G + wd) - 2 * (1 - wc1 - G))
      + mB * cB ^ 2 = 0)
    (hSc2 : c1 ^ 2 * ((G + wb) + (G + wd) - 2 * (1 - wc2 - G))
      + mB * cB ^ 2 = 0)
    (hCross : mB * (c1 ^ 2 * bB ^ 2 - r1 ^ 2 * cB ^ 2)
      = 2 * r1 ^ 2 * c1 ^ 2 * (1 - (mB + G + wb) - (nD + G + wd)))
    (hWS : wa1 + wa2 + wb + wc1 + wc2 + wd = 1)
    (hG : G < 0) (hwa1 : 0 < wa1) (hwa2 : 0 < wa2)
    (hwc1 : 0 < wc1) (hwc2 : 0 < wc2)
    (hr1 : r1 ≠ 0) (hc1 : c1 ≠ 0) :
    False := by
  have hr1sq : 0 < r1 ^ 2 := by positivity
  have hc1sq : 0 < c1 ^ 2 := by positivity
  -- the coordinate masses cancel through the cross relation
  have hkey : r1 ^ 2 * c1 ^ 2
      * ((2 * wa1 + 4 * G + 2 * mB + 2 * nD + wb + wd - 2)
        + (2 * wa2 + 4 * G + 2 * mB + 2 * nD + wb + wd - 2)
        - ((G + wb) + (G + wd) - 2 * (1 - wc1 - G))
        - ((G + wb) + (G + wd) - 2 * (1 - wc2 - G))
        + 4 * (1 - (mB + G + wb) - (nD + G + wd))) = 0 := by
    linear_combination c1 ^ 2 * hNa1 + c1 ^ 2 * hNa2 - r1 ^ 2 * hSc1
      - r1 ^ 2 * hSc2 - 2 * hCross
  have hfactor : r1 ^ 2 * c1 ^ 2 ≠ 0 :=
    mul_ne_zero (ne_of_gt hr1sq) (ne_of_gt hc1sq)
  have hlinear : (2 * wa1 + 4 * G + 2 * mB + 2 * nD + wb + wd - 2)
        + (2 * wa2 + 4 * G + 2 * mB + 2 * nD + wb + wd - 2)
        - ((G + wb) + (G + wd) - 2 * (1 - wc1 - G))
        - ((G + wb) + (G + wd) - 2 * (1 - wc2 - G))
        + 4 * (1 - (mB + G + wb) - (nD + G + wd)) = 0 := by
    rcases mul_eq_zero.mp hkey with hcase | hcase
    · exact absurd hcase hfactor
    · exact hcase
  -- the linear form reads 3 (wa1 + wa2) + (wc1 + wc2) = 4 G < 0
  linarith

/-! ## Layer 8 — the scalar capstone -/

/-- **THE SCALAR CAPSTONE.**  The full circuit scalar system either
refuses outright, or exits with both shifted weights and the co-pair
leak at zero.  The hypothesis list is symmetric in the side mirror, thus
the datum module consumes the capstone twice. -/
theorem circuit_scalar_kill {m n G wa1 wa2 wb wc1 wc2 wd : ℝ}
    {g1 g2 gb2 gd2 h1 h2 hb2 hd2 gbd : ℝ}
    {gaa1 ga12 gcc1 gc12 X11 X12 X21 : ℝ}
    {p1 r1 r2 aD bB c1 c2 d1 cB dD eb ed sa sc : ℝ}
    (hR1 : m * eb + gbd * ed = 0)
    (hR2 : gbd * eb + n * ed = 0)
    (hZ : g1 * eb + g2 * ed = 0)
    (hRowB : 2 * r1 * g1 = -(m * bB)) (hRowA : 2 * p1 * g2 = -(n * aD))
    (hRowC : 2 * c1 * h1 = -(m * cB)) (hRowD : 2 * d1 * h2 = -(n * dD))
    (hsa : sa ^ 2 = 1) (hsc : sc ^ 2 = 1)
    (hgb2 : gb2 = sa * g1) (hgd2 : gd2 = sa * g2)
    (hhb2 : hb2 = sc * h1) (hhd2 : hd2 = sc * h2)
    (hr2 : r2 = sa * r1) (hc2 : c2 = sc * c1)
    (hTightB1 : gaa1 * r1 + ga12 * r2 + g1 * bB = G * r1)
    (hTightC1 : h1 * cB + gcc1 * c1 + gc12 * c2 = G * c1)
    (hIdmA1B : (gaa1 + wa1) * g1 + ga12 * gb2 + g1 * (m + G + wb)
      + X11 * h1 + X12 * hb2 + g2 * gbd = g1)
    (hIdmA1D : (gaa1 + wa1) * g2 + ga12 * gd2 + g1 * gbd + X11 * h2
      + X12 * hd2 + g2 * (n + G + wd) = g2)
    (hIdmBC1 : g1 * X11 + gb2 * X21 + (m + G + wb) * h1
      + h1 * (gcc1 + wc1) + hb2 * gc12 + gbd * h2 = h1)
    (hIdmC1D : X11 * g2 + X21 * gd2 + h1 * gbd + (gcc1 + wc1) * h2
      + gc12 * hd2 + h2 * (n + G + wd) = h2)
    (hIdmBB : g1 ^ 2 + gb2 ^ 2 + (m + G + wb) ^ 2 + h1 ^ 2 + hb2 ^ 2
      + gbd ^ 2 = m + G + wb)
    (hIdmDD : g2 ^ 2 + gd2 ^ 2 + gbd ^ 2 + h2 ^ 2 + hd2 ^ 2
      + (n + G + wd) ^ 2 = n + G + wd)
    (hIdmBD : g1 * g2 + gb2 * gd2 + (m + G + wb) * gbd + h1 * h2
      + hb2 * hd2 + gbd * (n + G + wd) = gbd)
    (hS5 : n * dD ^ 2 * c1 ^ 2 = m * cB ^ 2 * d1 ^ 2)
    (hWS : wa1 + wa2 + wb + wc1 + wc2 + wd = 1)
    (htwinA : wa1 = wa2) (htwinC : wc1 = wc2)
    (hwa1 : 0 < wa1) (hwc1 : 0 < wc1)
    (hm : 0 < m) (hn : 0 < n) (hG : G < 0)
    (hdb : 0 ≤ G + wb) (hdd : 0 ≤ G + wd)
    (hp1 : p1 ≠ 0) (hr1 : r1 ≠ 0) (hc1 : c1 ≠ 0) (hd1 : d1 ≠ 0)
    (hbB : bB ≠ 0) (hcB : cB ≠ 0) (heb : eb ≠ 0) (hed : ed ≠ 0) :
    G + wb = 0 ∧ G + wd = 0 ∧ h1 * eb + h2 * ed = 0 := by
  have hkap := circuit_kappa hR1 hR2
  have hSq := circuit_cross_sq hR1 hR2 hed
  -- the collapsed row squares and the collapsed cross entry
  have hRSb : 2 * g1 ^ 2 + 2 * h1 ^ 2 + gbd ^ 2
      = (m + G + wb) * (1 - (m + G + wb)) := by
    linear_combination hIdmBB - (gb2 + sa * g1) * hgb2 - g1 ^ 2 * hsa
      - (hb2 + sc * h1) * hhb2 - h1 ^ 2 * hsc
  have hRSd : 2 * g2 ^ 2 + 2 * h2 ^ 2 + gbd ^ 2
      = (n + G + wd) * (1 - (n + G + wd)) := by
    linear_combination hIdmDD - (gd2 + sa * g2) * hgd2 - g2 ^ 2 * hsa
      - (hd2 + sc * h2) * hhd2 - h2 ^ 2 * hsc
  have hX0 : 2 * g1 * g2 + 2 * h1 * h2
      = gbd * (1 - (m + G + wb) - (n + G + wd)) := by
    linear_combination hIdmBD - sa * g2 * hgb2 - gb2 * hgd2
      - g1 * g2 * hsa - sc * h2 * hhb2 - hb2 * hhd2 - h1 * h2 * hsc
  -- the two diagonal windows
  have hwinB := circuit_diag_window hRSb hSq hm hn
  have hSqd : gbd ^ 2 = n * m := by linear_combination hSq
  have hX0d : 2 * g2 * g1 + 2 * h2 * h1
      = gbd * (1 - (n + G + wd) - (m + G + wb)) := by
    linear_combination hX0
  have hwinD := circuit_diag_window hRSd hSqd hn hm
  -- the two leak prices
  have hpriceB := circuit_leak_price hRSb hX0 hZ hR1 hSq
  have hZd : g2 * ed + g1 * eb = 0 := by linear_combination hZ
  have hR1d : n * ed + gbd * eb = 0 := by linear_combination hR2
  have hpriceDraw := circuit_leak_price hRSd hX0d hZd hR1d hSqd
  have hpriceD : 2 * h2 * (h1 * eb + h2 * ed)
      = ed * ((G + wd) * (1 - n - G - wd) + n * (G + wb)) := by
    linear_combination hpriceDraw
  -- the leak split
  by_cases htau : h1 * eb + h2 * ed = 0
  · obtain ⟨hdbz, hddz⟩ := circuit_zero_leak hpriceB htau heb hdb hdd hm
      hwinB.2
    exact ⟨hdbz, hddz, htau⟩
  · exfalso
    -- the claw and the solved coordinates
    have hdDv := circuit_claw hpriceB hpriceD hRowC hRowD hS5 hkap hdb hdd
      hm hn hwinB.2.le hwinD.2.le htau hd1 hcB hed
    have hZc : m * eb * p1 * bB + n * ed * r1 * aD = 0 := by
      linear_combination p1 * eb * hRowB + r1 * ed * hRowA
        - 2 * p1 * r1 * hZ
    have hnDv : n * ed ^ 2 = m * eb ^ 2 := hkap.symm
    have haDv := circuit_aD_value hZc hnDv (ne_of_gt hm) heb
    have hgbdv : gbd * ed = -(m * eb) := by linear_combination hR1
    -- the three scalar relations
    have hCross := circuit_cross_scalar hX0 hRowB hRowA hRowC hRowD hnDv
      hgbdv haDv hdDv hp1 hd1 heb (ne_of_gt hm)
    have hNa1 := circuit_newone_scalar hIdmA1B hIdmA1D hTightB1 hRowB hRowA
      hRowC hRowD hgb2 hgd2 hhb2 hhd2 hr2 hR1 hR2 hkap haDv hdDv hm hn hp1
      hbB hcB hd1 heb hed
    have hSc1 := circuit_spade_scalar hIdmBC1 hIdmC1D hTightC1 hRowB hRowA
      hRowC hRowD hgb2 hgd2 hhb2 hhd2 hc2 hR1 hR2 hkap haDv hdDv hm hn hp1
      hbB hcB hd1 heb hed
    have hNa2 : r1 ^ 2 * (2 * wa2 + 4 * G + 2 * m + 2 * n + wb + wd - 2)
        + m * bB ^ 2 = 0 := by
      rw [← htwinA]
      exact hNa1
    have hSc2 : c1 ^ 2 * ((G + wb) + (G + wd) - 2 * (1 - wc2 - G))
        + m * cB ^ 2 = 0 := by
      rw [← htwinC]
      exact hSc1
    have hwa2 : 0 < wa2 := htwinA ▸ hwa1
    have hwc2 : 0 < wc2 := htwinC ▸ hwc1
    exact circuit_weight_clash hNa1 hNa2 hSc1 hSc2 hCross hWS hG hwa1 hwa2
      hwc1 hwc2 hr1 hc1

end Gtz
