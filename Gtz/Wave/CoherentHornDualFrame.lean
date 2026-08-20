/-
# The dual frame of a triple, and the coherent horn as a polynomial system

The sign-coherent horn of a corank-two corner (`Gtz.corner_matching_of_signCoherent`)
puts each outside atom in an inside plane.  This module reads the design in the
frame DUAL to the inside triple — the three cross products — and the horn becomes
an explicit polynomial system.

## The engine

Parseval read at two probes (`Gtz.parseval_read_pair`) is an identity for every
pair of vectors.  Read at two dual normals `n_e = g_f × g_g` it splits
(`Gtz.dualPair_split`) into an inside part and an outside part, and the inside
part COLLAPSES: a dual normal annihilates its own two atoms, so only the
diagonal term survives, at the squared bracket
(`Gtz.inside_dualPair_diag`, `Gtz.inside_dualPair_offDiag`).  The result is

  `Σ_{d ∉ C} t_d·(n_e·g_d)(n_f·g_d) = n_e·n_f − [xyz]²·t_e·(e = f)` ,

the DUAL-FRAME PARSEVAL of a triple.  It holds at every size, with no corner
and no tie.

## The collapse

On the coherent horn the matched atom is annihilated by its own normal, so the
off-diagonal equation keeps ONE term and the diagonal keeps TWO
(`Gtz.coherent_offDiag_single`, `Gtz.coherent_diag_pair`).  The single
off-diagonal term is the landed matching quantization, re-derived here as the
off-diagonal of Parseval itself.  Squaring it gives the PRODUCT LAW
(`Gtz.coherent_slot_product`): the two slot energies of one outside atom
multiply to the squared dual pairing of the plane it misses.

## The law

Two energies with a fixed product and a fixed sum obey AM–GM, and the three
diagonal equations multiply:

  `Gtz.coherent_amgm_law` :
    `64·((n_x·n_y)(n_y·n_z)(n_z·n_x))² ≤ (∏_e (|n_e|² − t_e·[xyz]²))²` .

Both sides are polynomial in the design.  The dictionary
(`Gtz.dualNormal_selfPairing_eq_wedge`, `Gtz.dualNormal_pairing_eq_gram`) writes
them in the invariant currency: `|n_e|²` is the WEDGE of the opposite pair, and
`n_e·n_f` is a Gram minor of the pairings.  So the horn is a wedge-and-bracket
inequality, in the arena of `Gtz.WedgeBracketTax`.

## The producer

Independently, the complement of a triple at size six carries a determinant
producer (`Gtz.posDef_compl_of_det_gt_e2_mul_weight`): the outside weighted
moment is the identity minus the inside one, its determinant is the weighted
squared bracket of the complement (`Gtz.det_weighted_compl_eq_bracket`), and the
spectral-free floor of `Gtz.InvariantTaxTeeth` converts a determinant that beats
`tcap·e₂` into a strict dominator.  At `(6,3)` this reads

  `t_{d₁}t_{d₂}t_{d₃}·[d₁d₂d₃]² > tcap·e₂ ⟹ the complement dominates` ,

so no tie — a corner-free kill in the bracket currency
(`Gtz.not_isTie_of_complement_bracket_beats`).
-/
import Gtz.Wave.InvariantTaxTeeth
import Gtz.Wave.CornerSignMatching

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The dual normal of a pair -/

/-- **THE DUAL NORMAL.**  The cross product of two atoms.  It reads every atom
at the bracket of the triple, so it annihilates its own two atoms. -/
noncomputable def atomNormal (D : WeightedDesign m 3) (first second : Fin m) : Fin 3 → ℝ :=
  bracketNormal (D.atom first) (D.atom second)

/-- A dual normal reads an atom at the bracket. -/
theorem atomNormal_dot_atom (D : WeightedDesign m 3) (first second probe : Fin m) :
    atomNormal D first second ⬝ᵥ D.atom probe = atomBracket D first second probe := by
  rw [atomNormal, atomBracket, tripleBracket_eq_bracketNormal_dotProduct]

/-- A dual normal annihilates its own left atom. -/
theorem atomNormal_dot_left (D : WeightedDesign m 3) (first second : Fin m) :
    atomNormal D first second ⬝ᵥ D.atom first = 0 := by
  rw [atomNormal]
  exact bracketNormal_dotProduct_left _ _

/-- A dual normal annihilates its own right atom. -/
theorem atomNormal_dot_right (D : WeightedDesign m 3) (first second : Fin m) :
    atomNormal D first second ⬝ᵥ D.atom second = 0 := by
  rw [atomNormal]
  exact bracketNormal_dotProduct_right _ _

/-! ## 2. Parseval read at two probes -/

/-- **PARSEVAL AT TWO PROBES.**  The weighted readings of any two probes against
the atoms total the pairing of the probes.  The polarization of the frame law. -/
theorem parseval_read_pair (D : WeightedDesign m 3) (probeLeft probeRight : Fin 3 → ℝ) :
    ∑ a, D.weight a * ((probeLeft ⬝ᵥ D.atom a) * (probeRight ⬝ᵥ D.atom a))
      = probeLeft ⬝ᵥ probeRight := by
  have hterm : ∀ a : Fin m,
      D.weight a * ((probeLeft ⬝ᵥ D.atom a) * (probeRight ⬝ᵥ D.atom a))
        = probeLeft ⬝ᵥ ((D.weight a • atomMatrix (D.atom a)) *ᵥ probeRight) := by
    intro a
    rw [Matrix.smul_mulVec,
      show atomMatrix (D.atom a) *ᵥ probeRight = (D.atom a ⬝ᵥ probeRight) • D.atom a from
        vecMulVec_mulVec_eq _ _ _,
      dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      dotProduct_comm (D.atom a) probeRight]
    ring
  have hlin : ∑ a, probeLeft ⬝ᵥ ((D.weight a • atomMatrix (D.atom a)) *ᵥ probeRight)
      = probeLeft ⬝ᵥ ((∑ a, D.weight a • atomMatrix (D.atom a)) *ᵥ probeRight) := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
  rw [Finset.sum_congr rfl fun a _ => hterm a, hlin, D.isParseval, Matrix.one_mulVec]

/-- **THE OUTSIDE SPLIT.**  The outside weighted readings of two probes are the
pairing minus the inside weighted readings. -/
theorem dualPair_split (D : WeightedDesign m 3) (C : Finset (Fin m))
    (probeLeft probeRight : Fin 3 → ℝ) :
    ∑ d ∈ Cᶜ, D.weight d * ((probeLeft ⬝ᵥ D.atom d) * (probeRight ⬝ᵥ D.atom d))
      = probeLeft ⬝ᵥ probeRight
        - ∑ c ∈ C, D.weight c * ((probeLeft ⬝ᵥ D.atom c) * (probeRight ⬝ᵥ D.atom c)) := by
  classical
  have hsplit := Finset.sum_add_sum_compl C
    (fun a => D.weight a * ((probeLeft ⬝ᵥ D.atom a) * (probeRight ⬝ᵥ D.atom a)))
  rw [parseval_read_pair] at hsplit
  linarith [hsplit]

/-! ## 3. The inside collapse -/

/-- The bracket is invariant under a cyclic turn of its three slots. -/
theorem atomBracket_cycle (D : WeightedDesign m 3) (first second third : Fin m) :
    atomBracket D first second third = atomBracket D second third first := by
  simp only [atomBracket, tripleBracket_eq]
  ring

/-- **THE INSIDE DIAGONAL.**  Against one dual normal twice, the inside triple
contributes only its own weight times the squared bracket. -/
theorem inside_dualPair_diag (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∑ c ∈ ({x, y, z} : Finset (Fin m)),
        D.weight c * ((atomNormal D y z ⬝ᵥ D.atom c) * (atomNormal D y z ⬝ᵥ D.atom c))
      = D.weight x * atomBracket D x y z ^ 2 := by
  rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton, atomNormal_dot_left, atomNormal_dot_right,
    atomNormal_dot_atom]
  rw [show atomBracket D y z x = atomBracket D x y z from
    (atomBracket_cycle D x y z).symm]
  ring

/-- **THE INSIDE OFF-DIAGONAL.**  Against two different dual normals the inside
triple contributes nothing: each normal annihilates two of the three atoms, and
the third is annihilated by the other normal. -/
theorem inside_dualPair_offDiag (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∑ c ∈ ({x, y, z} : Finset (Fin m)),
        D.weight c * ((atomNormal D y z ⬝ᵥ D.atom c) * (atomNormal D z x ⬝ᵥ D.atom c))
      = 0 := by
  rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton, atomNormal_dot_left, atomNormal_dot_right,
    atomNormal_dot_right, atomNormal_dot_left]
  ring

/-- **THE DUAL-FRAME PARSEVAL, DIAGONAL.**  Every size, no corner, no tie. -/
theorem outside_dualPair_diag (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d * ((atomNormal D y z ⬝ᵥ D.atom d) * (atomNormal D y z ⬝ᵥ D.atom d))
      = atomNormal D y z ⬝ᵥ atomNormal D y z
        - D.weight x * atomBracket D x y z ^ 2 := by
  rw [dualPair_split D ({x, y, z} : Finset (Fin m)),
    inside_dualPair_diag D hxy hxz hyz]

/-- **THE DUAL-FRAME PARSEVAL, OFF-DIAGONAL.**  The outside weighted cross
readings of two dual normals total their pairing exactly. -/
theorem outside_dualPair_offDiag (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d * ((atomNormal D y z ⬝ᵥ D.atom d) * (atomNormal D z x ⬝ᵥ D.atom d))
      = atomNormal D y z ⬝ᵥ atomNormal D z x := by
  rw [dualPair_split D ({x, y, z} : Finset (Fin m)),
    inside_dualPair_offDiag D hxy hxz hyz, sub_zero]

/-! ## 4. The invariant dictionary -/

/-- **A DUAL NORMAL READS ITS OWN WEDGE.**  Lagrange: the squared normal of a
pair is the pair's wedge — leverage product minus squared pairing. -/
theorem dualNormal_selfPairing_eq_wedge (D : WeightedDesign m 3) (first second : Fin m) :
    atomNormal D first second ⬝ᵥ atomNormal D first second
      = leverageOf (D.atom first) * leverageOf (D.atom second)
        - atomPairing D first second ^ 2 := by
  simp only [atomNormal, bracketNormal, leverageOf, atomPairing, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **TWO DUAL NORMALS PAIR AT A GRAM MINOR.**  Lagrange again: the pairing of
two normals sharing an atom is a two-by-two minor of the pairing matrix. -/
theorem dualNormal_pairing_eq_gram (D : WeightedDesign m 3) (shared first second : Fin m) :
    atomNormal D first shared ⬝ᵥ atomNormal D shared second
      = atomPairing D first shared * atomPairing D shared second
        - leverageOf (D.atom shared) * atomPairing D first second := by
  simp only [atomNormal, bracketNormal, leverageOf, atomPairing, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## 5. The coherent collapse at size six -/

/-- **THE OFF-DIAGONAL KEEPS ONE TERM.**  On the coherent horn each matched atom
is annihilated by the normal of the plane it lies in, so the off-diagonal dual
Parseval of two planes is carried by the third matched atom ALONE.  This is the
landed matching quantization, read as the off-diagonal of Parseval. -/
theorem coherent_offDiag_single (D : WeightedDesign 6 3) {x y z dyz dxz dxy : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h12 : dyz ≠ dxz) (h13 : dyz ≠ dxy) (h23 : dxz ≠ dxy)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {dyz, dxz, dxy})
    (hzYZ : atomBracket D y z dyz = 0) (hzXZ : atomBracket D x z dxz = 0) :
    D.weight dxy * ((atomNormal D y z ⬝ᵥ D.atom dxy) * (atomNormal D z x ⬝ᵥ D.atom dxy))
      = atomNormal D y z ⬝ᵥ atomNormal D z x := by
  have hmain := outside_dualPair_offDiag D hxy hxz hyz
  rw [hcompl, Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
    Finset.sum_singleton] at hmain
  have hA : atomNormal D y z ⬝ᵥ D.atom dyz = 0 := by
    rw [atomNormal_dot_atom]; exact hzYZ
  have hB : atomNormal D z x ⬝ᵥ D.atom dxz = 0 := by
    rw [atomNormal_dot_atom,
      show atomBracket D z x dxz = -atomBracket D x z dxz from
        tripleBracket_swapLeft _ _ _, hzXZ, neg_zero]
  rw [hA, hB] at hmain
  rw [← hmain]
  ring

/-- **THE DIAGONAL KEEPS TWO TERMS.**  The matched atom of a plane is invisible
to that plane's normal, so the diagonal dual Parseval is carried by the other
two matched atoms. -/
theorem coherent_diag_pair (D : WeightedDesign 6 3) {x y z dyz dxz dxy : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h12 : dyz ≠ dxz) (h13 : dyz ≠ dxy) (h23 : dxz ≠ dxy)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {dyz, dxz, dxy})
    (hzYZ : atomBracket D y z dyz = 0) :
    D.weight dxz * (atomNormal D y z ⬝ᵥ D.atom dxz) ^ 2
        + D.weight dxy * (atomNormal D y z ⬝ᵥ D.atom dxy) ^ 2
      = atomNormal D y z ⬝ᵥ atomNormal D y z
        - D.weight x * atomBracket D x y z ^ 2 := by
  have hmain := outside_dualPair_diag D hxy hxz hyz
  rw [hcompl, Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
    Finset.sum_singleton] at hmain
  have hA : atomNormal D y z ⬝ᵥ D.atom dyz = 0 := by
    rw [atomNormal_dot_atom]; exact hzYZ
  rw [hA] at hmain
  rw [← hmain]
  ring


/-! ## 6. The product law and the AM–GM law of the horn -/

/-- **THE SLOT PRODUCT LAW.**  The two slot energies of ONE matched outside atom
— read by the two normals that do not annihilate it — multiply to the squared
dual pairing of those two planes.  Squaring the single off-diagonal term removes
every sign, so the law is a polynomial identity. -/
theorem coherent_slot_product (D : WeightedDesign 6 3) {x y z dyz dxz dxy : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h12 : dyz ≠ dxz) (h13 : dyz ≠ dxy) (h23 : dxz ≠ dxy)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {dyz, dxz, dxy})
    (hzYZ : atomBracket D y z dyz = 0) (hzXZ : atomBracket D x z dxz = 0) :
    (D.weight dxy * (atomNormal D y z ⬝ᵥ D.atom dxy) ^ 2)
        * (D.weight dxy * (atomNormal D z x ⬝ᵥ D.atom dxy) ^ 2)
      = (atomNormal D y z ⬝ᵥ atomNormal D z x) ^ 2 := by
  have hq := coherent_offDiag_single D hxy hxz hyz h12 h13 h23 hcompl hzYZ hzXZ
  rw [← hq]
  ring

/-- A slot energy is nonnegative. -/
theorem slot_energy_nonneg (D : WeightedDesign m 3) (slotLabel : Fin m)
    (probe : Fin 3 → ℝ) : 0 ≤ D.weight slotLabel * (probe ⬝ᵥ D.atom slotLabel) ^ 2 :=
  mul_nonneg (D.weight_pos slotLabel).le (sq_nonneg _)

/-- **AM–GM AT ONE PLANE.**  Two nonnegative slots with a pinned total have their
product below a quarter of the squared total. -/
theorem four_mul_le_sq_of_add {slotFirst slotSecond total : ℝ}
    (hfirst : 0 ≤ slotFirst) (hsecond : 0 ≤ slotSecond)
    (hsum : slotFirst + slotSecond = total) :
    4 * (slotFirst * slotSecond) ≤ total ^ 2 := by
  nlinarith [sq_nonneg (slotFirst - slotSecond)]

/-- **THE AM–GM LAW OF THE COHERENT HORN.**  Each inside plane reads exactly two
matched atoms, so its diagonal total dominates twice the root of their product.
The three products regroup by MATCHED ATOM — each atom is read by exactly the two
normals that do not annihilate it — and the product law turns each pair into a
squared dual pairing.  The result is one polynomial inequality of the horn:

  `64·((n_x·n_y)(n_y·n_z)(n_z·n_x))² ≤ (∏_e (|n_e|² − t_e·[xyz]²))²` ,

tie-free, weight-carrying, and written in the invariant currency by
`Gtz.dualNormal_selfPairing_eq_wedge` — the left side is a product of squared
Gram minors, the right side a product of wedges taxed at the squared bracket. -/
theorem coherent_amgm_law (D : WeightedDesign 6 3) {x y z dyz dxz dxy : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h12 : dyz ≠ dxz) (h13 : dyz ≠ dxy) (h23 : dxz ≠ dxy)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {dyz, dxz, dxy})
    (hzYZ : atomBracket D y z dyz = 0) (hzXZ : atomBracket D x z dxz = 0)
    (hzXY : atomBracket D x y dxy = 0) :
    64 * ((atomNormal D y z ⬝ᵥ atomNormal D z x)
          * ((atomNormal D z x ⬝ᵥ atomNormal D x y)
            * (atomNormal D x y ⬝ᵥ atomNormal D y z))) ^ 2
      ≤ ((atomNormal D y z ⬝ᵥ atomNormal D y z - D.weight x * atomBracket D x y z ^ 2)
          * ((atomNormal D z x ⬝ᵥ atomNormal D z x - D.weight y * atomBracket D x y z ^ 2)
            * (atomNormal D x y ⬝ᵥ atomNormal D x y
                - D.weight z * atomBracket D x y z ^ 2))) ^ 2 := by
  classical
  have hCy : (({y, z, x} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {dxz, dxy, dyz} := by
    rw [show ({y, z, x} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto, hcompl]
    ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hCz : (({z, x, y} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {dxy, dyz, dxz} := by
    rw [show ({z, x, y} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto, hcompl]
    ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hbY : atomBracket D y z x = atomBracket D x y z := (atomBracket_cycle D x y z).symm
  have hbZ : atomBracket D z x y = atomBracket D x y z := by rw [atomBracket_cycle D z x y]
  have hzZX : atomBracket D z x dxz = 0 := by
    rw [show atomBracket D z x dxz = -atomBracket D x z dxz from
      tripleBracket_swapLeft _ _ _, hzXZ, neg_zero]
  have hzYX : atomBracket D y x dxy = 0 := by
    rw [show atomBracket D y x dxy = -atomBracket D x y dxy from
      tripleBracket_swapLeft _ _ _, hzXY, neg_zero]
  have hzZY : atomBracket D z y dyz = 0 := by
    rw [show atomBracket D z y dyz = -atomBracket D y z dyz from
      tripleBracket_swapLeft _ _ _, hzYZ, neg_zero]
  -- the three diagonal equations, one per inside plane
  have hdX := coherent_diag_pair D hxy hxz hyz h12 h13 h23 hcompl hzYZ
  have hdY := coherent_diag_pair D hyz (Ne.symm hxy) (Ne.symm hxz)
    h23 (Ne.symm h12) (Ne.symm h13) hCy hzZX
  have hdZ := coherent_diag_pair D (Ne.symm hxz) (Ne.symm hyz) hxy
    (Ne.symm h13) (Ne.symm h23) h12 hCz hzXY
  rw [hbY] at hdY
  rw [hbZ] at hdZ
  -- the three product laws, one per matched outside atom
  have hpA := coherent_slot_product D hxy hxz hyz h12 h13 h23 hcompl hzYZ hzXZ
  have hpB := coherent_slot_product D hyz (Ne.symm hxy) (Ne.symm hxz)
    h23 (Ne.symm h12) (Ne.symm h13) hCy hzZX hzYX
  have hpC := coherent_slot_product D (Ne.symm hxz) (Ne.symm hyz) hxy
    (Ne.symm h13) (Ne.symm h23) h12 hCz hzXY hzZY
  set slotXfirst : ℝ := D.weight dxz * (atomNormal D y z ⬝ᵥ D.atom dxz) ^ 2 with hsXf
  set slotXsecond : ℝ := D.weight dxy * (atomNormal D y z ⬝ᵥ D.atom dxy) ^ 2 with hsXs
  set slotYfirst : ℝ := D.weight dxy * (atomNormal D z x ⬝ᵥ D.atom dxy) ^ 2 with hsYf
  set slotYsecond : ℝ := D.weight dyz * (atomNormal D z x ⬝ᵥ D.atom dyz) ^ 2 with hsYs
  set slotZfirst : ℝ := D.weight dyz * (atomNormal D x y ⬝ᵥ D.atom dyz) ^ 2 with hsZf
  set slotZsecond : ℝ := D.weight dxz * (atomNormal D x y ⬝ᵥ D.atom dxz) ^ 2 with hsZs
  have hnXf : 0 ≤ slotXfirst := by rw [hsXf]; exact slot_energy_nonneg D dxz _
  have hnXs : 0 ≤ slotXsecond := by rw [hsXs]; exact slot_energy_nonneg D dxy _
  have hnYf : 0 ≤ slotYfirst := by rw [hsYf]; exact slot_energy_nonneg D dxy _
  have hnYs : 0 ≤ slotYsecond := by rw [hsYs]; exact slot_energy_nonneg D dyz _
  have hnZf : 0 ≤ slotZfirst := by rw [hsZf]; exact slot_energy_nonneg D dyz _
  have hnZs : 0 ≤ slotZsecond := by rw [hsZs]; exact slot_energy_nonneg D dxz _
  have hX := four_mul_le_sq_of_add hnXf hnXs hdX
  have hY := four_mul_le_sq_of_add hnYf hnYs hdY
  have hZ := four_mul_le_sq_of_add hnZf hnZs hdZ
  have hexpand : ((atomNormal D y z ⬝ᵥ atomNormal D z x)
        * ((atomNormal D z x ⬝ᵥ atomNormal D x y)
          * (atomNormal D x y ⬝ᵥ atomNormal D y z))) ^ 2
      = (atomNormal D y z ⬝ᵥ atomNormal D z x) ^ 2
        * ((atomNormal D z x ⬝ᵥ atomNormal D x y) ^ 2
          * (atomNormal D x y ⬝ᵥ atomNormal D y z) ^ 2) := by ring
  have hprodRegroup :
      64 * ((atomNormal D y z ⬝ᵥ atomNormal D z x)
          * ((atomNormal D z x ⬝ᵥ atomNormal D x y)
            * (atomNormal D x y ⬝ᵥ atomNormal D y z))) ^ 2
        = (4 * (slotXfirst * slotXsecond))
          * ((4 * (slotYfirst * slotYsecond)) * (4 * (slotZfirst * slotZsecond))) := by
    rw [hexpand, ← hpA, ← hpB, ← hpC]
    ring
  have h4Y : (0:ℝ) ≤ 4 * (slotYfirst * slotYsecond) :=
    mul_nonneg (by norm_num) (mul_nonneg hnYf hnYs)
  have h4Z : (0:ℝ) ≤ 4 * (slotZfirst * slotZsecond) :=
    mul_nonneg (by norm_num) (mul_nonneg hnZf hnZs)
  have hinner : (4 * (slotYfirst * slotYsecond)) * (4 * (slotZfirst * slotZsecond))
      ≤ (atomNormal D z x ⬝ᵥ atomNormal D z x - D.weight y * atomBracket D x y z ^ 2) ^ 2
        * (atomNormal D x y ⬝ᵥ atomNormal D x y
            - D.weight z * atomBracket D x y z ^ 2) ^ 2 :=
    mul_le_mul hY hZ h4Z (sq_nonneg _)
  rw [hprodRegroup]
  calc (4 * (slotXfirst * slotXsecond))
        * ((4 * (slotYfirst * slotYsecond)) * (4 * (slotZfirst * slotZsecond)))
      ≤ (atomNormal D y z ⬝ᵥ atomNormal D y z - D.weight x * atomBracket D x y z ^ 2) ^ 2
        * ((atomNormal D z x ⬝ᵥ atomNormal D z x - D.weight y * atomBracket D x y z ^ 2) ^ 2
          * (atomNormal D x y ⬝ᵥ atomNormal D x y
              - D.weight z * atomBracket D x y z ^ 2) ^ 2) :=
        mul_le_mul hX hinner (mul_nonneg h4Y h4Z) (sq_nonneg _)
    _ = _ := by ring

/-! ## 7. The size-six determinant law of the complement -/

/-- **THE OUTSIDE MOMENT IS THE COMPLEMENT OF THE INSIDE ONE.**  Parseval, split
at a subset. -/
theorem weighted_compl_eq_one_sub_inside (D : WeightedDesign m 3) (C : Finset (Fin m)) :
    ∑ d ∈ Cᶜ, D.weight d • atomMatrix (D.atom d)
      = 1 - ∑ c ∈ C, D.weight c • atomMatrix (D.atom c) := by
  classical
  have hsplit := Finset.sum_add_sum_compl C (fun a => D.weight a • atomMatrix (D.atom a))
  rw [D.isParseval] at hsplit
  rw [← hsplit]
  abel

/-- **THE SIZE-SIX DETERMINANT LAW.**  At six atoms the complement of a triple is
a TRIPLE, so the Cauchy–Binet expansion of the outside weighted moment collapses
to a single term: its determinant is the weighted squared bracket of the
complement.  The identity consumes `6 = 3 + 3` — at `(5,3)` the complement of a
triple is a pair and the determinant is identically zero. -/
theorem det_weighted_compl_eq_bracket (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    {d1 d2 d3 : Fin 6} (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3)
    (hcompl : (Cᶜ : Finset (Fin 6)) = {d1, d2, d3}) :
    (∑ d ∈ (Cᶜ : Finset (Fin 6)), D.weight d • atomMatrix (D.atom d)).det
      = D.weight d1 * D.weight d2 * D.weight d3 * atomBracket D d1 d2 d3 ^ 2 := by
  rw [hcompl, Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
    Finset.sum_singleton, ← add_assoc, det_smul_atomMatrix_three, atomBracket]

/-! ## 8. The determinant producer of the complement -/

/-- The quadratic form of one weighted atom. -/
theorem quadForm_weighted_atom (scale : ℝ) (atomVec probe : Fin 3 → ℝ) :
    probe ⬝ᵥ ((scale • atomMatrix atomVec) *ᵥ probe) = scale * (probe ⬝ᵥ atomVec) ^ 2 := by
  rw [Matrix.smul_mulVec,
    show atomMatrix atomVec *ᵥ probe = (atomVec ⬝ᵥ probe) • atomVec from
      vecMulVec_mulVec_eq _ _ _, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, dotProduct_comm atomVec probe]
  ring

/-- The quadratic form of a weighted subset moment is the weighted energy sum. -/
theorem quadForm_weighted_sum (D : WeightedDesign m 3) (S : Finset (Fin m))
    (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ ((∑ a ∈ S, D.weight a • atomMatrix (D.atom a)) *ᵥ probe)
      = ∑ a ∈ S, D.weight a * (probe ⬝ᵥ D.atom a) ^ 2 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun a _ => quadForm_weighted_atom _ _ _

/-- The quadratic form of an unweighted subset sum is the plain energy sum. -/
theorem quadForm_subsetSum_eq (D : WeightedDesign m 3) (S : Finset (Fin m))
    (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (subsetSum D S *ᵥ probe) = ∑ a ∈ S, (probe ⬝ᵥ D.atom a) ^ 2 := by
  rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show atomMatrix (D.atom a) *ᵥ probe = (D.atom a ⬝ᵥ probe) • D.atom a from
    vecMulVec_mulVec_eq _ _ _, dotProduct_smul, smul_eq_mul,
    dotProduct_comm probe (D.atom a)]
  ring

/-- **THE DETERMINANT PRODUCER.**  If the determinant of the outside weighted
moment beats its second invariant times a cap on the outside weights, the
complement DOMINATES STRICTLY.  The spectral-free floor of
`Gtz.InvariantTaxTeeth` supplies the eigenvalue bound, the weight cap turns the
weighted moment into the unweighted one, and no eigenvalue is ever named. -/
theorem posDef_compl_of_det_gt_e2_mul_weight (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {tcap : ℝ} (hcapPos : 0 < tcap)
    (hcap : ∀ d ∈ Cᶜ, D.weight d ≤ tcap)
    (hbeat : tcap * (((Matrix.trace (∑ d ∈ Cᶜ, D.weight d • atomMatrix (D.atom d))) ^ 2
        - Matrix.trace ((∑ d ∈ Cᶜ, D.weight d • atomMatrix (D.atom d))
          * (∑ d ∈ Cᶜ, D.weight d • atomMatrix (D.atom d)))) / 2)
      < (∑ d ∈ Cᶜ, D.weight d • atomMatrix (D.atom d)).det) :
    (subsetSum D Cᶜ - 1).PosDef := by
  classical
  set outsideMoment : Matrix (Fin 3) (Fin 3) ℝ :=
    ∑ d ∈ Cᶜ, D.weight d • atomMatrix (D.atom d) with houtDef
  have hpsd : outsideMoment.PosSemidef := by
    rw [houtDef]
    refine Matrix.posSemidef_sum _ fun d _ => ?_
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe => ?_⟩
    · refine isHermitian_of_transpose_eq ?_
      rw [Matrix.transpose_smul, transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom d)).1]
    · rw [star_trivial, quadForm_weighted_atom]
      exact mul_nonneg (D.weight_pos d).le (sq_nonneg _)
  have he2nn : 0 ≤ ((Matrix.trace outsideMoment) ^ 2
      - Matrix.trace (outsideMoment * outsideMoment)) / 2 := e2_nonneg_of_posSemidef hpsd
  have hdetpos : 0 < outsideMoment.det := by
    have := mul_nonneg hcapPos.le he2nn
    linarith [hbeat]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨((posSemidef_subsetSum D Cᶜ).1.sub Matrix.isHermitian_one), fun probe hprobe => ?_⟩
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec]
  have hnorm : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobe
  have hweighted : probe ⬝ᵥ (outsideMoment *ᵥ probe)
      ≤ tcap * (probe ⬝ᵥ (subsetSum D Cᶜ *ᵥ probe)) := by
    rw [houtDef, quadForm_weighted_sum, quadForm_subsetSum_eq, Finset.mul_sum]
    exact Finset.sum_le_sum fun d hd =>
      mul_le_mul_of_nonneg_right (hcap d hd) (sq_nonneg _)
  have hteeth := e2_mul_form_ge_det_mul_normSq hpsd probe
  have hchain : outsideMoment.det * (probe ⬝ᵥ probe)
      ≤ (((Matrix.trace outsideMoment) ^ 2
          - Matrix.trace (outsideMoment * outsideMoment)) / 2 * tcap)
        * (probe ⬝ᵥ (subsetSum D Cᶜ *ᵥ probe)) := by
    calc outsideMoment.det * (probe ⬝ᵥ probe)
        ≤ ((Matrix.trace outsideMoment) ^ 2
            - Matrix.trace (outsideMoment * outsideMoment)) / 2
          * (probe ⬝ᵥ (outsideMoment *ᵥ probe)) := hteeth
      _ ≤ ((Matrix.trace outsideMoment) ^ 2
            - Matrix.trace (outsideMoment * outsideMoment)) / 2
          * (tcap * (probe ⬝ᵥ (subsetSum D Cᶜ *ᵥ probe))) :=
          mul_le_mul_of_nonneg_left hweighted he2nn
      _ = _ := by ring
  by_contra hcon
  push Not at hcon
  have hsmall : probe ⬝ᵥ (subsetSum D Cᶜ *ᵥ probe) ≤ probe ⬝ᵥ probe := by linarith
  have hstep : (((Matrix.trace outsideMoment) ^ 2
        - Matrix.trace (outsideMoment * outsideMoment)) / 2 * tcap)
      * (probe ⬝ᵥ (subsetSum D Cᶜ *ᵥ probe))
    ≤ (((Matrix.trace outsideMoment) ^ 2
        - Matrix.trace (outsideMoment * outsideMoment)) / 2 * tcap) * (probe ⬝ᵥ probe) :=
    mul_le_mul_of_nonneg_left hsmall (mul_nonneg he2nn hcapPos.le)
  have hstrict : (((Matrix.trace outsideMoment) ^ 2
        - Matrix.trace (outsideMoment * outsideMoment)) / 2 * tcap) * (probe ⬝ᵥ probe)
      < outsideMoment.det * (probe ⬝ᵥ probe) :=
    mul_lt_mul_of_pos_right (by linarith [hbeat]) hnorm
  linarith [hchain, hstep, hstrict]

/-- **THE COMPLEMENT BRACKET KILL.**  At `(6,3)`, if the weighted squared bracket
of the complement of a triple beats its second invariant times a cap on the three
complementary weights, the design is NO TIE.  A kill in the bracket currency with
no corner and no horn: the size marker of `Gtz.det_weighted_compl_eq_bracket` is
the whole mechanism. -/
theorem not_isTie_of_complement_bracket_beats (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    {d1 d2 d3 : Fin 6} (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3)
    (hcompl : (Cᶜ : Finset (Fin 6)) = {d1, d2, d3}) {tcap : ℝ} (hcapPos : 0 < tcap)
    (hcap : ∀ d ∈ Cᶜ, D.weight d ≤ tcap)
    (hbeat : tcap * (((Matrix.trace (∑ d ∈ Cᶜ, D.weight d • atomMatrix (D.atom d))) ^ 2
        - Matrix.trace ((∑ d ∈ Cᶜ, D.weight d • atomMatrix (D.atom d))
          * (∑ d ∈ Cᶜ, D.weight d • atomMatrix (D.atom d)))) / 2)
      < D.weight d1 * D.weight d2 * D.weight d3 * atomBracket D d1 d2 d3 ^ 2) :
    ¬ IsTie D := by
  intro htie
  have hpd := posDef_compl_of_det_gt_e2_mul_weight D C hcapPos hcap
    (by rw [det_weighted_compl_eq_bracket D C h12 h13 h23 hcompl]; exact hbeat)
  have hcard : (Cᶜ : Finset (Fin 6)).card = 3 := by
    rw [hcompl]; exact card_triple_eq h12 h13 h23
  exact htie.2 _ hcard hpd

/-! ## 9. The M-matrix producer -/

/-- **A Z-PATTERN FORM WITH A POSITIVE VECTOR IS POSITIVE DEFINITE.**  A
symmetric `3×3` matrix whose off-diagonal entries are nonpositive and which
sends SOME strictly positive vector to a strictly positive vector is positive
definite.  The proof is one scaled identity: against the weights `v` the
quadratic form splits into the three row readings plus three nonpositive
squares, so no eigenvalue and no diagonal dominance is ever named.  This is the
M-matrix criterion, in the only size the campaign needs. -/
theorem posDef_three_of_zPattern_of_posVector {gapForm : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : gapFormᵀ = gapForm)
    (h01 : gapForm 0 1 ≤ 0) (h02 : gapForm 0 2 ≤ 0) (h12 : gapForm 1 2 ≤ 0)
    {scale : Fin 3 → ℝ} (hv0 : 0 < scale 0) (hv1 : 0 < scale 1) (hv2 : 0 < scale 2)
    (hr0 : 0 < gapForm 0 0 * scale 0 + gapForm 0 1 * scale 1 + gapForm 0 2 * scale 2)
    (hr1 : 0 < gapForm 0 1 * scale 0 + gapForm 1 1 * scale 1 + gapForm 1 2 * scale 2)
    (hr2 : 0 < gapForm 0 2 * scale 0 + gapForm 1 2 * scale 1 + gapForm 2 2 * scale 2) :
    gapForm.PosDef := by
  have hs10 : gapForm 1 0 = gapForm 0 1 := by
    have h := congrFun (congrFun hsymm 0) 1
    simpa only [Matrix.transpose_apply] using h
  have hs20 : gapForm 2 0 = gapForm 0 2 := by
    have h := congrFun (congrFun hsymm 0) 2
    simpa only [Matrix.transpose_apply] using h
  have hs21 : gapForm 2 1 = gapForm 1 2 := by
    have h := congrFun (congrFun hsymm 1) 2
    simpa only [Matrix.transpose_apply] using h
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobe => ?_⟩
  rw [star_trivial]
  have hexp : probe ⬝ᵥ (gapForm *ᵥ probe)
      = gapForm 0 0 * probe 0 ^ 2 + gapForm 1 1 * probe 1 ^ 2 + gapForm 2 2 * probe 2 ^ 2
        + 2 * (gapForm 0 1 * (probe 0 * probe 1))
        + 2 * (gapForm 0 2 * (probe 0 * probe 2))
        + 2 * (gapForm 1 2 * (probe 1 * probe 2)) := by
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    rw [hs10, hs20, hs21]
    ring
  -- the scaled identity: the form against the weights is the three row readings
  -- plus three nonpositive squares
  have hid : (scale 0 * scale 1 * scale 2) * (probe ⬝ᵥ (gapForm *ᵥ probe))
      = probe 0 ^ 2 * ((scale 1 * scale 2)
            * (gapForm 0 0 * scale 0 + gapForm 0 1 * scale 1 + gapForm 0 2 * scale 2))
        + probe 1 ^ 2 * ((scale 0 * scale 2)
            * (gapForm 0 1 * scale 0 + gapForm 1 1 * scale 1 + gapForm 1 2 * scale 2))
        + probe 2 ^ 2 * ((scale 0 * scale 1)
            * (gapForm 0 2 * scale 0 + gapForm 1 2 * scale 1 + gapForm 2 2 * scale 2))
        - scale 2 * (gapForm 0 1 * (scale 1 * probe 0 - scale 0 * probe 1) ^ 2)
        - scale 1 * (gapForm 0 2 * (scale 2 * probe 0 - scale 0 * probe 2) ^ 2)
        - scale 0 * (gapForm 1 2 * (scale 2 * probe 1 - scale 1 * probe 2) ^ 2) := by
    rw [hexp]; ring
  have hneg0 : scale 2 * (gapForm 0 1 * (scale 1 * probe 0 - scale 0 * probe 1) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hv2.le (mul_nonpos_of_nonpos_of_nonneg h01 (sq_nonneg _))
  have hneg1 : scale 1 * (gapForm 0 2 * (scale 2 * probe 0 - scale 0 * probe 2) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hv1.le (mul_nonpos_of_nonpos_of_nonneg h02 (sq_nonneg _))
  have hneg2 : scale 0 * (gapForm 1 2 * (scale 2 * probe 1 - scale 1 * probe 2) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hv0.le (mul_nonpos_of_nonpos_of_nonneg h12 (sq_nonneg _))
  have hrow0 : 0 ≤ probe 0 ^ 2 * ((scale 1 * scale 2)
      * (gapForm 0 0 * scale 0 + gapForm 0 1 * scale 1 + gapForm 0 2 * scale 2)) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (mul_pos hv1 hv2).le hr0.le)
  have hrow1 : 0 ≤ probe 1 ^ 2 * ((scale 0 * scale 2)
      * (gapForm 0 1 * scale 0 + gapForm 1 1 * scale 1 + gapForm 1 2 * scale 2)) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (mul_pos hv0 hv2).le hr1.le)
  have hrow2 : 0 ≤ probe 2 ^ 2 * ((scale 0 * scale 1)
      * (gapForm 0 2 * scale 0 + gapForm 1 2 * scale 1 + gapForm 2 2 * scale 2)) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (mul_pos hv0 hv1).le hr2.le)
  have hscalepos : 0 < scale 0 * scale 1 * scale 2 := mul_pos (mul_pos hv0 hv1) hv2
  -- some coordinate is nonzero, so its row reading is strictly positive
  have hstrict : 0 < probe 0 ^ 2 * ((scale 1 * scale 2)
        * (gapForm 0 0 * scale 0 + gapForm 0 1 * scale 1 + gapForm 0 2 * scale 2))
      + probe 1 ^ 2 * ((scale 0 * scale 2)
        * (gapForm 0 1 * scale 0 + gapForm 1 1 * scale 1 + gapForm 1 2 * scale 2))
      + probe 2 ^ 2 * ((scale 0 * scale 1)
        * (gapForm 0 2 * scale 0 + gapForm 1 2 * scale 1 + gapForm 2 2 * scale 2)) := by
    obtain ⟨slot, hslot⟩ := Function.ne_iff.mp hprobe
    fin_cases slot
    · have hsq : 0 < probe 0 ^ 2 := by
        have : probe 0 ≠ 0 := hslot
        positivity
      have : 0 < probe 0 ^ 2 * ((scale 1 * scale 2)
          * (gapForm 0 0 * scale 0 + gapForm 0 1 * scale 1 + gapForm 0 2 * scale 2)) :=
        mul_pos hsq (mul_pos (mul_pos hv1 hv2) hr0)
      linarith
    · have hsq : 0 < probe 1 ^ 2 := by
        have : probe 1 ≠ 0 := hslot
        positivity
      have : 0 < probe 1 ^ 2 * ((scale 0 * scale 2)
          * (gapForm 0 1 * scale 0 + gapForm 1 1 * scale 1 + gapForm 1 2 * scale 2)) :=
        mul_pos hsq (mul_pos (mul_pos hv0 hv2) hr1)
      linarith
    · have hsq : 0 < probe 2 ^ 2 := by
        have : probe 2 ≠ 0 := hslot
        positivity
      have : 0 < probe 2 ^ 2 * ((scale 0 * scale 1)
          * (gapForm 0 2 * scale 0 + gapForm 1 2 * scale 1 + gapForm 2 2 * scale 2)) :=
        mul_pos hsq (mul_pos (mul_pos hv0 hv1) hr2)
      linarith
  nlinarith [hid, hstrict, hneg0, hneg1, hneg2, hscalepos]

/-! ## 10. The complement gap in the dual frame -/

/-- The bilinear reading of a subset gap: the subset energies minus the pairing. -/
theorem bilinear_subsetSum_sub_one (D : WeightedDesign m 3) (S : Finset (Fin m))
    (probeLeft probeRight : Fin 3 → ℝ) :
    probeLeft ⬝ᵥ ((subsetSum D S - 1) *ᵥ probeRight)
      = (∑ a ∈ S, (probeLeft ⬝ᵥ D.atom a) * (probeRight ⬝ᵥ D.atom a))
        - probeLeft ⬝ᵥ probeRight := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, subsetSum,
    Matrix.sum_mulVec, dotProduct_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show atomMatrix (D.atom a) *ᵥ probeRight = (D.atom a ⬝ᵥ probeRight) • D.atom a from
    vecMulVec_mulVec_eq _ _ _, dotProduct_smul, smul_eq_mul,
    dotProduct_comm (D.atom a) probeRight]
  ring

/-- **THE Z-PATTERN OF THE COMPLEMENT GAP.**  At the coherent horn the complement's
gap, read in the dual frame at two DIFFERENT planes, is the dual pairing of those
planes scaled by the ODDS of the atom matched to the third:

  `t_{d}·(n_e·(S_{Cᶜ}−1)·n_f) = (1 − t_{d})·(n_e·n_f)` .

Both scales are strictly positive, so the entry carries EXACTLY THE SIGN of
`n_e·n_f`.  With the three dual pairings negative the complement's gap is a
Z-matrix in this frame, and `Gtz.posDef_three_of_zPattern_of_posVector` applies
to it.  No other informative triple has this pattern. -/
theorem coherent_complGap_offDiag (D : WeightedDesign 6 3) {x y z dyz dxz dxy : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h12 : dyz ≠ dxz) (h13 : dyz ≠ dxy) (h23 : dxz ≠ dxy)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {dyz, dxz, dxy})
    (hzYZ : atomBracket D y z dyz = 0) (hzXZ : atomBracket D x z dxz = 0) :
    D.weight dxy * (atomNormal D y z ⬝ᵥ
        ((subsetSum D ((({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6))) - 1)
          *ᵥ atomNormal D z x))
      = (1 - D.weight dxy) * (atomNormal D y z ⬝ᵥ atomNormal D z x) := by
  rw [hcompl]
  have hbil := bilinear_subsetSum_sub_one D ({dyz, dxz, dxy} : Finset (Fin 6))
    (atomNormal D y z) (atomNormal D z x)
  rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
    Finset.sum_singleton] at hbil
  have hA : atomNormal D y z ⬝ᵥ D.atom dyz = 0 := by
    rw [atomNormal_dot_atom]; exact hzYZ
  have hB : atomNormal D z x ⬝ᵥ D.atom dxz = 0 := by
    rw [atomNormal_dot_atom,
      show atomBracket D z x dxz = -atomBracket D x z dxz from
        tripleBracket_swapLeft _ _ _, hzXZ, neg_zero]
  rw [hA, hB] at hbil
  have hq := coherent_offDiag_single D hxy hxz hyz h12 h13 h23 hcompl hzYZ hzXZ
  rw [hbil]
  linear_combination hq

/-- **THE DIAGONAL OF THE COMPLEMENT GAP.**  Its own matched atom is invisible to
a plane's normal, so the diagonal entry is the two surviving slot readings minus
the plane's wedge. -/
theorem coherent_complGap_diag (D : WeightedDesign 6 3) {x y z dyz dxz dxy : Fin 6}
    (h12 : dyz ≠ dxz) (h13 : dyz ≠ dxy) (h23 : dxz ≠ dxy)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {dyz, dxz, dxy})
    (hzYZ : atomBracket D y z dyz = 0) :
    atomNormal D y z ⬝ᵥ
        ((subsetSum D ((({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6))) - 1)
          *ᵥ atomNormal D y z)
      = (atomNormal D y z ⬝ᵥ D.atom dxz) ^ 2 + (atomNormal D y z ⬝ᵥ D.atom dxy) ^ 2
        - atomNormal D y z ⬝ᵥ atomNormal D y z := by
  rw [hcompl]
  have hbil := bilinear_subsetSum_sub_one D ({dyz, dxz, dxy} : Finset (Fin 6))
    (atomNormal D y z) (atomNormal D y z)
  rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
    Finset.sum_singleton] at hbil
  have hA : atomNormal D y z ⬝ᵥ D.atom dyz = 0 := by
    rw [atomNormal_dot_atom]; exact hzYZ
  rw [hA] at hbil
  rw [hbil]
  ring

/-! ## 11. The two cycles: the difference identity -/

/-- **THE DUAL-FRAME DETERMINANT.**  For any six vectors, the determinant of the
matrix of brackets `[plane, atom]` is the squared bracket of the base triple
times the bracket of the other three.  A six-term Grassmann expansion, closed by
`ring` in coordinates. -/
theorem tripleBracket_dualFrame_det (baseX baseY baseZ probeOne probeTwo probeThree : Fin 3 → ℝ) :
    tripleBracket baseX baseY baseZ ^ 2 * tripleBracket probeOne probeTwo probeThree
      = tripleBracket baseY baseZ probeOne
          * (tripleBracket baseZ baseX probeTwo * tripleBracket baseX baseY probeThree)
        + tripleBracket baseY baseZ probeTwo
          * (tripleBracket baseZ baseX probeThree * tripleBracket baseX baseY probeOne)
        + tripleBracket baseY baseZ probeThree
          * (tripleBracket baseZ baseX probeOne * tripleBracket baseX baseY probeTwo)
        - tripleBracket baseY baseZ probeOne
          * (tripleBracket baseZ baseX probeThree * tripleBracket baseX baseY probeTwo)
        - tripleBracket baseY baseZ probeTwo
          * (tripleBracket baseZ baseX probeOne * tripleBracket baseX baseY probeThree)
        - tripleBracket baseY baseZ probeThree
          * (tripleBracket baseZ baseX probeTwo * tripleBracket baseX baseY probeOne) := by
  simp only [tripleBracket_eq]
  ring

/-- **THE BRACKET IS THE SUM OF TWO CYCLES.**  At the coherent horn four of the
six Grassmann terms carry a matched atom against its own plane and vanish, so the
complement's bracket is carried by the two 3-CYCLES alone. -/
theorem coherent_bracket_two_cycles (D : WeightedDesign 6 3) {x y z dyz dxz dxy : Fin 6}
    (hzYZ : atomBracket D y z dyz = 0) (hzXZ : atomBracket D x z dxz = 0)
    (hzXY : atomBracket D x y dxy = 0) :
    atomBracket D x y z ^ 2 * atomBracket D dyz dxz dxy
      = (atomNormal D y z ⬝ᵥ D.atom dxz)
          * ((atomNormal D z x ⬝ᵥ D.atom dxy) * (atomNormal D x y ⬝ᵥ D.atom dyz))
        + (atomNormal D y z ⬝ᵥ D.atom dxy)
          * ((atomNormal D z x ⬝ᵥ D.atom dyz) * (atomNormal D x y ⬝ᵥ D.atom dxz)) := by
  have hzZX : atomBracket D z x dxz = 0 := by
    rw [show atomBracket D z x dxz = -atomBracket D x z dxz from
      tripleBracket_swapLeft _ _ _, hzXZ, neg_zero]
  have hgen : atomBracket D x y z ^ 2 * atomBracket D dyz dxz dxy
      = atomBracket D y z dyz * (atomBracket D z x dxz * atomBracket D x y dxy)
        + atomBracket D y z dxz * (atomBracket D z x dxy * atomBracket D x y dyz)
        + atomBracket D y z dxy * (atomBracket D z x dyz * atomBracket D x y dxz)
        - atomBracket D y z dyz * (atomBracket D z x dxy * atomBracket D x y dxz)
        - atomBracket D y z dxz * (atomBracket D z x dyz * atomBracket D x y dxy)
        - atomBracket D y z dxy * (atomBracket D z x dxz * atomBracket D x y dyz) :=
    tripleBracket_dualFrame_det (D.atom x) (D.atom y) (D.atom z)
      (D.atom dyz) (D.atom dxz) (D.atom dxy)
  simp only [atomNormal_dot_atom]
  rw [hgen, hzYZ, hzZX, hzXY]
  ring

/-- **THE CYCLE CROSS PRODUCT.**  The two cycles multiply, against the three
matched weights, to the product of the three dual pairings — with its sign.
Three instances of the single off-diagonal law, multiplied. -/
theorem coherent_cycle_cross (D : WeightedDesign 6 3) {x y z dyz dxz dxy : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h12 : dyz ≠ dxz) (h13 : dyz ≠ dxy) (h23 : dxz ≠ dxy)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {dyz, dxz, dxy})
    (hzYZ : atomBracket D y z dyz = 0) (hzXZ : atomBracket D x z dxz = 0)
    (hzXY : atomBracket D x y dxy = 0) :
    (D.weight dyz * (D.weight dxz * D.weight dxy))
        * (((atomNormal D y z ⬝ᵥ D.atom dxz)
              * ((atomNormal D z x ⬝ᵥ D.atom dxy) * (atomNormal D x y ⬝ᵥ D.atom dyz)))
          * ((atomNormal D y z ⬝ᵥ D.atom dxy)
              * ((atomNormal D z x ⬝ᵥ D.atom dyz) * (atomNormal D x y ⬝ᵥ D.atom dxz))))
      = (atomNormal D y z ⬝ᵥ atomNormal D z x)
        * ((atomNormal D z x ⬝ᵥ atomNormal D x y)
          * (atomNormal D x y ⬝ᵥ atomNormal D y z)) := by
  have hCy : (({y, z, x} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {dxz, dxy, dyz} := by
    rw [show ({y, z, x} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto, hcompl]
    ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hCz : (({z, x, y} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {dxy, dyz, dxz} := by
    rw [show ({z, x, y} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto, hcompl]
    ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hzZX : atomBracket D z x dxz = 0 := by
    rw [show atomBracket D z x dxz = -atomBracket D x z dxz from
      tripleBracket_swapLeft _ _ _, hzXZ, neg_zero]
  have hzYX : atomBracket D y x dxy = 0 := by
    rw [show atomBracket D y x dxy = -atomBracket D x y dxy from
      tripleBracket_swapLeft _ _ _, hzXY, neg_zero]
  have hzZY : atomBracket D z y dyz = 0 := by
    rw [show atomBracket D z y dyz = -atomBracket D y z dyz from
      tripleBracket_swapLeft _ _ _, hzYZ, neg_zero]
  have hqA := coherent_offDiag_single D hxy hxz hyz h12 h13 h23 hcompl hzYZ hzXZ
  have hqB := coherent_offDiag_single D hyz (Ne.symm hxy) (Ne.symm hxz)
    h23 (Ne.symm h12) (Ne.symm h13) hCy hzZX hzYX
  have hqC := coherent_offDiag_single D (Ne.symm hxz) (Ne.symm hyz) hxy
    (Ne.symm h13) (Ne.symm h23) h12 hCz hzXY hzZY
  rw [← hqA, ← hqB, ← hqC]
  ring

/-- **THE DIFFERENCE IDENTITY.**  The weighted squared bracket of the complement
equals the two cycle energies PLUS TWICE the product of the three dual pairings:

  `t·t·t·[xyz]⁴·[d d' d'']² = P + Q + 2·Π` ,

`P`, `Q` the products of the three first and the three second slot energies and
`Π` the product of the three dual pairings.  Since `P·Q = Π²`, the right side is
`(√P − √Q)²` exactly when `Π < 0` — which the coherent sign pattern forces.  So
the bracket is the DIFFERENCE of the two cycles, and near the boundary the two
cycles cancel: that is why the bracket is quadratically small there, and why an
AM–GM bound that sees only the plane totals is weak. -/
theorem coherent_difference_identity (D : WeightedDesign 6 3) {x y z dyz dxz dxy : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h12 : dyz ≠ dxz) (h13 : dyz ≠ dxy) (h23 : dxz ≠ dxy)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {dyz, dxz, dxy})
    (hzYZ : atomBracket D y z dyz = 0) (hzXZ : atomBracket D x z dxz = 0)
    (hzXY : atomBracket D x y dxy = 0) :
    (D.weight dyz * (D.weight dxz * D.weight dxy))
        * (atomBracket D x y z ^ 2 * atomBracket D dyz dxz dxy) ^ 2
      = (D.weight dxz * (atomNormal D y z ⬝ᵥ D.atom dxz) ^ 2)
          * ((D.weight dxy * (atomNormal D z x ⬝ᵥ D.atom dxy) ^ 2)
            * (D.weight dyz * (atomNormal D x y ⬝ᵥ D.atom dyz) ^ 2))
        + (D.weight dxy * (atomNormal D y z ⬝ᵥ D.atom dxy) ^ 2)
          * ((D.weight dyz * (atomNormal D z x ⬝ᵥ D.atom dyz) ^ 2)
            * (D.weight dxz * (atomNormal D x y ⬝ᵥ D.atom dxz) ^ 2))
        + 2 * ((atomNormal D y z ⬝ᵥ atomNormal D z x)
            * ((atomNormal D z x ⬝ᵥ atomNormal D x y)
              * (atomNormal D x y ⬝ᵥ atomNormal D y z))) := by
  have hcyc := coherent_bracket_two_cycles D hzYZ hzXZ hzXY
  have hcross := coherent_cycle_cross D hxy hxz hyz h12 h13 h23 hcompl hzYZ hzXZ hzXY
  rw [hcyc, ← hcross]
  ring

/-! ## 12. The exact plane-product law: AM–GM removed -/

/-- **THE EXACT PRODUCT LAW OF THE PLANE TOTALS.**  Expand the three diagonal
totals and regroup by MATCHED ATOM: every one of the six mixed terms carries one
of the three atom pairs, so it is a squared dual pairing times the remaining
plane total.  The result is an IDENTITY

  `D_x·D_y·D_z = P + Q + Π_xy·D_z + Π_yz·D_x + Π_zx·D_y` ,

with `P`, `Q` the two cycle energies and `Π_ef` the squared dual pairings.  It
replaces the AM–GM step of `Gtz.coherent_amgm_law` WITH NO LOSS, and through
`Gtz.coherent_difference_identity` — which prices `P + Q` by the complement's
bracket — it reads the plane totals directly against the bracket budget. -/
theorem coherent_plane_product_identity (D : WeightedDesign 6 3) {x y z dyz dxz dxy : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h12 : dyz ≠ dxz) (h13 : dyz ≠ dxy) (h23 : dxz ≠ dxy)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {dyz, dxz, dxy})
    (hzYZ : atomBracket D y z dyz = 0) (hzXZ : atomBracket D x z dxz = 0)
    (hzXY : atomBracket D x y dxy = 0) :
    (atomNormal D y z ⬝ᵥ atomNormal D y z - D.weight x * atomBracket D x y z ^ 2)
        * ((atomNormal D z x ⬝ᵥ atomNormal D z x - D.weight y * atomBracket D x y z ^ 2)
          * (atomNormal D x y ⬝ᵥ atomNormal D x y - D.weight z * atomBracket D x y z ^ 2))
      = (D.weight dxz * (atomNormal D y z ⬝ᵥ D.atom dxz) ^ 2)
            * ((D.weight dxy * (atomNormal D z x ⬝ᵥ D.atom dxy) ^ 2)
              * (D.weight dyz * (atomNormal D x y ⬝ᵥ D.atom dyz) ^ 2))
        + (D.weight dxy * (atomNormal D y z ⬝ᵥ D.atom dxy) ^ 2)
            * ((D.weight dyz * (atomNormal D z x ⬝ᵥ D.atom dyz) ^ 2)
              * (D.weight dxz * (atomNormal D x y ⬝ᵥ D.atom dxz) ^ 2))
        + (atomNormal D y z ⬝ᵥ atomNormal D z x) ^ 2
            * (atomNormal D x y ⬝ᵥ atomNormal D x y - D.weight z * atomBracket D x y z ^ 2)
        + (atomNormal D z x ⬝ᵥ atomNormal D x y) ^ 2
            * (atomNormal D y z ⬝ᵥ atomNormal D y z - D.weight x * atomBracket D x y z ^ 2)
        + (atomNormal D x y ⬝ᵥ atomNormal D y z) ^ 2
            * (atomNormal D z x ⬝ᵥ atomNormal D z x
                - D.weight y * atomBracket D x y z ^ 2) := by
  have hCy : (({y, z, x} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {dxz, dxy, dyz} := by
    rw [show ({y, z, x} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto, hcompl]
    ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hCz : (({z, x, y} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {dxy, dyz, dxz} := by
    rw [show ({z, x, y} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto, hcompl]
    ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hbY : atomBracket D y z x = atomBracket D x y z := (atomBracket_cycle D x y z).symm
  have hbZ : atomBracket D z x y = atomBracket D x y z := by rw [atomBracket_cycle D z x y]
  have hzZX : atomBracket D z x dxz = 0 := by
    rw [show atomBracket D z x dxz = -atomBracket D x z dxz from
      tripleBracket_swapLeft _ _ _, hzXZ, neg_zero]
  have hzYX : atomBracket D y x dxy = 0 := by
    rw [show atomBracket D y x dxy = -atomBracket D x y dxy from
      tripleBracket_swapLeft _ _ _, hzXY, neg_zero]
  have hzZY : atomBracket D z y dyz = 0 := by
    rw [show atomBracket D z y dyz = -atomBracket D y z dyz from
      tripleBracket_swapLeft _ _ _, hzYZ, neg_zero]
  have hdX := coherent_diag_pair D hxy hxz hyz h12 h13 h23 hcompl hzYZ
  have hdY := coherent_diag_pair D hyz (Ne.symm hxy) (Ne.symm hxz)
    h23 (Ne.symm h12) (Ne.symm h13) hCy hzZX
  have hdZ := coherent_diag_pair D (Ne.symm hxz) (Ne.symm hyz) hxy
    (Ne.symm h13) (Ne.symm h23) h12 hCz hzXY
  rw [hbY] at hdY
  rw [hbZ] at hdZ
  have hpA := coherent_slot_product D hxy hxz hyz h12 h13 h23 hcompl hzYZ hzXZ
  have hpB := coherent_slot_product D hyz (Ne.symm hxy) (Ne.symm hxz)
    h23 (Ne.symm h12) (Ne.symm h13) hCy hzZX hzYX
  have hpC := coherent_slot_product D (Ne.symm hxz) (Ne.symm hyz) hxy
    (Ne.symm h13) (Ne.symm h23) h12 hCz hzXY hzZY
  rw [← hdX, ← hdY, ← hdZ, ← hpA, ← hpB, ← hpC]
  ring

/-! ## 13. The congruence, and the complement certificate -/

/-- **CONGRUENCE REFLECTS POSITIVE DEFINITENESS.**  If an invertible congruence
of a symmetric form is positive definite, so is the form. -/
theorem posDef_of_posDef_congr {form frame : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : formᵀ = form) (hdet : IsUnit frame.det)
    (hcong : (frameᵀ * form * frame).PosDef) : form.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobe => ?_⟩
  rw [star_trivial]
  set pull : Fin 3 → ℝ := frame⁻¹ *ᵥ probe with hpull
  have hframePull : frame *ᵥ pull = probe := by
    rw [hpull, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv frame hdet, Matrix.one_mulVec]
  have hpullne : pull ≠ 0 := by
    intro hzero
    rw [hzero, Matrix.mulVec_zero] at hframePull
    exact hprobe hframePull.symm
  have hstep : (frameᵀ * form * frame) *ᵥ pull = frameᵀ *ᵥ (form *ᵥ probe) := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hframePull]
  have hform : pull ⬝ᵥ ((frameᵀ * form * frame) *ᵥ pull) = probe ⬝ᵥ (form *ᵥ probe) := by
    rw [hstep, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hframePull]
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hcong).2 hpullne
  rw [star_trivial, hform] at hpos
  exact hpos

/-- The frame whose three columns are the dual normals of a triple. -/
noncomputable def dualNormalFrame (D : WeightedDesign m 3) (x y z : Fin m) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun coord slot =>
    (![atomNormal D y z, atomNormal D z x, atomNormal D x y] slot) coord

/-- **THE DUAL FRAME HAS THE SQUARED BRACKET AS DETERMINANT.**  The classical
`det[b×c, c×a, a×b] = [abc]²`: the dual frame is invertible exactly when the
triple spans. -/
theorem det_dualNormalFrame (D : WeightedDesign m 3) (x y z : Fin m) :
    (dualNormalFrame D x y z).det = atomBracket D x y z ^ 2 := by
  simp only [dualNormalFrame, Matrix.det_fin_three, Matrix.of_apply, atomNormal,
    bracketNormal, atomBracket, tripleBracket_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The congruence of a form by the dual frame reads the form at the normals. -/
theorem dualNormalFrame_congr_apply (D : WeightedDesign m 3) (x y z : Fin m)
    (form : Matrix (Fin 3) (Fin 3) ℝ) (rowSlot colSlot : Fin 3) :
    ((dualNormalFrame D x y z)ᵀ * form * dualNormalFrame D x y z) rowSlot colSlot
      = (![atomNormal D y z, atomNormal D z x, atomNormal D x y] rowSlot) ⬝ᵥ
        (form *ᵥ (![atomNormal D y z, atomNormal D z x, atomNormal D x y] colSlot)) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dualNormalFrame, Matrix.of_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- **THE COMPLEMENT CERTIFICATE.**  At a `(6,3)` corner whose triple spans, if
the complement's gap read in the dual frame has nonpositive off-diagonal entries
and sends one strictly positive vector to a strictly positive vector, then the
complement DOMINATES STRICTLY.  The Z-pattern is supplied by
`Gtz.coherent_complGap_offDiag`, whose entries carry the sign of the dual
pairings; the producer is `Gtz.posDef_three_of_zPattern_of_posVector`; and the
congruence is invertible because its determinant is the squared bracket. -/
theorem posDef_compl_of_dualFrame_certificate (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) {x y z : Fin 6} (hspan : atomBracket D x y z ≠ 0)
    (h01 : ((dualNormalFrame D x y z)ᵀ * (subsetSum D Cᶜ - 1)
      * dualNormalFrame D x y z) 0 1 ≤ 0)
    (h02 : ((dualNormalFrame D x y z)ᵀ * (subsetSum D Cᶜ - 1)
      * dualNormalFrame D x y z) 0 2 ≤ 0)
    (h12 : ((dualNormalFrame D x y z)ᵀ * (subsetSum D Cᶜ - 1)
      * dualNormalFrame D x y z) 1 2 ≤ 0)
    {scale : Fin 3 → ℝ} (hv0 : 0 < scale 0) (hv1 : 0 < scale 1) (hv2 : 0 < scale 2)
    (hr0 : 0 < ((dualNormalFrame D x y z)ᵀ * (subsetSum D Cᶜ - 1)
          * dualNormalFrame D x y z) 0 0 * scale 0
        + ((dualNormalFrame D x y z)ᵀ * (subsetSum D Cᶜ - 1)
          * dualNormalFrame D x y z) 0 1 * scale 1
        + ((dualNormalFrame D x y z)ᵀ * (subsetSum D Cᶜ - 1)
          * dualNormalFrame D x y z) 0 2 * scale 2)
    (hr1 : 0 < ((dualNormalFrame D x y z)ᵀ * (subsetSum D Cᶜ - 1)
          * dualNormalFrame D x y z) 0 1 * scale 0
        + ((dualNormalFrame D x y z)ᵀ * (subsetSum D Cᶜ - 1)
          * dualNormalFrame D x y z) 1 1 * scale 1
        + ((dualNormalFrame D x y z)ᵀ * (subsetSum D Cᶜ - 1)
          * dualNormalFrame D x y z) 1 2 * scale 2)
    (hr2 : 0 < ((dualNormalFrame D x y z)ᵀ * (subsetSum D Cᶜ - 1)
          * dualNormalFrame D x y z) 0 2 * scale 0
        + ((dualNormalFrame D x y z)ᵀ * (subsetSum D Cᶜ - 1)
          * dualNormalFrame D x y z) 1 2 * scale 1
        + ((dualNormalFrame D x y z)ᵀ * (subsetSum D Cᶜ - 1)
          * dualNormalFrame D x y z) 2 2 * scale 2) :
    (subsetSum D Cᶜ - 1).PosDef := by
  have hgapsymm : (subsetSum D Cᶜ - 1)ᵀ = subsetSum D Cᶜ - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum_transpose]
  have hcongsymm : ((dualNormalFrame D x y z)ᵀ * (subsetSum D Cᶜ - 1)
      * dualNormalFrame D x y z)ᵀ
      = (dualNormalFrame D x y z)ᵀ * (subsetSum D Cᶜ - 1) * dualNormalFrame D x y z := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hgapsymm, Matrix.mul_assoc]
  have hdet : IsUnit (dualNormalFrame D x y z).det := by
    rw [det_dualNormalFrame]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hspan)
  exact posDef_of_posDef_congr hgapsymm hdet
    (posDef_three_of_zPattern_of_posVector hcongsymm h01 h02 h12 hv0 hv1 hv2 hr0 hr1 hr2)

/-- **THE COHERENT COMPLEMENT KILL.**  A `(6,3)` design whose complement gap
carries a dual-frame certificate is NO TIE. -/
theorem not_isTie_of_dualFrame_certificate (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    {d1 d2 d3 : Fin 6} (h12' : d1 ≠ d2) (h13' : d1 ≠ d3) (h23' : d2 ≠ d3)
    (hcompl : (Cᶜ : Finset (Fin 6)) = {d1, d2, d3})
    (hpd : (subsetSum D Cᶜ - 1).PosDef) : ¬ IsTie D := by
  intro htie
  have hcard : (Cᶜ : Finset (Fin 6)).card = 3 := by
    rw [hcompl]; exact card_triple_eq h12' h13' h23'
  exact htie.2 _ hcard hpd

end Gtz
