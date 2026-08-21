/-
# The pair normals of a design are a Parseval frame

Parseval read once says the weighted atoms resolve the identity.  This module
reads it TWICE: the weighted PAIR NORMALS `g_i × g_j`, carrying the product
weights `t_i·t_j`, resolve the identity as well.  The polarized form is one law
over ordered pairs, for every pair of probes:

  **`Σᵢ Σⱼ tᵢtⱼ·[v gᵢ gⱼ]·[w gᵢ gⱼ] = 2·⟨v,w⟩`**  (`Gtz.pairNormal_parseval_polar`)

The proof is elementary and self-contained: rotate each bracket onto its own
pair normal (`tripleBracket_eq_bracketNormal_dotProduct`), spend Parseval at
the rotated probes, close with the Lagrange polarization, and spend Parseval
once more.  No compound matrices, no Cauchy–Binet, no determinants of sums.

## What sits below this law

Both landed budgets are its shadows.  Tracing over an orthonormal basis of
probes gives the wedge budget `Σ tᵢtⱼ·wᵢⱼ = 6` (`Gtz.wedge_mass_budget`),
because three basis probes carry mass `2·3`.  Averaging the atom instance over
the design gives the bracket budget `Σ tₐt_bt_c·[abc]² = 6`
(`Gtz.bracket_budget`), because an ordered triple is counted once for each slot
that plays the probe.

## What is new

The probe is FREE.  `Gtz.probe_pairNormal_mass` prices the pair bracket mass
of ANY vector at twice its squared length.  The landed
`Gtz.pair_bracket_mass` prices the mass through a PAIR against the design's
atoms; this law prices the mass through a VECTOR against the design's pairs.
The two index patterns are complementary readings of one frame.

Every unit probe carries mass exactly two (`Gtz.unitProbe_pairNormal_mass`).
The corner axis of the corank-two arm is a unit vector, so its pair bracket
mass is two — independent of the corner scale.  A unit null probe of the
corank-one arm obeys the same law.  The distinguished vectors of the two arms
obey one statement that consumes no corner equation and no tie hypothesis.

[MEASURED at machine precision before proving: the matrix identity
`Σ_{i<j} tᵢtⱼ·nᵢⱼnᵢⱼᵀ = 1` at residual `2.2e-16` for sizes 5, 6, 7; the polar
law at `1.1e-16`; the atom law at `8.9e-16`; the corner axis mass at
`2.000000000000` on an explicit corner.]
-/
import Gtz.Wave.PairMinorBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

variable {m : ℕ}

/-! ## 1. Parseval, polarized -/

/-- The trace of an atom matrix against a rank-one frame is the product of the
two readings of the atom. -/
theorem trace_atomMatrix_mul_vecMulVec (g y x : Fin 3 → ℝ) :
    Matrix.trace (atomMatrix g * Matrix.vecMulVec y x)
      = (g ⬝ᵥ x) * (g ⬝ᵥ y) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, atomMatrix,
    Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- The trace of a rank-one frame is the inner product of its two legs. -/
theorem trace_vecMulVec' (y x : Fin 3 → ℝ) :
    Matrix.trace (Matrix.vecMulVec y x) = x ⬝ᵥ y := by
  simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, dotProduct,
    Fin.sum_univ_three]
  ring

/-- **PARSEVAL AT TWO PROBES.**  The weighted products of the atom readings
resolve the inner product of the probes. -/
theorem parseval_bilinear (D : WeightedDesign m 3) (x y : Fin 3 → ℝ) :
    ∑ c, D.weight c * ((D.atom c ⬝ᵥ x) * (D.atom c ⬝ᵥ y)) = x ⬝ᵥ y := by
  have h := congrArg
    (fun M : Matrix (Fin 3) (Fin 3) ℝ => Matrix.trace (M * Matrix.vecMulVec y x))
    D.isParseval
  simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.one_mul, smul_mul_assoc,
    Matrix.trace_smul, smul_eq_mul, trace_atomMatrix_mul_vecMulVec,
    trace_vecMulVec'] at h
  exact h

/-! ## 2. The Lagrange polarization -/

/-- The polarized Lagrange identity: the pairing of two pair normals over one
shared leg reads the probes through the leg. -/
theorem bracketNormal_dot_bracketNormal (v w a : Fin 3 → ℝ) :
    bracketNormal v a ⬝ᵥ bracketNormal w a
      = (v ⬝ᵥ w) * (a ⬝ᵥ a) - (v ⬝ᵥ a) * (w ⬝ᵥ a) := by
  simp only [bracketNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## 3. The frame law -/

/-- **THE PAIR NORMALS ARE A PARSEVAL FRAME, POLARIZED.**  Over ordered pairs
the weighted bracket products against two probes resolve twice the inner
product of the probes.  The diagonal contributes zero by itself, so the
unordered pair normals resolve the inner product exactly. -/
theorem pairNormal_parseval_polar (D : WeightedDesign m 3) (v w : Fin 3 → ℝ) :
    ∑ i, ∑ j, D.weight i * (D.weight j
        * (tripleBracket v (D.atom i) (D.atom j)
            * tripleBracket w (D.atom i) (D.atom j)))
      = 2 * (v ⬝ᵥ w) := by
  have hrow : ∀ i : Fin m, ∑ j, D.weight j
      * (tripleBracket v (D.atom i) (D.atom j)
          * tripleBracket w (D.atom i) (D.atom j))
      = (v ⬝ᵥ w) * (D.atom i ⬝ᵥ D.atom i)
          - (v ⬝ᵥ D.atom i) * (w ⬝ᵥ D.atom i) := by
    intro i
    have hread : ∀ j : Fin m,
        tripleBracket v (D.atom i) (D.atom j)
            * tripleBracket w (D.atom i) (D.atom j)
          = (D.atom j ⬝ᵥ bracketNormal v (D.atom i))
              * (D.atom j ⬝ᵥ bracketNormal w (D.atom i)) := by
      intro j
      rw [tripleBracket_eq_bracketNormal_dotProduct,
        tripleBracket_eq_bracketNormal_dotProduct,
        dotProduct_comm (bracketNormal v (D.atom i)),
        dotProduct_comm (bracketNormal w (D.atom i))]
    calc ∑ j, D.weight j
        * (tripleBracket v (D.atom i) (D.atom j)
            * tripleBracket w (D.atom i) (D.atom j))
        = ∑ j, D.weight j
            * ((D.atom j ⬝ᵥ bracketNormal v (D.atom i))
                * (D.atom j ⬝ᵥ bracketNormal w (D.atom i))) := by
          exact Finset.sum_congr rfl fun j _ => by rw [hread j]
      _ = bracketNormal v (D.atom i) ⬝ᵥ bracketNormal w (D.atom i) :=
          parseval_bilinear D _ _
      _ = (v ⬝ᵥ w) * (D.atom i ⬝ᵥ D.atom i)
            - (v ⬝ᵥ D.atom i) * (w ⬝ᵥ D.atom i) :=
          bracketNormal_dot_bracketNormal v w (D.atom i)
  have hlev : ∑ c, D.weight c * (D.atom c ⬝ᵥ D.atom c) = 3 := by
    have h := sum_weighted_leverage D
    calc ∑ c, D.weight c * (D.atom c ⬝ᵥ D.atom c)
        = ∑ c, D.weight c * leverageOf (D.atom c) :=
          Finset.sum_congr rfl fun c _ => by
            rw [dotProduct_self_eq_leverage]
      _ = 3 := h
  have hvw : ∑ c, D.weight c * ((D.atom c ⬝ᵥ v) * (D.atom c ⬝ᵥ w)) = v ⬝ᵥ w :=
    parseval_bilinear D v w
  calc ∑ i, ∑ j, D.weight i * (D.weight j
        * (tripleBracket v (D.atom i) (D.atom j)
            * tripleBracket w (D.atom i) (D.atom j)))
      = ∑ i, D.weight i * (∑ j, D.weight j
          * (tripleBracket v (D.atom i) (D.atom j)
              * tripleBracket w (D.atom i) (D.atom j))) := by
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ = ∑ i, D.weight i * ((v ⬝ᵥ w) * (D.atom i ⬝ᵥ D.atom i)
          - (v ⬝ᵥ D.atom i) * (w ⬝ᵥ D.atom i)) := by
        exact Finset.sum_congr rfl fun i _ => by rw [hrow i]
    _ = (v ⬝ᵥ w) * (∑ c, D.weight c * (D.atom c ⬝ᵥ D.atom c))
          - ∑ c, D.weight c * ((D.atom c ⬝ᵥ v) * (D.atom c ⬝ᵥ w)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c _ => by
          rw [dotProduct_comm (D.atom c) v, dotProduct_comm (D.atom c) w]
          ring
    _ = (v ⬝ᵥ w) * 3 - (v ⬝ᵥ w) := by rw [hlev, hvw]
    _ = 2 * (v ⬝ᵥ w) := by ring

/-! ## 4. The free probe -/

/-- **THE PAIR BRACKET MASS OF ANY VECTOR IS TWICE ITS SQUARED LENGTH.**  Over
ordered pairs.  The probe is arbitrary — on the design or off it. -/
theorem probe_pairNormal_mass (D : WeightedDesign m 3) (v : Fin 3 → ℝ) :
    ∑ i, ∑ j, D.weight i * (D.weight j
        * tripleBracket v (D.atom i) (D.atom j) ^ 2)
      = 2 * (v ⬝ᵥ v) := by
  have h := pairNormal_parseval_polar D v v
  calc ∑ i, ∑ j, D.weight i * (D.weight j
        * tripleBracket v (D.atom i) (D.atom j) ^ 2)
      = ∑ i, ∑ j, D.weight i * (D.weight j
          * (tripleBracket v (D.atom i) (D.atom j)
              * tripleBracket v (D.atom i) (D.atom j))) := by
        exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by ring
    _ = 2 * (v ⬝ᵥ v) := h

/-- The atom instance: the pair bracket mass through an atom is twice its
leverage. -/
theorem atom_pairNormal_mass (D : WeightedDesign m 3) (c : Fin m) :
    ∑ i, ∑ j, D.weight i * (D.weight j
        * tripleBracket (D.atom c) (D.atom i) (D.atom j) ^ 2)
      = 2 * leverageOf (D.atom c) := by
  rw [probe_pairNormal_mass D (D.atom c), dotProduct_self_eq_leverage]

/-- **EVERY UNIT PROBE CARRIES PAIR BRACKET MASS EXACTLY TWO.**  The corner
axis and a unit null probe are unit vectors, so the distinguished directions
of the two corank arms obey this one law — with no corner equation and no tie
hypothesis. -/
theorem unitProbe_pairNormal_mass (D : WeightedDesign m 3) (v : Fin 3 → ℝ)
    (hv : v ⬝ᵥ v = 1) :
    ∑ i, ∑ j, D.weight i * (D.weight j
        * tripleBracket v (D.atom i) (D.atom j) ^ 2)
      = 2 := by
  rw [probe_pairNormal_mass D v, hv, mul_one]

end Gtz
