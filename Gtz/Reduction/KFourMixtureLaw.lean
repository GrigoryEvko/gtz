import Gtz.Reduction.KFourTreeAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16384

/-
# P1: the mixture law at M(K4) -- `sum_T P_T S_T >= B`, semidefinite form

Mechanization of the matroid lane's rung-11 law P1
(the M(K4) matroid-lane ledger): the fractional selection at the
matrix-tree marginals dominates the frame,
  `sum_T (prod_T m) * S_T  >=  det B * B`
as quadratic forms, where `S_T` carries conductances `y = m/w` on the
tree edges and `P_T = prod_T m / det B` are the matrix-tree tree
probabilities.  Since the edge marginal of `P` is the leverage
(`sum_{T through c} prod_T m = m_c F_c(m)`, step alpha), the left side
collapses to `sum_c y_c m_c F_c(m) (drop_c x)^2`, and the pen proof is
matrix Cauchy-Schwarz against `B^{-1}`.

Kernel route, division-free and spectral-theory-free: the adjugate of the
K4 Laplacian is the Cauchy-Binet sum of cross-product squares, so the
matrix Cauchy-Schwarz decomposes over the fifteen edge pairs into scalar
Lagrange identities.  The whole law is then ONE homogeneous polynomial
identity
  `RHS * (sum w) - LHS = sum of 186 manifestly nonnegative products`
closed by `ring`, plus sign bookkeeping.  This is the SEMIDEFINITE form;
the ledger's strict form (equality impossible at nonzero probes, since
any five of the six K4 directions span) is left to a successor lane.
-/

namespace Gtz

open Matrix

/-- The mixture aggregate collapses to leverage form: the quadratic form
of `sum_T (prod_T m) S_T` at a probe equals
`sum_c y_c m_c F_c(m) (drop_c x)^2` -- step alpha in aggregate. -/
theorem kFour_mixture_treeForm_expansion (conductance weight : Fin 6 → ℝ)
    (probe : Fin 3 → ℝ) :
    (k4TreeTriples.map fun tree =>
        kFourTreeWeightProduct (fun edge => conductance edge * weight edge) tree
          * (conductance tree.1 * k4Drop probe tree.1 ^ 2
            + conductance tree.2.1 * k4Drop probe tree.2.1 ^ 2
            + conductance tree.2.2 * k4Drop probe tree.2.2 ^ 2)).sum
      = ∑ edge, conductance edge * (conductance edge * weight edge)
          * kFourEdgeCompanionSum (fun other => conductance other * weight other)
              edge
          * k4Drop probe edge ^ 2 := by
  simp only [k4TreeTriples, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, kFourTreeWeightProduct, kFourEdgeCompanionSum,
    Fin.sum_univ_six, k4Drop_zero, k4Drop_one, k4Drop_two, k4Drop_three,
    k4Drop_four, k4Drop_five]
  ring

/-- **P1, leverage form.**  For nonnegative conductances and simplex
weights, at every probe:
`det B * (x^T B x) <= sum_c y_c m_c F_c(m) (drop_c x)^2`. -/
theorem kFour_mixtureLaw_leverageForm (conductance weight : Fin 6 → ℝ)
    (probe : Fin 3 → ℝ)
    (hcond : ∀ edge, 0 ≤ conductance edge) (hw : ∀ edge, 0 ≤ weight edge)
    (hsum : ∑ edge, weight edge = 1) :
    kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
        * (probe ⬝ᵥ (kFourWeightLaplacian
            (fun edge => conductance edge * weight edge)).mulVec probe)
      ≤ ∑ edge, conductance edge * (conductance edge * weight edge)
          * kFourEdgeCompanionSum (fun other => conductance other * weight other)
              edge
          * k4Drop probe edge ^ 2 := by
  have hsix : weight 0 + weight 1 + weight 2 + weight 3 + weight 4
      + weight 5 = 1 := by
    simpa [Fin.sum_univ_six] using hsum
  have hkey : (∑ edge, conductance edge * (conductance edge * weight edge)
          * kFourEdgeCompanionSum (fun other => conductance other * weight other)
              edge
          * k4Drop probe edge ^ 2)
        * (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5)
      - kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * (probe ⬝ᵥ (kFourWeightLaplacian
              (fun edge => conductance edge * weight edge)).mulVec probe)
      = conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 0 * weight 2) * (conductance 2 * probe 2) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 0 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 0 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 1 * weight 2) * (conductance 2 * probe 2) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 1 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 1 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 2 * weight 3) * (conductance 2 * probe 2) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 2 * weight 4) * (conductance 2 * probe 2 - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 2 * weight 5) * (conductance 2 * probe 2 - (-(conductance 5 * (probe 1 - probe 2)))) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 3 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 3 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 4 * weight 5) * (-(conductance 4 * (probe 0 - probe 2)) - (-(conductance 5 * (probe 1 - probe 2)))) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 0 * weight 1) * (-(conductance 1 * probe 1)) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 0 * weight 3) * (conductance 3 * (probe 0 - probe 1)) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 0 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 1 * weight 2) * (-(conductance 1 * probe 1)) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 1 * weight 3) * (-(conductance 1 * probe 1) - (conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 1 * weight 4) * (-(conductance 1 * probe 1)) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 1 * weight 5) * (-(conductance 1 * probe 1) - (-(conductance 5 * (probe 1 - probe 2)))) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 2 * weight 3) * (conductance 3 * (probe 0 - probe 1)) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 2 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 3 * weight 4) * (conductance 3 * (probe 0 - probe 1)) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 3 * weight 5) * (conductance 3 * (probe 0 - probe 1) - (-(conductance 5 * (probe 1 - probe 2)))) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 4 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 0 * weight 2) * (-(conductance 2 * probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 0 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 0 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 1 * weight 2) * (-(conductance 2 * probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 1 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 1 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 2 * weight 3) * (-(conductance 2 * probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 2 * weight 4) * (-(conductance 2 * probe 2) - (conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 2 * weight 5) * (-(conductance 2 * probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 3 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 3 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 4 * weight 5) * (conductance 4 * (probe 0 - probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 0 * weight 1) * (conductance 1 * probe 1) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 0 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 0 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 1 * weight 2) * (conductance 1 * probe 1) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 1 * weight 3) * (conductance 1 * probe 1 - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 1 * weight 5) * (conductance 1 * probe 1 - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 2 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 2 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1)) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 4 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (conductance 1 * probe 1) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (conductance 2 * probe 2) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 1 * weight 2) * (conductance 1 * probe 1 - (conductance 2 * probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (conductance 1 * probe 1 - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (conductance 1 * probe 1 - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 1 * weight 5) * (conductance 1 * probe 1) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (conductance 2 * probe 2 - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (conductance 2 * probe 2 - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 2 * weight 5) * (conductance 2 * probe 2) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1)) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 4 * weight 5) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 1) * (conductance 0 * probe 0) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 2) * (conductance 0 * probe 0) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 3) * (conductance 0 * probe 0 - (conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 4) * (conductance 0 * probe 0 - (conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 5) * (conductance 0 * probe 0) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 1 * weight 3) * (conductance 3 * (probe 0 - probe 1)) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 1 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 2 * weight 3) * (conductance 3 * (probe 0 - probe 1)) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 2 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 3 * weight 4) * (conductance 3 * (probe 0 - probe 1) - (conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 3 * weight 5) * (conductance 3 * (probe 0 - probe 1)) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 4 * weight 5) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 0 * weight 2) * (-(conductance 2 * probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 0 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 0 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 1 * weight 2) * (-(conductance 2 * probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 1 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 1 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 2 * weight 3) * (-(conductance 2 * probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 2 * weight 4) * (-(conductance 2 * probe 2) - (conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 2 * weight 5) * (-(conductance 2 * probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 3 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 3 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 4 * weight 5) * (conductance 4 * (probe 0 - probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 1) * (-(conductance 0 * probe 0)) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 2) * (-(conductance 0 * probe 0) - (-(conductance 2 * probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 3) * (-(conductance 0 * probe 0) - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 4) * (-(conductance 0 * probe 0)) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 5) * (-(conductance 0 * probe 0) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 1 * weight 2) * (-(conductance 2 * probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 1 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 1 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 2 * weight 3) * (-(conductance 2 * probe 2) - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 2 * weight 4) * (-(conductance 2 * probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 2 * weight 5) * (-(conductance 2 * probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1)) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 4 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (-(conductance 0 * probe 0)) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (-(conductance 0 * probe 0)) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (-(conductance 0 * probe 0) - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (-(conductance 0 * probe 0) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 5) * (-(conductance 0 * probe 0)) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1)) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 4 * weight 5) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 1) * (conductance 0 * probe 0 - (conductance 1 * probe 1)) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 2) * (conductance 0 * probe 0) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 3) * (conductance 0 * probe 0) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 4) * (conductance 0 * probe 0 - (conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 5) * (conductance 0 * probe 0 - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 1 * weight 2) * (conductance 1 * probe 1) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 1 * weight 3) * (conductance 1 * probe 1) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 1 * weight 4) * (conductance 1 * probe 1 - (conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 1 * weight 5) * (conductance 1 * probe 1 - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 2 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 2 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 3 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 3 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 4 * weight 5) * (conductance 4 * (probe 0 - probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 0 * weight 1) * (conductance 1 * probe 1) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 0 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 0 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 1 * weight 2) * (conductance 1 * probe 1) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 1 * weight 3) * (conductance 1 * probe 1 - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 1 * weight 5) * (conductance 1 * probe 1 - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 2 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 2 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1)) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 4 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (-(conductance 0 * probe 0)) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (-(conductance 0 * probe 0)) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (-(conductance 0 * probe 0) - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (-(conductance 0 * probe 0) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 5) * (-(conductance 0 * probe 0)) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1)) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 4 * weight 5) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 1) * (conductance 0 * probe 0 - (conductance 1 * probe 1)) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 2) * (conductance 0 * probe 0 - (conductance 2 * probe 2)) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 3) * (conductance 0 * probe 0) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 4) * (conductance 0 * probe 0) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 5) * (conductance 0 * probe 0) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 1 * weight 2) * (conductance 1 * probe 1 - (conductance 2 * probe 2)) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 1 * weight 3) * (conductance 1 * probe 1) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 1 * weight 5) * (conductance 1 * probe 1) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 2 * weight 3) * (conductance 2 * probe 2) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 2 * weight 4) * (conductance 2 * probe 2) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 2 * weight 5) * (conductance 2 * probe 2) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (conductance 0 * probe 0 - (conductance 1 * probe 1)) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (conductance 0 * probe 0 - (conductance 2 * probe 2)) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (conductance 0 * probe 0) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (conductance 0 * probe 0) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 5) * (conductance 0 * probe 0) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 1 * weight 2) * (conductance 1 * probe 1 - (conductance 2 * probe 2)) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (conductance 1 * probe 1) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 1 * weight 5) * (conductance 1 * probe 1) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (conductance 2 * probe 2) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (conductance 2 * probe 2) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 2 * weight 5) * (conductance 2 * probe 2) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (conductance 0 * probe 0 - (conductance 1 * probe 1)) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (conductance 0 * probe 0 - (conductance 2 * probe 2)) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (conductance 0 * probe 0) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (conductance 0 * probe 0) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 5) * (conductance 0 * probe 0) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 1 * weight 2) * (conductance 1 * probe 1 - (conductance 2 * probe 2)) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (conductance 1 * probe 1) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 1 * weight 5) * (conductance 1 * probe 1) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (conductance 2 * probe 2) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (conductance 2 * probe 2) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 2 * weight 5) * (conductance 2 * probe 2) ^ 2 := by
    rw [dotProduct_kFourWeightLaplacian_mulVec]
    simp only [kFourSpanningTreeSum, k4TreeTriples, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, kFourTreeWeightProduct,
      kFourEdgeCompanionSum, Fin.sum_univ_six, k4Drop_zero, k4Drop_one,
      k4Drop_two, k4Drop_three, k4Drop_four, k4Drop_five]
    ring
  have hsos0 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 0 * weight 2) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 1) (hw 1))) (mul_nonneg (hw 0) (hw 2))) (sq_nonneg _)
  have hsos1 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 0 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 1) (hw 1))) (mul_nonneg (hw 0) (hw 4))) (sq_nonneg _)
  have hsos2 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 0 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 1) (hw 1))) (mul_nonneg (hw 0) (hw 5))) (sq_nonneg _)
  have hsos3 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 1 * weight 2) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 1) (hw 1))) (mul_nonneg (hw 1) (hw 2))) (sq_nonneg _)
  have hsos4 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 1 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 1) (hw 1))) (mul_nonneg (hw 1) (hw 4))) (sq_nonneg _)
  have hsos5 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 1 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 1) (hw 1))) (mul_nonneg (hw 1) (hw 5))) (sq_nonneg _)
  have hsos6 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 2 * weight 3) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 1) (hw 1))) (mul_nonneg (hw 2) (hw 3))) (sq_nonneg _)
  have hsos7 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 2 * weight 4) * (conductance 2 * probe 2 - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 1) (hw 1))) (mul_nonneg (hw 2) (hw 4))) (sq_nonneg _)
  have hsos8 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 2 * weight 5) * (conductance 2 * probe 2 - (-(conductance 5 * (probe 1 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 1) (hw 1))) (mul_nonneg (hw 2) (hw 5))) (sq_nonneg _)
  have hsos9 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 3 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 1) (hw 1))) (mul_nonneg (hw 3) (hw 4))) (sq_nonneg _)
  have hsos10 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 3 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 1) (hw 1))) (mul_nonneg (hw 3) (hw 5))) (sq_nonneg _)
  have hsos11 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 4 * weight 5) * (-(conductance 4 * (probe 0 - probe 2)) - (-(conductance 5 * (probe 1 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 1) (hw 1))) (mul_nonneg (hw 4) (hw 5))) (sq_nonneg _)
  have hsos12 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 0 * weight 1) * (-(conductance 1 * probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 0) (hw 1))) (sq_nonneg _)
  have hsos13 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 0 * weight 3) * (conductance 3 * (probe 0 - probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 0) (hw 3))) (sq_nonneg _)
  have hsos14 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 0 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 0) (hw 5))) (sq_nonneg _)
  have hsos15 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 1 * weight 2) * (-(conductance 1 * probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 1) (hw 2))) (sq_nonneg _)
  have hsos16 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 1 * weight 3) * (-(conductance 1 * probe 1) - (conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 1) (hw 3))) (sq_nonneg _)
  have hsos17 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 1 * weight 4) * (-(conductance 1 * probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 1) (hw 4))) (sq_nonneg _)
  have hsos18 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 1 * weight 5) * (-(conductance 1 * probe 1) - (-(conductance 5 * (probe 1 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 1) (hw 5))) (sq_nonneg _)
  have hsos19 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 2 * weight 3) * (conductance 3 * (probe 0 - probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 2) (hw 3))) (sq_nonneg _)
  have hsos20 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 2 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 2) (hw 5))) (sq_nonneg _)
  have hsos21 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 3 * weight 4) * (conductance 3 * (probe 0 - probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 3) (hw 4))) (sq_nonneg _)
  have hsos22 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 3 * weight 5) * (conductance 3 * (probe 0 - probe 1) - (-(conductance 5 * (probe 1 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 3) (hw 5))) (sq_nonneg _)
  have hsos23 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 4 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 4) (hw 5))) (sq_nonneg _)
  have hsos24 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 0 * weight 2) * (-(conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 0) (hw 2))) (sq_nonneg _)
  have hsos25 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 0 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 0) (hw 4))) (sq_nonneg _)
  have hsos26 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 0 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 0) (hw 5))) (sq_nonneg _)
  have hsos27 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 1 * weight 2) * (-(conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 1) (hw 2))) (sq_nonneg _)
  have hsos28 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 1 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 1) (hw 4))) (sq_nonneg _)
  have hsos29 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 1 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 1) (hw 5))) (sq_nonneg _)
  have hsos30 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 2 * weight 3) * (-(conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 2) (hw 3))) (sq_nonneg _)
  have hsos31 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 2 * weight 4) * (-(conductance 2 * probe 2) - (conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 2) (hw 4))) (sq_nonneg _)
  have hsos32 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 2 * weight 5) * (-(conductance 2 * probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 2) (hw 5))) (sq_nonneg _)
  have hsos33 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 3 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 3) (hw 4))) (sq_nonneg _)
  have hsos34 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 3 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 3) (hw 5))) (sq_nonneg _)
  have hsos35 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 4 * weight 5) * (conductance 4 * (probe 0 - probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 4) (hw 5))) (sq_nonneg _)
  have hsos36 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 0 * weight 1) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 0) (hw 1))) (sq_nonneg _)
  have hsos37 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 0 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 0) (hw 3))) (sq_nonneg _)
  have hsos38 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 0 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 0) (hw 5))) (sq_nonneg _)
  have hsos39 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 1 * weight 2) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 1) (hw 2))) (sq_nonneg _)
  have hsos40 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 1 * weight 3) * (conductance 1 * probe 1 - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 1) (hw 3))) (sq_nonneg _)
  have hsos41 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 1) (hw 4))) (sq_nonneg _)
  have hsos42 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 1 * weight 5) * (conductance 1 * probe 1 - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 1) (hw 5))) (sq_nonneg _)
  have hsos43 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 2 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 2) (hw 3))) (sq_nonneg _)
  have hsos44 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 2 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 2) (hw 5))) (sq_nonneg _)
  have hsos45 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 3) (hw 4))) (sq_nonneg _)
  have hsos46 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1)) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 3) (hw 5))) (sq_nonneg _)
  have hsos47 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 4 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 4) (hw 5))) (sq_nonneg _)
  have hsos48 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 1))) (sq_nonneg _)
  have hsos49 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 2))) (sq_nonneg _)
  have hsos50 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 3))) (sq_nonneg _)
  have hsos51 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 4))) (sq_nonneg _)
  have hsos52 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 1 * weight 2) * (conductance 1 * probe 1 - (conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 1) (hw 2))) (sq_nonneg _)
  have hsos53 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (conductance 1 * probe 1 - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 1) (hw 3))) (sq_nonneg _)
  have hsos54 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (conductance 1 * probe 1 - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 1) (hw 4))) (sq_nonneg _)
  have hsos55 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 1 * weight 5) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 1) (hw 5))) (sq_nonneg _)
  have hsos56 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (conductance 2 * probe 2 - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 2) (hw 3))) (sq_nonneg _)
  have hsos57 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (conductance 2 * probe 2 - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 2) (hw 4))) (sq_nonneg _)
  have hsos58 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 2 * weight 5) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 2) (hw 5))) (sq_nonneg _)
  have hsos59 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1)) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 3) (hw 4))) (sq_nonneg _)
  have hsos60 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 3) (hw 5))) (sq_nonneg _)
  have hsos61 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 4 * weight 5) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 0) (hw 0)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 4) (hw 5))) (sq_nonneg _)
  have hsos62 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 1) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 0) (hw 1))) (sq_nonneg _)
  have hsos63 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 2) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 0) (hw 2))) (sq_nonneg _)
  have hsos64 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 3) * (conductance 0 * probe 0 - (conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 0) (hw 3))) (sq_nonneg _)
  have hsos65 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 4) * (conductance 0 * probe 0 - (conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 0) (hw 4))) (sq_nonneg _)
  have hsos66 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 5) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 0) (hw 5))) (sq_nonneg _)
  have hsos67 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 1 * weight 3) * (conductance 3 * (probe 0 - probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 1) (hw 3))) (sq_nonneg _)
  have hsos68 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 1 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 1) (hw 4))) (sq_nonneg _)
  have hsos69 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 2 * weight 3) * (conductance 3 * (probe 0 - probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 2) (hw 3))) (sq_nonneg _)
  have hsos70 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 2 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 2) (hw 4))) (sq_nonneg _)
  have hsos71 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 3 * weight 4) * (conductance 3 * (probe 0 - probe 1) - (conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 3) (hw 4))) (sq_nonneg _)
  have hsos72 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 3 * weight 5) * (conductance 3 * (probe 0 - probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 3) (hw 5))) (sq_nonneg _)
  have hsos73 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 4 * weight 5) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 2) (hw 2))) (mul_nonneg (hw 4) (hw 5))) (sq_nonneg _)
  have hsos74 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 0 * weight 2) * (-(conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 0) (hw 2))) (sq_nonneg _)
  have hsos75 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 0 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 0) (hw 4))) (sq_nonneg _)
  have hsos76 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 0 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 0) (hw 5))) (sq_nonneg _)
  have hsos77 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 1 * weight 2) * (-(conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 1) (hw 2))) (sq_nonneg _)
  have hsos78 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 1 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 1) (hw 4))) (sq_nonneg _)
  have hsos79 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 1 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 1) (hw 5))) (sq_nonneg _)
  have hsos80 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 2 * weight 3) * (-(conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 2) (hw 3))) (sq_nonneg _)
  have hsos81 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 2 * weight 4) * (-(conductance 2 * probe 2) - (conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 2) (hw 4))) (sq_nonneg _)
  have hsos82 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 2 * weight 5) * (-(conductance 2 * probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 2) (hw 5))) (sq_nonneg _)
  have hsos83 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 3 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 3) (hw 4))) (sq_nonneg _)
  have hsos84 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 3 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 3) (hw 5))) (sq_nonneg _)
  have hsos85 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 4 * weight 5) * (conductance 4 * (probe 0 - probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 4) (hw 5))) (sq_nonneg _)
  have hsos86 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 1) * (-(conductance 0 * probe 0)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 0) (hw 1))) (sq_nonneg _)
  have hsos87 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 2) * (-(conductance 0 * probe 0) - (-(conductance 2 * probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 0) (hw 2))) (sq_nonneg _)
  have hsos88 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 3) * (-(conductance 0 * probe 0) - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 0) (hw 3))) (sq_nonneg _)
  have hsos89 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 4) * (-(conductance 0 * probe 0)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 0) (hw 4))) (sq_nonneg _)
  have hsos90 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 5) * (-(conductance 0 * probe 0) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 0) (hw 5))) (sq_nonneg _)
  have hsos91 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 1 * weight 2) * (-(conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 1) (hw 2))) (sq_nonneg _)
  have hsos92 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 1 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 1) (hw 3))) (sq_nonneg _)
  have hsos93 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 1 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 1) (hw 5))) (sq_nonneg _)
  have hsos94 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 2 * weight 3) * (-(conductance 2 * probe 2) - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 2) (hw 3))) (sq_nonneg _)
  have hsos95 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 2 * weight 4) * (-(conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 2) (hw 4))) (sq_nonneg _)
  have hsos96 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 2 * weight 5) * (-(conductance 2 * probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 2) (hw 5))) (sq_nonneg _)
  have hsos97 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 3) (hw 4))) (sq_nonneg _)
  have hsos98 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1)) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 3) (hw 5))) (sq_nonneg _)
  have hsos99 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 4 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 4) (hw 5))) (sq_nonneg _)
  have hsos100 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (-(conductance 0 * probe 0)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 1))) (sq_nonneg _)
  have hsos101 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (-(conductance 0 * probe 0)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 2))) (sq_nonneg _)
  have hsos102 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (-(conductance 0 * probe 0) - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 3))) (sq_nonneg _)
  have hsos103 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (-(conductance 0 * probe 0) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 4))) (sq_nonneg _)
  have hsos104 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 5) * (-(conductance 0 * probe 0)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 5))) (sq_nonneg _)
  have hsos105 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 1) (hw 3))) (sq_nonneg _)
  have hsos106 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 1) (hw 4))) (sq_nonneg _)
  have hsos107 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 2) (hw 3))) (sq_nonneg _)
  have hsos108 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 2) (hw 4))) (sq_nonneg _)
  have hsos109 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1)) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 3) (hw 4))) (sq_nonneg _)
  have hsos110 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 3) (hw 5))) (sq_nonneg _)
  have hsos111 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 4 * weight 5) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 1) (hw 1)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 4) (hw 5))) (sq_nonneg _)
  have hsos112 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 1) * (conductance 0 * probe 0 - (conductance 1 * probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 0) (hw 1))) (sq_nonneg _)
  have hsos113 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 2) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 0) (hw 2))) (sq_nonneg _)
  have hsos114 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 3) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 0) (hw 3))) (sq_nonneg _)
  have hsos115 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 4) * (conductance 0 * probe 0 - (conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 0) (hw 4))) (sq_nonneg _)
  have hsos116 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 5) * (conductance 0 * probe 0 - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 0) (hw 5))) (sq_nonneg _)
  have hsos117 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 1 * weight 2) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 1) (hw 2))) (sq_nonneg _)
  have hsos118 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 1 * weight 3) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 1) (hw 3))) (sq_nonneg _)
  have hsos119 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 1 * weight 4) * (conductance 1 * probe 1 - (conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 1) (hw 4))) (sq_nonneg _)
  have hsos120 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 1 * weight 5) * (conductance 1 * probe 1 - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 1) (hw 5))) (sq_nonneg _)
  have hsos121 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 2 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 2) (hw 4))) (sq_nonneg _)
  have hsos122 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 2 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 2) (hw 5))) (sq_nonneg _)
  have hsos123 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 3 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 3) (hw 4))) (sq_nonneg _)
  have hsos124 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 3 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 3) (hw 5))) (sq_nonneg _)
  have hsos125 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 4 * weight 5) * (conductance 4 * (probe 0 - probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 3) (hw 3))) (mul_nonneg (hw 4) (hw 5))) (sq_nonneg _)
  have hsos126 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 0 * weight 1) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 0) (hw 1))) (sq_nonneg _)
  have hsos127 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 0 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 0) (hw 3))) (sq_nonneg _)
  have hsos128 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 0 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 0) (hw 5))) (sq_nonneg _)
  have hsos129 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 1 * weight 2) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 1) (hw 2))) (sq_nonneg _)
  have hsos130 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 1 * weight 3) * (conductance 1 * probe 1 - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 1) (hw 3))) (sq_nonneg _)
  have hsos131 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 1) (hw 4))) (sq_nonneg _)
  have hsos132 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 1 * weight 5) * (conductance 1 * probe 1 - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 1) (hw 5))) (sq_nonneg _)
  have hsos133 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 2 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 2) (hw 3))) (sq_nonneg _)
  have hsos134 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 2 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 2) (hw 5))) (sq_nonneg _)
  have hsos135 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 3) (hw 4))) (sq_nonneg _)
  have hsos136 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1)) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 3) (hw 5))) (sq_nonneg _)
  have hsos137 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 4 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 4) (hw 5))) (sq_nonneg _)
  have hsos138 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (-(conductance 0 * probe 0)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 1))) (sq_nonneg _)
  have hsos139 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (-(conductance 0 * probe 0)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 2))) (sq_nonneg _)
  have hsos140 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (-(conductance 0 * probe 0) - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 3))) (sq_nonneg _)
  have hsos141 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (-(conductance 0 * probe 0) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 4))) (sq_nonneg _)
  have hsos142 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 5) * (-(conductance 0 * probe 0)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 5))) (sq_nonneg _)
  have hsos143 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 1) (hw 3))) (sq_nonneg _)
  have hsos144 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 1) (hw 4))) (sq_nonneg _)
  have hsos145 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 2) (hw 3))) (sq_nonneg _)
  have hsos146 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 2) (hw 4))) (sq_nonneg _)
  have hsos147 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1)) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 3) (hw 4))) (sq_nonneg _)
  have hsos148 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 3) (hw 5))) (sq_nonneg _)
  have hsos149 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 4 * weight 5) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 2) (hw 2)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 4) (hw 5))) (sq_nonneg _)
  have hsos150 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 1) * (conductance 0 * probe 0 - (conductance 1 * probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 0) (hw 1))) (sq_nonneg _)
  have hsos151 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 2) * (conductance 0 * probe 0 - (conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 0) (hw 2))) (sq_nonneg _)
  have hsos152 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 3) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 0) (hw 3))) (sq_nonneg _)
  have hsos153 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 4) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 0) (hw 4))) (sq_nonneg _)
  have hsos154 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 5) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 0) (hw 5))) (sq_nonneg _)
  have hsos155 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 1 * weight 2) * (conductance 1 * probe 1 - (conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 1) (hw 2))) (sq_nonneg _)
  have hsos156 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 1 * weight 3) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 1) (hw 3))) (sq_nonneg _)
  have hsos157 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 1) (hw 4))) (sq_nonneg _)
  have hsos158 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 1 * weight 5) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 1) (hw 5))) (sq_nonneg _)
  have hsos159 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 2 * weight 3) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 2) (hw 3))) (sq_nonneg _)
  have hsos160 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 2 * weight 4) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 2) (hw 4))) (sq_nonneg _)
  have hsos161 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 2 * weight 5) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 4) (hw 4))) (mul_nonneg (hw 2) (hw 5))) (sq_nonneg _)
  have hsos162 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (conductance 0 * probe 0 - (conductance 1 * probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 1))) (sq_nonneg _)
  have hsos163 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (conductance 0 * probe 0 - (conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 2))) (sq_nonneg _)
  have hsos164 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 3))) (sq_nonneg _)
  have hsos165 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 4))) (sq_nonneg _)
  have hsos166 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 5) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 5))) (sq_nonneg _)
  have hsos167 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 1 * weight 2) * (conductance 1 * probe 1 - (conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 1) (hw 2))) (sq_nonneg _)
  have hsos168 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 1) (hw 3))) (sq_nonneg _)
  have hsos169 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 1) (hw 4))) (sq_nonneg _)
  have hsos170 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 1 * weight 5) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 1) (hw 5))) (sq_nonneg _)
  have hsos171 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 2) (hw 3))) (sq_nonneg _)
  have hsos172 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 2) (hw 4))) (sq_nonneg _)
  have hsos173 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 2 * weight 5) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 3) (hw 3)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 2) (hw 5))) (sq_nonneg _)
  have hsos174 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (conductance 0 * probe 0 - (conductance 1 * probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 4) (hw 4)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 1))) (sq_nonneg _)
  have hsos175 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (conductance 0 * probe 0 - (conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 4) (hw 4)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 2))) (sq_nonneg _)
  have hsos176 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 4) (hw 4)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 3))) (sq_nonneg _)
  have hsos177 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 4) (hw 4)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 4))) (sq_nonneg _)
  have hsos178 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 5) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 4) (hw 4)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 0) (hw 5))) (sq_nonneg _)
  have hsos179 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 1 * weight 2) * (conductance 1 * probe 1 - (conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 4) (hw 4)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 1) (hw 2))) (sq_nonneg _)
  have hsos180 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 4) (hw 4)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 1) (hw 3))) (sq_nonneg _)
  have hsos181 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 4) (hw 4)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 1) (hw 4))) (sq_nonneg _)
  have hsos182 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 1 * weight 5) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 4) (hw 4)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 1) (hw 5))) (sq_nonneg _)
  have hsos183 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 4) (hw 4)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 2) (hw 3))) (sq_nonneg _)
  have hsos184 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 4) (hw 4)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 2) (hw 4))) (sq_nonneg _)
  have hsos185 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 2 * weight 5) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hcond 4) (hw 4)) (mul_nonneg (hcond 5) (hw 5))) (mul_nonneg (hw 2) (hw 5))) (sq_nonneg _)
  rw [hsix, mul_one] at hkey
  linarith

/-- **P1, THE MIXTURE LAW (semidefinite form, rung 11).**  The
matrix-tree mixture of the sixteen tree forms dominates the frame:
`x^T (sum_T (prod_T m) S_T) x >= det B * (x^T B x)`; dividing by
`det B > 0` gives `sum_T P_T S_T >= B` at the matrix-tree probabilities
`P_T = prod_T m / det B`. -/
theorem kFour_mixtureLaw (conductance weight : Fin 6 → ℝ) (probe : Fin 3 → ℝ)
    (hcond : ∀ edge, 0 ≤ conductance edge) (hw : ∀ edge, 0 ≤ weight edge)
    (hsum : ∑ edge, weight edge = 1) :
    kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
        * (probe ⬝ᵥ (kFourWeightLaplacian
            (fun edge => conductance edge * weight edge)).mulVec probe)
      ≤ (k4TreeTriples.map fun tree =>
          kFourTreeWeightProduct (fun edge => conductance edge * weight edge)
              tree
            * (conductance tree.1 * k4Drop probe tree.1 ^ 2
              + conductance tree.2.1 * k4Drop probe tree.2.1 ^ 2
              + conductance tree.2.2 * k4Drop probe tree.2.2 ^ 2)).sum := by
  rw [kFour_mixture_treeForm_expansion]
  exact kFour_mixtureLaw_leverageForm conductance weight probe hcond hw hsum

/-- **P1, STRICT FORM (rung 11).**  On the open simplex with strictly
positive conductances, the matrix-tree mixture strictly dominates the
frame at every nonzero probe:
`det B * (x^T B x) < sum_c y_c m_c F_c(m) (drop_c x)^2` for `x /= 0`.
Dividing by `det B > 0`: `sum_T P_T S_T > B` -- the ledger's P1.  The
witness square is chosen per nonvanishing probe coordinate from the
Lagrange decomposition; positivity of the remaining summands is the
semidefinite bookkeeping. -/
theorem kFour_mixtureLaw_leverageForm_strict (conductance weight : Fin 6 → ℝ)
    (probe : Fin 3 → ℝ)
    (hcond : ∀ edge, 0 < conductance edge) (hw : ∀ edge, 0 < weight edge)
    (hsum : ∑ edge, weight edge = 1) (hprobe : probe ≠ 0) :
    kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
        * (probe ⬝ᵥ (kFourWeightLaplacian
            (fun edge => conductance edge * weight edge)).mulVec probe)
      < ∑ edge, conductance edge * (conductance edge * weight edge)
          * kFourEdgeCompanionSum (fun other => conductance other * weight other)
              edge
          * k4Drop probe edge ^ 2 := by
  have hsix : weight 0 + weight 1 + weight 2 + weight 3 + weight 4
      + weight 5 = 1 := by
    simpa [Fin.sum_univ_six] using hsum
  have hkey : (∑ edge, conductance edge * (conductance edge * weight edge)
          * kFourEdgeCompanionSum (fun other => conductance other * weight other)
              edge
          * k4Drop probe edge ^ 2)
        * (weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5)
      - kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
          * (probe ⬝ᵥ (kFourWeightLaplacian
              (fun edge => conductance edge * weight edge)).mulVec probe)
      = conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 0 * weight 2) * (conductance 2 * probe 2) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 0 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 0 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 1 * weight 2) * (conductance 2 * probe 2) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 1 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 1 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 2 * weight 3) * (conductance 2 * probe 2) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 2 * weight 4) * (conductance 2 * probe 2 - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 2 * weight 5) * (conductance 2 * probe 2 - (-(conductance 5 * (probe 1 - probe 2)))) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 3 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 3 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 4 * weight 5) * (-(conductance 4 * (probe 0 - probe 2)) - (-(conductance 5 * (probe 1 - probe 2)))) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 0 * weight 1) * (-(conductance 1 * probe 1)) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 0 * weight 3) * (conductance 3 * (probe 0 - probe 1)) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 0 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 1 * weight 2) * (-(conductance 1 * probe 1)) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 1 * weight 3) * (-(conductance 1 * probe 1) - (conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 1 * weight 4) * (-(conductance 1 * probe 1)) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 1 * weight 5) * (-(conductance 1 * probe 1) - (-(conductance 5 * (probe 1 - probe 2)))) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 2 * weight 3) * (conductance 3 * (probe 0 - probe 1)) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 2 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 3 * weight 4) * (conductance 3 * (probe 0 - probe 1)) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 3 * weight 5) * (conductance 3 * (probe 0 - probe 1) - (-(conductance 5 * (probe 1 - probe 2)))) ^ 2
        + conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 4 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 0 * weight 2) * (-(conductance 2 * probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 0 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 0 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 1 * weight 2) * (-(conductance 2 * probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 1 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 1 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 2 * weight 3) * (-(conductance 2 * probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 2 * weight 4) * (-(conductance 2 * probe 2) - (conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 2 * weight 5) * (-(conductance 2 * probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 3 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 3 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 4 * weight 5) * (conductance 4 * (probe 0 - probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 0 * weight 1) * (conductance 1 * probe 1) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 0 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 0 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 1 * weight 2) * (conductance 1 * probe 1) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 1 * weight 3) * (conductance 1 * probe 1 - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 1 * weight 5) * (conductance 1 * probe 1 - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 2 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 2 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1)) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 4 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (conductance 1 * probe 1) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (conductance 2 * probe 2) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 1 * weight 2) * (conductance 1 * probe 1 - (conductance 2 * probe 2)) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (conductance 1 * probe 1 - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (conductance 1 * probe 1 - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 1 * weight 5) * (conductance 1 * probe 1) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (conductance 2 * probe 2 - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (conductance 2 * probe 2 - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 2 * weight 5) * (conductance 2 * probe 2) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1)) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 4 * weight 5) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 1) * (conductance 0 * probe 0) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 2) * (conductance 0 * probe 0) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 3) * (conductance 0 * probe 0 - (conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 4) * (conductance 0 * probe 0 - (conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 5) * (conductance 0 * probe 0) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 1 * weight 3) * (conductance 3 * (probe 0 - probe 1)) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 1 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 2 * weight 3) * (conductance 3 * (probe 0 - probe 1)) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 2 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 3 * weight 4) * (conductance 3 * (probe 0 - probe 1) - (conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 3 * weight 5) * (conductance 3 * (probe 0 - probe 1)) ^ 2
        + conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 4 * weight 5) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 0 * weight 2) * (-(conductance 2 * probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 0 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 0 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 1 * weight 2) * (-(conductance 2 * probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 1 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 1 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 2 * weight 3) * (-(conductance 2 * probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 2 * weight 4) * (-(conductance 2 * probe 2) - (conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 2 * weight 5) * (-(conductance 2 * probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 3 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 3 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 4 * weight 5) * (conductance 4 * (probe 0 - probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 1) * (-(conductance 0 * probe 0)) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 2) * (-(conductance 0 * probe 0) - (-(conductance 2 * probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 3) * (-(conductance 0 * probe 0) - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 4) * (-(conductance 0 * probe 0)) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 5) * (-(conductance 0 * probe 0) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 1 * weight 2) * (-(conductance 2 * probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 1 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 1 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 2 * weight 3) * (-(conductance 2 * probe 2) - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 2 * weight 4) * (-(conductance 2 * probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 2 * weight 5) * (-(conductance 2 * probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1)) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 4 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (-(conductance 0 * probe 0)) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (-(conductance 0 * probe 0)) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (-(conductance 0 * probe 0) - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (-(conductance 0 * probe 0) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 5) * (-(conductance 0 * probe 0)) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1)) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 4 * weight 5) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 1) * (conductance 0 * probe 0 - (conductance 1 * probe 1)) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 2) * (conductance 0 * probe 0) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 3) * (conductance 0 * probe 0) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 4) * (conductance 0 * probe 0 - (conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 5) * (conductance 0 * probe 0 - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 1 * weight 2) * (conductance 1 * probe 1) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 1 * weight 3) * (conductance 1 * probe 1) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 1 * weight 4) * (conductance 1 * probe 1 - (conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 1 * weight 5) * (conductance 1 * probe 1 - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 2 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 2 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 3 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 3 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 4 * weight 5) * (conductance 4 * (probe 0 - probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 0 * weight 1) * (conductance 1 * probe 1) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 0 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 0 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 1 * weight 2) * (conductance 1 * probe 1) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 1 * weight 3) * (conductance 1 * probe 1 - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 1 * weight 5) * (conductance 1 * probe 1 - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 2 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 2 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1)) - (conductance 5 * (probe 1 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 4 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (-(conductance 0 * probe 0)) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (-(conductance 0 * probe 0)) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (-(conductance 0 * probe 0) - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (-(conductance 0 * probe 0) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 5) * (-(conductance 0 * probe 0)) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1)) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2
        + conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 4 * weight 5) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 1) * (conductance 0 * probe 0 - (conductance 1 * probe 1)) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 2) * (conductance 0 * probe 0 - (conductance 2 * probe 2)) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 3) * (conductance 0 * probe 0) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 4) * (conductance 0 * probe 0) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 5) * (conductance 0 * probe 0) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 1 * weight 2) * (conductance 1 * probe 1 - (conductance 2 * probe 2)) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 1 * weight 3) * (conductance 1 * probe 1) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 1 * weight 5) * (conductance 1 * probe 1) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 2 * weight 3) * (conductance 2 * probe 2) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 2 * weight 4) * (conductance 2 * probe 2) ^ 2
        + conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 2 * weight 5) * (conductance 2 * probe 2) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (conductance 0 * probe 0 - (conductance 1 * probe 1)) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (conductance 0 * probe 0 - (conductance 2 * probe 2)) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (conductance 0 * probe 0) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (conductance 0 * probe 0) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 5) * (conductance 0 * probe 0) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 1 * weight 2) * (conductance 1 * probe 1 - (conductance 2 * probe 2)) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (conductance 1 * probe 1) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 1 * weight 5) * (conductance 1 * probe 1) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (conductance 2 * probe 2) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (conductance 2 * probe 2) ^ 2
        + conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 2 * weight 5) * (conductance 2 * probe 2) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (conductance 0 * probe 0 - (conductance 1 * probe 1)) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (conductance 0 * probe 0 - (conductance 2 * probe 2)) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (conductance 0 * probe 0) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (conductance 0 * probe 0) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 5) * (conductance 0 * probe 0) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 1 * weight 2) * (conductance 1 * probe 1 - (conductance 2 * probe 2)) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (conductance 1 * probe 1) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 1 * weight 5) * (conductance 1 * probe 1) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (conductance 2 * probe 2) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (conductance 2 * probe 2) ^ 2
        + conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 2 * weight 5) * (conductance 2 * probe 2) ^ 2 := by
    rw [dotProduct_kFourWeightLaplacian_mulVec]
    simp only [kFourSpanningTreeSum, k4TreeTriples, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, kFourTreeWeightProduct,
      kFourEdgeCompanionSum, Fin.sum_univ_six, k4Drop_zero, k4Drop_one,
      k4Drop_two, k4Drop_three, k4Drop_four, k4Drop_five]
    ring
  have hsos0 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 0 * weight 2) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 1).le) ((hw 1).le))) (mul_nonneg ((hw 0).le) ((hw 2).le))) (sq_nonneg _)
  have hsos1 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 0 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 1).le) ((hw 1).le))) (mul_nonneg ((hw 0).le) ((hw 4).le))) (sq_nonneg _)
  have hsos2 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 0 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 1).le) ((hw 1).le))) (mul_nonneg ((hw 0).le) ((hw 5).le))) (sq_nonneg _)
  have hsos3 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 1 * weight 2) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 1).le) ((hw 1).le))) (mul_nonneg ((hw 1).le) ((hw 2).le))) (sq_nonneg _)
  have hsos4 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 1 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 1).le) ((hw 1).le))) (mul_nonneg ((hw 1).le) ((hw 4).le))) (sq_nonneg _)
  have hsos5 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 1 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 1).le) ((hw 1).le))) (mul_nonneg ((hw 1).le) ((hw 5).le))) (sq_nonneg _)
  have hsos6 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 2 * weight 3) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 1).le) ((hw 1).le))) (mul_nonneg ((hw 2).le) ((hw 3).le))) (sq_nonneg _)
  have hsos7 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 2 * weight 4) * (conductance 2 * probe 2 - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 1).le) ((hw 1).le))) (mul_nonneg ((hw 2).le) ((hw 4).le))) (sq_nonneg _)
  have hsos8 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 2 * weight 5) * (conductance 2 * probe 2 - (-(conductance 5 * (probe 1 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 1).le) ((hw 1).le))) (mul_nonneg ((hw 2).le) ((hw 5).le))) (sq_nonneg _)
  have hsos9 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 3 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 1).le) ((hw 1).le))) (mul_nonneg ((hw 3).le) ((hw 4).le))) (sq_nonneg _)
  have hsos10 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 3 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 1).le) ((hw 1).le))) (mul_nonneg ((hw 3).le) ((hw 5).le))) (sq_nonneg _)
  have hsos11 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 1 * weight 1) * (weight 4 * weight 5) * (-(conductance 4 * (probe 0 - probe 2)) - (-(conductance 5 * (probe 1 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 1).le) ((hw 1).le))) (mul_nonneg ((hw 4).le) ((hw 5).le))) (sq_nonneg _)
  have hsos12 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 0 * weight 1) * (-(conductance 1 * probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 0).le) ((hw 1).le))) (sq_nonneg _)
  have hsos13 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 0 * weight 3) * (conductance 3 * (probe 0 - probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 0).le) ((hw 3).le))) (sq_nonneg _)
  have hsos14 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 0 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 0).le) ((hw 5).le))) (sq_nonneg _)
  have hsos15 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 1 * weight 2) * (-(conductance 1 * probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 1).le) ((hw 2).le))) (sq_nonneg _)
  have hsos16 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 1 * weight 3) * (-(conductance 1 * probe 1) - (conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 1).le) ((hw 3).le))) (sq_nonneg _)
  have hsos17 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 1 * weight 4) * (-(conductance 1 * probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 1).le) ((hw 4).le))) (sq_nonneg _)
  have hsos18 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 1 * weight 5) * (-(conductance 1 * probe 1) - (-(conductance 5 * (probe 1 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 1).le) ((hw 5).le))) (sq_nonneg _)
  have hsos19 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 2 * weight 3) * (conductance 3 * (probe 0 - probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 2).le) ((hw 3).le))) (sq_nonneg _)
  have hsos20 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 2 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 2).le) ((hw 5).le))) (sq_nonneg _)
  have hsos21 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 3 * weight 4) * (conductance 3 * (probe 0 - probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 3).le) ((hw 4).le))) (sq_nonneg _)
  have hsos22 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 3 * weight 5) * (conductance 3 * (probe 0 - probe 1) - (-(conductance 5 * (probe 1 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 3).le) ((hw 5).le))) (sq_nonneg _)
  have hsos23 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 2 * weight 2) * (weight 4 * weight 5) * (-(conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 4).le) ((hw 5).le))) (sq_nonneg _)
  have hsos24 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 0 * weight 2) * (-(conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 0).le) ((hw 2).le))) (sq_nonneg _)
  have hsos25 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 0 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 0).le) ((hw 4).le))) (sq_nonneg _)
  have hsos26 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 0 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 0).le) ((hw 5).le))) (sq_nonneg _)
  have hsos27 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 1 * weight 2) * (-(conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 1).le) ((hw 2).le))) (sq_nonneg _)
  have hsos28 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 1 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 1).le) ((hw 4).le))) (sq_nonneg _)
  have hsos29 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 1 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 1).le) ((hw 5).le))) (sq_nonneg _)
  have hsos30 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 2 * weight 3) * (-(conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 2).le) ((hw 3).le))) (sq_nonneg _)
  have hsos31 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 2 * weight 4) * (-(conductance 2 * probe 2) - (conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 2).le) ((hw 4).le))) (sq_nonneg _)
  have hsos32 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 2 * weight 5) * (-(conductance 2 * probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 2).le) ((hw 5).le))) (sq_nonneg _)
  have hsos33 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 3 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 3).le) ((hw 4).le))) (sq_nonneg _)
  have hsos34 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 3 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 3).le) ((hw 5).le))) (sq_nonneg _)
  have hsos35 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 3 * weight 3) * (weight 4 * weight 5) * (conductance 4 * (probe 0 - probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 4).le) ((hw 5).le))) (sq_nonneg _)
  have hsos36 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 0 * weight 1) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 0).le) ((hw 1).le))) (sq_nonneg _)
  have hsos37 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 0 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 0).le) ((hw 3).le))) (sq_nonneg _)
  have hsos38 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 0 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 0).le) ((hw 5).le))) (sq_nonneg _)
  have hsos39 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 1 * weight 2) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 1).le) ((hw 2).le))) (sq_nonneg _)
  have hsos40 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 1 * weight 3) * (conductance 1 * probe 1 - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 1).le) ((hw 3).le))) (sq_nonneg _)
  have hsos41 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 1).le) ((hw 4).le))) (sq_nonneg _)
  have hsos42 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 1 * weight 5) * (conductance 1 * probe 1 - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 1).le) ((hw 5).le))) (sq_nonneg _)
  have hsos43 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 2 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 2).le) ((hw 3).le))) (sq_nonneg _)
  have hsos44 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 2 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 2).le) ((hw 5).le))) (sq_nonneg _)
  have hsos45 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 3).le) ((hw 4).le))) (sq_nonneg _)
  have hsos46 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1)) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 3).le) ((hw 5).le))) (sq_nonneg _)
  have hsos47 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 4 * weight 4) * (weight 4 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 4).le) ((hw 5).le))) (sq_nonneg _)
  have hsos48 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 1).le))) (sq_nonneg _)
  have hsos49 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 2).le))) (sq_nonneg _)
  have hsos50 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 3).le))) (sq_nonneg _)
  have hsos51 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 4).le))) (sq_nonneg _)
  have hsos52 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 1 * weight 2) * (conductance 1 * probe 1 - (conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 1).le) ((hw 2).le))) (sq_nonneg _)
  have hsos53 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (conductance 1 * probe 1 - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 1).le) ((hw 3).le))) (sq_nonneg _)
  have hsos54 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (conductance 1 * probe 1 - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 1).le) ((hw 4).le))) (sq_nonneg _)
  have hsos55 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 1 * weight 5) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 1).le) ((hw 5).le))) (sq_nonneg _)
  have hsos56 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (conductance 2 * probe 2 - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 2).le) ((hw 3).le))) (sq_nonneg _)
  have hsos57 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (conductance 2 * probe 2 - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 2).le) ((hw 4).le))) (sq_nonneg _)
  have hsos58 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 2 * weight 5) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 2).le) ((hw 5).le))) (sq_nonneg _)
  have hsos59 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1)) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 3).le) ((hw 4).le))) (sq_nonneg _)
  have hsos60 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 3).le) ((hw 5).le))) (sq_nonneg _)
  have hsos61 : (0 : ℝ) ≤ conductance 0 * weight 0 * (conductance 5 * weight 5) * (weight 4 * weight 5) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 0).le) ((hw 0).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 4).le) ((hw 5).le))) (sq_nonneg _)
  have hsos62 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 1) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 0).le) ((hw 1).le))) (sq_nonneg _)
  have hsos63 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 2) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 0).le) ((hw 2).le))) (sq_nonneg _)
  have hsos64 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 3) * (conductance 0 * probe 0 - (conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 0).le) ((hw 3).le))) (sq_nonneg _)
  have hsos65 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 4) * (conductance 0 * probe 0 - (conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 0).le) ((hw 4).le))) (sq_nonneg _)
  have hsos66 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 0 * weight 5) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 0).le) ((hw 5).le))) (sq_nonneg _)
  have hsos67 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 1 * weight 3) * (conductance 3 * (probe 0 - probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 1).le) ((hw 3).le))) (sq_nonneg _)
  have hsos68 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 1 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 1).le) ((hw 4).le))) (sq_nonneg _)
  have hsos69 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 2 * weight 3) * (conductance 3 * (probe 0 - probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 2).le) ((hw 3).le))) (sq_nonneg _)
  have hsos70 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 2 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 2).le) ((hw 4).le))) (sq_nonneg _)
  have hsos71 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 3 * weight 4) * (conductance 3 * (probe 0 - probe 1) - (conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 3).le) ((hw 4).le))) (sq_nonneg _)
  have hsos72 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 3 * weight 5) * (conductance 3 * (probe 0 - probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 3).le) ((hw 5).le))) (sq_nonneg _)
  have hsos73 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 2 * weight 2) * (weight 4 * weight 5) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 2).le) ((hw 2).le))) (mul_nonneg ((hw 4).le) ((hw 5).le))) (sq_nonneg _)
  have hsos74 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 0 * weight 2) * (-(conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 0).le) ((hw 2).le))) (sq_nonneg _)
  have hsos75 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 0 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 0).le) ((hw 4).le))) (sq_nonneg _)
  have hsos76 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 0 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 0).le) ((hw 5).le))) (sq_nonneg _)
  have hsos77 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 1 * weight 2) * (-(conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 1).le) ((hw 2).le))) (sq_nonneg _)
  have hsos78 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 1 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 1).le) ((hw 4).le))) (sq_nonneg _)
  have hsos79 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 1 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 1).le) ((hw 5).le))) (sq_nonneg _)
  have hsos80 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 2 * weight 3) * (-(conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 2).le) ((hw 3).le))) (sq_nonneg _)
  have hsos81 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 2 * weight 4) * (-(conductance 2 * probe 2) - (conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 2).le) ((hw 4).le))) (sq_nonneg _)
  have hsos82 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 2 * weight 5) * (-(conductance 2 * probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 2).le) ((hw 5).le))) (sq_nonneg _)
  have hsos83 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 3 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 3).le) ((hw 4).le))) (sq_nonneg _)
  have hsos84 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 3 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 3).le) ((hw 5).le))) (sq_nonneg _)
  have hsos85 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 3 * weight 3) * (weight 4 * weight 5) * (conductance 4 * (probe 0 - probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 4).le) ((hw 5).le))) (sq_nonneg _)
  have hsos86 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 1) * (-(conductance 0 * probe 0)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 0).le) ((hw 1).le))) (sq_nonneg _)
  have hsos87 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 2) * (-(conductance 0 * probe 0) - (-(conductance 2 * probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 0).le) ((hw 2).le))) (sq_nonneg _)
  have hsos88 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 3) * (-(conductance 0 * probe 0) - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 0).le) ((hw 3).le))) (sq_nonneg _)
  have hsos89 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 4) * (-(conductance 0 * probe 0)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 0).le) ((hw 4).le))) (sq_nonneg _)
  have hsos90 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 0 * weight 5) * (-(conductance 0 * probe 0) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 0).le) ((hw 5).le))) (sq_nonneg _)
  have hsos91 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 1 * weight 2) * (-(conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 1).le) ((hw 2).le))) (sq_nonneg _)
  have hsos92 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 1 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 1).le) ((hw 3).le))) (sq_nonneg _)
  have hsos93 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 1 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 1).le) ((hw 5).le))) (sq_nonneg _)
  have hsos94 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 2 * weight 3) * (-(conductance 2 * probe 2) - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 2).le) ((hw 3).le))) (sq_nonneg _)
  have hsos95 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 2 * weight 4) * (-(conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 2).le) ((hw 4).le))) (sq_nonneg _)
  have hsos96 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 2 * weight 5) * (-(conductance 2 * probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 2).le) ((hw 5).le))) (sq_nonneg _)
  have hsos97 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 3).le) ((hw 4).le))) (sq_nonneg _)
  have hsos98 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1)) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 3).le) ((hw 5).le))) (sq_nonneg _)
  have hsos99 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 4 * weight 4) * (weight 4 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 4).le) ((hw 5).le))) (sq_nonneg _)
  have hsos100 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (-(conductance 0 * probe 0)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 1).le))) (sq_nonneg _)
  have hsos101 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (-(conductance 0 * probe 0)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 2).le))) (sq_nonneg _)
  have hsos102 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (-(conductance 0 * probe 0) - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 3).le))) (sq_nonneg _)
  have hsos103 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (-(conductance 0 * probe 0) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 4).le))) (sq_nonneg _)
  have hsos104 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 0 * weight 5) * (-(conductance 0 * probe 0)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 5).le))) (sq_nonneg _)
  have hsos105 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 1).le) ((hw 3).le))) (sq_nonneg _)
  have hsos106 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 1).le) ((hw 4).le))) (sq_nonneg _)
  have hsos107 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 2).le) ((hw 3).le))) (sq_nonneg _)
  have hsos108 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 2).le) ((hw 4).le))) (sq_nonneg _)
  have hsos109 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1)) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 3).le) ((hw 4).le))) (sq_nonneg _)
  have hsos110 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 3).le) ((hw 5).le))) (sq_nonneg _)
  have hsos111 : (0 : ℝ) ≤ conductance 1 * weight 1 * (conductance 5 * weight 5) * (weight 4 * weight 5) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 1).le) ((hw 1).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 4).le) ((hw 5).le))) (sq_nonneg _)
  have hsos112 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 1) * (conductance 0 * probe 0 - (conductance 1 * probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 0).le) ((hw 1).le))) (sq_nonneg _)
  have hsos113 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 2) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 0).le) ((hw 2).le))) (sq_nonneg _)
  have hsos114 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 3) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 0).le) ((hw 3).le))) (sq_nonneg _)
  have hsos115 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 4) * (conductance 0 * probe 0 - (conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 0).le) ((hw 4).le))) (sq_nonneg _)
  have hsos116 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 0 * weight 5) * (conductance 0 * probe 0 - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 0).le) ((hw 5).le))) (sq_nonneg _)
  have hsos117 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 1 * weight 2) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 1).le) ((hw 2).le))) (sq_nonneg _)
  have hsos118 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 1 * weight 3) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 1).le) ((hw 3).le))) (sq_nonneg _)
  have hsos119 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 1 * weight 4) * (conductance 1 * probe 1 - (conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 1).le) ((hw 4).le))) (sq_nonneg _)
  have hsos120 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 1 * weight 5) * (conductance 1 * probe 1 - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 1).le) ((hw 5).le))) (sq_nonneg _)
  have hsos121 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 2 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 2).le) ((hw 4).le))) (sq_nonneg _)
  have hsos122 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 2 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 2).le) ((hw 5).le))) (sq_nonneg _)
  have hsos123 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 3 * weight 4) * (conductance 4 * (probe 0 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 3).le) ((hw 4).le))) (sq_nonneg _)
  have hsos124 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 3 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 3).le) ((hw 5).le))) (sq_nonneg _)
  have hsos125 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 3 * weight 3) * (weight 4 * weight 5) * (conductance 4 * (probe 0 - probe 2) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 3).le) ((hw 3).le))) (mul_nonneg ((hw 4).le) ((hw 5).le))) (sq_nonneg _)
  have hsos126 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 0 * weight 1) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 0).le) ((hw 1).le))) (sq_nonneg _)
  have hsos127 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 0 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 0).le) ((hw 3).le))) (sq_nonneg _)
  have hsos128 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 0 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 0).le) ((hw 5).le))) (sq_nonneg _)
  have hsos129 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 1 * weight 2) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 1).le) ((hw 2).le))) (sq_nonneg _)
  have hsos130 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 1 * weight 3) * (conductance 1 * probe 1 - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 1).le) ((hw 3).le))) (sq_nonneg _)
  have hsos131 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 1).le) ((hw 4).le))) (sq_nonneg _)
  have hsos132 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 1 * weight 5) * (conductance 1 * probe 1 - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 1).le) ((hw 5).le))) (sq_nonneg _)
  have hsos133 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 2 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 2).le) ((hw 3).le))) (sq_nonneg _)
  have hsos134 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 2 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 2).le) ((hw 5).le))) (sq_nonneg _)
  have hsos135 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 3).le) ((hw 4).le))) (sq_nonneg _)
  have hsos136 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1)) - (conductance 5 * (probe 1 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 3).le) ((hw 5).le))) (sq_nonneg _)
  have hsos137 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 4 * weight 4) * (weight 4 * weight 5) * (conductance 5 * (probe 1 - probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 4).le) ((hw 5).le))) (sq_nonneg _)
  have hsos138 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (-(conductance 0 * probe 0)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 1).le))) (sq_nonneg _)
  have hsos139 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (-(conductance 0 * probe 0)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 2).le))) (sq_nonneg _)
  have hsos140 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (-(conductance 0 * probe 0) - (-(conductance 3 * (probe 0 - probe 1)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 3).le))) (sq_nonneg _)
  have hsos141 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (-(conductance 0 * probe 0) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 4).le))) (sq_nonneg _)
  have hsos142 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 0 * weight 5) * (-(conductance 0 * probe 0)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 5).le))) (sq_nonneg _)
  have hsos143 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 1).le) ((hw 3).le))) (sq_nonneg _)
  have hsos144 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 1).le) ((hw 4).le))) (sq_nonneg _)
  have hsos145 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 2).le) ((hw 3).le))) (sq_nonneg _)
  have hsos146 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 2).le) ((hw 4).le))) (sq_nonneg _)
  have hsos147 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 3 * weight 4) * (-(conductance 3 * (probe 0 - probe 1)) - (-(conductance 4 * (probe 0 - probe 2)))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 3).le) ((hw 4).le))) (sq_nonneg _)
  have hsos148 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 3 * weight 5) * (-(conductance 3 * (probe 0 - probe 1))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 3).le) ((hw 5).le))) (sq_nonneg _)
  have hsos149 : (0 : ℝ) ≤ conductance 2 * weight 2 * (conductance 5 * weight 5) * (weight 4 * weight 5) * (-(conductance 4 * (probe 0 - probe 2))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 2).le) ((hw 2).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 4).le) ((hw 5).le))) (sq_nonneg _)
  have hsos150 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 1) * (conductance 0 * probe 0 - (conductance 1 * probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 0).le) ((hw 1).le))) (sq_nonneg _)
  have hsos151 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 2) * (conductance 0 * probe 0 - (conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 0).le) ((hw 2).le))) (sq_nonneg _)
  have hsos152 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 3) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 0).le) ((hw 3).le))) (sq_nonneg _)
  have hsos153 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 4) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 0).le) ((hw 4).le))) (sq_nonneg _)
  have hsos154 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 0 * weight 5) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 0).le) ((hw 5).le))) (sq_nonneg _)
  have hsos155 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 1 * weight 2) * (conductance 1 * probe 1 - (conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 1).le) ((hw 2).le))) (sq_nonneg _)
  have hsos156 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 1 * weight 3) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 1).le) ((hw 3).le))) (sq_nonneg _)
  have hsos157 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 1).le) ((hw 4).le))) (sq_nonneg _)
  have hsos158 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 1 * weight 5) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 1).le) ((hw 5).le))) (sq_nonneg _)
  have hsos159 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 2 * weight 3) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 2).le) ((hw 3).le))) (sq_nonneg _)
  have hsos160 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 2 * weight 4) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 2).le) ((hw 4).le))) (sq_nonneg _)
  have hsos161 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 4 * weight 4) * (weight 2 * weight 5) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 4).le) ((hw 4).le))) (mul_nonneg ((hw 2).le) ((hw 5).le))) (sq_nonneg _)
  have hsos162 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (conductance 0 * probe 0 - (conductance 1 * probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 1).le))) (sq_nonneg _)
  have hsos163 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (conductance 0 * probe 0 - (conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 2).le))) (sq_nonneg _)
  have hsos164 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 3).le))) (sq_nonneg _)
  have hsos165 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 4).le))) (sq_nonneg _)
  have hsos166 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 0 * weight 5) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 5).le))) (sq_nonneg _)
  have hsos167 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 1 * weight 2) * (conductance 1 * probe 1 - (conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 1).le) ((hw 2).le))) (sq_nonneg _)
  have hsos168 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 1).le) ((hw 3).le))) (sq_nonneg _)
  have hsos169 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 1).le) ((hw 4).le))) (sq_nonneg _)
  have hsos170 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 1 * weight 5) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 1).le) ((hw 5).le))) (sq_nonneg _)
  have hsos171 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 2).le) ((hw 3).le))) (sq_nonneg _)
  have hsos172 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 2).le) ((hw 4).le))) (sq_nonneg _)
  have hsos173 : (0 : ℝ) ≤ conductance 3 * weight 3 * (conductance 5 * weight 5) * (weight 2 * weight 5) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 3).le) ((hw 3).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 2).le) ((hw 5).le))) (sq_nonneg _)
  have hsos174 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 1) * (conductance 0 * probe 0 - (conductance 1 * probe 1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 4).le) ((hw 4).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 1).le))) (sq_nonneg _)
  have hsos175 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 2) * (conductance 0 * probe 0 - (conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 4).le) ((hw 4).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 2).le))) (sq_nonneg _)
  have hsos176 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 3) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 4).le) ((hw 4).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 3).le))) (sq_nonneg _)
  have hsos177 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 4) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 4).le) ((hw 4).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 4).le))) (sq_nonneg _)
  have hsos178 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 0 * weight 5) * (conductance 0 * probe 0) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 4).le) ((hw 4).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 0).le) ((hw 5).le))) (sq_nonneg _)
  have hsos179 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 1 * weight 2) * (conductance 1 * probe 1 - (conductance 2 * probe 2)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 4).le) ((hw 4).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 1).le) ((hw 2).le))) (sq_nonneg _)
  have hsos180 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 1 * weight 3) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 4).le) ((hw 4).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 1).le) ((hw 3).le))) (sq_nonneg _)
  have hsos181 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 1 * weight 4) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 4).le) ((hw 4).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 1).le) ((hw 4).le))) (sq_nonneg _)
  have hsos182 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 1 * weight 5) * (conductance 1 * probe 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 4).le) ((hw 4).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 1).le) ((hw 5).le))) (sq_nonneg _)
  have hsos183 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 2 * weight 3) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 4).le) ((hw 4).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 2).le) ((hw 3).le))) (sq_nonneg _)
  have hsos184 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 2 * weight 4) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 4).le) ((hw 4).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 2).le) ((hw 4).le))) (sq_nonneg _)
  have hsos185 : (0 : ℝ) ≤ conductance 4 * weight 4 * (conductance 5 * weight 5) * (weight 2 * weight 5) * (conductance 2 * probe 2) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((hcond 4).le) ((hw 4).le)) (mul_nonneg ((hcond 5).le) ((hw 5).le))) (mul_nonneg ((hw 2).le) ((hw 5).le))) (sq_nonneg _)
  rw [hsix, mul_one] at hkey
  have hcases : probe 0 ≠ 0 ∨ probe 1 ≠ 0 ∨ probe 2 ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨hzero, hone, htwo⟩ := hall
    exact hprobe (funext fun coord => by
      fin_cases coord <;> simp [hzero, hone, htwo])
  rcases hcases with hval | hval | hval
  · have hdiff : conductance 0 * probe 0 ≠ 0 :=
      mul_ne_zero (hcond 0).ne' hval
    have hwitness : 0 < conductance 1 * weight 1 * (conductance 2 * weight 2)
        * (weight 0 * weight 1) * (conductance 0 * probe 0) ^ 2 :=
      mul_pos (mul_pos (mul_pos (mul_pos (hcond 1) (hw 1))
          (mul_pos (hcond 2) (hw 2))) (mul_pos (hw 0) (hw 1)))
        (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hdiff)))
    linarith
  · have hdiff : -(conductance 1 * probe 1) ≠ 0 :=
      neg_ne_zero.mpr (mul_ne_zero (hcond 1).ne' hval)
    have hwitness : 0 < conductance 0 * weight 0 * (conductance 2 * weight 2)
        * (weight 0 * weight 1) * (-(conductance 1 * probe 1)) ^ 2 :=
      mul_pos (mul_pos (mul_pos (mul_pos (hcond 0) (hw 0))
          (mul_pos (hcond 2) (hw 2))) (mul_pos (hw 0) (hw 1)))
        (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hdiff)))
    linarith
  · have hdiff : conductance 2 * probe 2 ≠ 0 :=
      mul_ne_zero (hcond 2).ne' hval
    have hwitness : 0 < conductance 0 * weight 0 * (conductance 1 * weight 1)
        * (weight 0 * weight 2) * (conductance 2 * probe 2) ^ 2 :=
      mul_pos (mul_pos (mul_pos (mul_pos (hcond 0) (hw 0))
          (mul_pos (hcond 1) (hw 1))) (mul_pos (hw 0) (hw 2)))
        (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hdiff)))
    linarith

/-- **P1, STRICT, mixture form**: `x^T (sum_T (prod_T m) S_T) x
> det B * (x^T B x)` at every nonzero probe. -/
theorem kFour_mixtureLaw_strict (conductance weight : Fin 6 → ℝ)
    (probe : Fin 3 → ℝ)
    (hcond : ∀ edge, 0 < conductance edge) (hw : ∀ edge, 0 < weight edge)
    (hsum : ∑ edge, weight edge = 1) (hprobe : probe ≠ 0) :
    kFourSpanningTreeSum (fun edge => conductance edge * weight edge)
        * (probe ⬝ᵥ (kFourWeightLaplacian
            (fun edge => conductance edge * weight edge)).mulVec probe)
      < (k4TreeTriples.map fun tree =>
          kFourTreeWeightProduct (fun edge => conductance edge * weight edge)
              tree
            * (conductance tree.1 * k4Drop probe tree.1 ^ 2
              + conductance tree.2.1 * k4Drop probe tree.2.1 ^ 2
              + conductance tree.2.2 * k4Drop probe tree.2.2 ^ 2)).sum := by
  rw [kFour_mixture_treeForm_expansion]
  exact kFour_mixtureLaw_leverageForm_strict conductance weight probe hcond hw
    hsum hprobe

end Gtz
