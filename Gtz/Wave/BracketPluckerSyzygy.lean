/-
# The Plücker syzygy of the bracket masses

The bracket masses of a design are the diagonal of a RANK-ONE form
(`Gtz.BracketPhaseRigidity`), so they are the squared coordinates of a single
vector `b` in `Λ³ℝ⁶`.  That vector is not free: it is the Plücker vector of a
three-plane, and Plücker vectors satisfy the GRASSMANN–PLÜCKER SYZYGIES.  This
module lands the syzygy and reads it in the campaign's currencies.

* `Gtz.tripleBracket_plucker` — the three-term relation for five vectors of
  `ℝ³`, `[abc][ade] − [abd][ace] + [abe][acd] = 0`, by `ring`;
* `Gtz.weightedBracket_plucker` — the same syzygy on the WEIGHTED brackets
  `b_C = √(t_at_bt_c)·[abc]`, whose squares are the bracket masses.  All three
  products carry the identical weight factor `t_a·√(t_bt_ct_dt_e)`, so the
  syzygy survives the weighting untouched;
* **THE MASS TRIANGLE BOUND** (`Gtz.bracketMass_triangle`): squaring the
  syzygy and discarding the cross term,

    `m_{abc}·m_{ade} ≤ 2·(m_{abd}·m_{ace} + m_{abe}·m_{acd})` ,

  a polynomial constraint on the mass distribution that is MULTIPLICATIVE in
  the masses — three products of pairs, never a sum of masses.  The twenty
  masses are therefore not an arbitrary probability distribution on the
  triples: through every five labels they obey a triangle bound on their
  pairwise products.

The syzygy is the one structure that distinguishes the masses of an ACTUAL
design from an arbitrary nonnegative family with the right marginals, and it
is field-blind — the realness of this lane stays at the two named carriers,
`Gtz.pair_mass_nonneg` and `Gtz.bracket_threeCycle_nonneg`.
-/
import Gtz.Wave.BracketPhaseRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The syzygies of brackets -/

/-- **THE GRASSMANN–PLÜCKER THREE-TERM SYZYGY.**  For any five vectors of
`ℝ³`, `[abc][ade] − [abd][ace] + [abe][acd] = 0`.  A polynomial identity in
fifteen coordinates. -/
theorem tripleBracket_plucker (a b c d e : Fin 3 → ℝ) :
    tripleBracket a b c * tripleBracket a d e
      - tripleBracket a b d * tripleBracket a c e
      + tripleBracket a b e * tripleBracket a c d = 0 := by
  simp only [tripleBracket_eq]
  ring

/-! ## 2. The weighted syzygy -/

/-- The weighted bracket of a triple: the square root of the weight product
times the bracket.  Its square is the bracket mass. -/
noncomputable def weightedBracket (D : WeightedDesign m 3) (a b c : Fin m) : ℝ :=
  Real.sqrt (D.weight a) * Real.sqrt (D.weight b) * Real.sqrt (D.weight c)
    * atomBracket D a b c

/-- The square of a weighted bracket is the bracket mass of its triple. -/
theorem sq_weightedBracket (D : WeightedDesign m 3) (a b c : Fin m) :
    weightedBracket D a b c ^ 2
      = D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2)) := by
  have h0 : Real.sqrt (D.weight a) ^ 2 = D.weight a := Real.sq_sqrt (D.weight_pos a).le
  have h1 : Real.sqrt (D.weight b) ^ 2 = D.weight b := Real.sq_sqrt (D.weight_pos b).le
  have h2 : Real.sqrt (D.weight c) ^ 2 = D.weight c := Real.sq_sqrt (D.weight_pos c).le
  calc weightedBracket D a b c ^ 2
      = Real.sqrt (D.weight a) ^ 2 * (Real.sqrt (D.weight b) ^ 2
          * (Real.sqrt (D.weight c) ^ 2 * atomBracket D a b c ^ 2)) := by
        rw [weightedBracket]; ring
    _ = _ := by rw [h0, h1, h2]

/-- **THE WEIGHTED SYZYGY.**  The three-term Plücker relation survives the
weighting: all three products carry the identical factor
`t_a·√(t_bt_ct_dt_e)`, so

  `b_{abc}b_{ade} − b_{abd}b_{ace} + b_{abe}b_{acd} = 0` . -/
theorem weightedBracket_plucker (D : WeightedDesign m 3) (a b c d e : Fin m) :
    weightedBracket D a b c * weightedBracket D a d e
      - weightedBracket D a b d * weightedBracket D a c e
      + weightedBracket D a b e * weightedBracket D a c d = 0 := by
  have hsq : Real.sqrt (D.weight a) * Real.sqrt (D.weight a) = D.weight a :=
    Real.mul_self_sqrt (D.weight_pos a).le
  have hgp := tripleBracket_plucker (D.atom a) (D.atom b) (D.atom c)
    (D.atom d) (D.atom e)
  rw [← atomBracket, ← atomBracket, ← atomBracket, ← atomBracket, ← atomBracket,
    ← atomBracket] at hgp
  have hfactor : weightedBracket D a b c * weightedBracket D a d e
      - weightedBracket D a b d * weightedBracket D a c e
      + weightedBracket D a b e * weightedBracket D a c d
      = ((Real.sqrt (D.weight a) * Real.sqrt (D.weight a))
          * (Real.sqrt (D.weight b) * Real.sqrt (D.weight c)
            * Real.sqrt (D.weight d) * Real.sqrt (D.weight e)))
        * (atomBracket D a b c * atomBracket D a d e
          - atomBracket D a b d * atomBracket D a c e
          + atomBracket D a b e * atomBracket D a c d) := by
    simp only [weightedBracket]
    ring
  rw [hfactor, hgp, mul_zero]

/-! ## 3. The mass triangle bound -/

/-- **THE MASS TRIANGLE BOUND.**  Squaring the weighted syzygy and discarding
the cross term by `2xy ≤ x² + y²`:

  `m_{abc}·m_{ade} ≤ 2·(m_{abd}·m_{ace} + m_{abe}·m_{acd})` .

A polynomial, MULTIPLICATIVE constraint on the bracket masses through every
five labels — products of pairs on both sides, never a sum of masses.  The
twenty masses are a probability distribution on the triples
(`Gtz.bracketMass_nonneg` with the bracket budget), but not an arbitrary one:
this bound is what an actual design's masses satisfy and a generic
distribution does not. -/
theorem bracketMass_triangle (D : WeightedDesign m 3) (a b c d e : Fin m) :
    (D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2)))
        * (D.weight a * (D.weight d * (D.weight e * atomBracket D a d e ^ 2)))
      ≤ 2 * ((D.weight a * (D.weight b * (D.weight d * atomBracket D a b d ^ 2)))
            * (D.weight a * (D.weight c * (D.weight e * atomBracket D a c e ^ 2)))
          + (D.weight a * (D.weight b * (D.weight e * atomBracket D a b e ^ 2)))
            * (D.weight a * (D.weight c * (D.weight d * atomBracket D a c d ^ 2)))) := by
  have hsyz := weightedBracket_plucker D a b c d e
  set p : ℝ := weightedBracket D a b c * weightedBracket D a d e with hp
  set q : ℝ := weightedBracket D a b d * weightedBracket D a c e with hq
  set r : ℝ := weightedBracket D a b e * weightedBracket D a c d with hr
  have hpqr : p = q - r := by rw [hp, hq, hr]; linarith [hsyz]
  have hbound : p ^ 2 ≤ 2 * (q ^ 2 + r ^ 2) := by
    rw [hpqr]; nlinarith [sq_nonneg (q + r), sq_nonneg (q - r)]
  have hexp : ∀ u v w x y z : Fin m,
      (weightedBracket D u v w * weightedBracket D x y z) ^ 2
        = (D.weight u * (D.weight v * (D.weight w * atomBracket D u v w ^ 2)))
          * (D.weight x * (D.weight y * (D.weight z * atomBracket D x y z ^ 2))) := by
    intro u v w x y z
    rw [mul_pow, sq_weightedBracket, sq_weightedBracket]
  rw [hp, hq, hr, hexp, hexp, hexp] at hbound
  linarith [hbound]

/-- **A VANISHING PAIR OF MASSES FORCES A THIRD.**  If two of the three
Plücker products vanish then so does the first: through five labels the masses
cannot vanish in an arbitrary pattern.  With
`Gtz.hasParallelPair_iff_exists_pair_bracket_mass_zero` this constrains where
the hinge's zero can sit. -/
theorem bracketMass_plucker_propagation (D : WeightedDesign m 3) (a b c d e : Fin m)
    (hq : weightedBracket D a b d * weightedBracket D a c e = 0)
    (hr : weightedBracket D a b e * weightedBracket D a c d = 0) :
    weightedBracket D a b c * weightedBracket D a d e = 0 := by
  have hsyz := weightedBracket_plucker D a b c d e
  linarith [hsyz, hq, hr]

end Gtz
