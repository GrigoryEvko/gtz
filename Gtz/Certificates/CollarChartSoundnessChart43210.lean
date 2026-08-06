import Gtz.Certificates.CollarChartReplay
import Gtz.Certificates.CollarChartSoundness

/-!
# Bridge (ii) instantiated: chart soundness for the barycentric order chart
43210

One kernel-checked identity per flat dictionary core: the substituted flat
core equals the certificate-side product of sign-carrying atoms and chart
cores.  Combined with `polyEval_substituteFlatPoly` and
`normalizerValueIsPos` of `CollarChartSoundness`, this says exactly that the
sign of every emitted chart polynomial at a chart point is the sign of the
flat dictionary core at the corresponding weight point.

Emitted: 393 of 393 flat cores -- those whose Lean-side
unreduced substitution stays under 4000 terms.  The rest are
blocked only by `powPoly normalizerPoly k` expanding to `5^k` terms before
canonicalization; precomputed reduced normalizer powers (one `decide` per
step, `canon (polyMul N^k N) = canon N^(k+1)`) remove that ceiling.
-/

namespace GtzCollarChartSoundnessChart43210

open Gtz.CollarReplay GtzCollarChartSoundness

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-- The order chart 43210: the slot of each rim weight. -/
def orderChart43210 : OrderChart :=
  ⟨3, 2, 1, 0⟩

/-- Chart core 0 of the barycentric order chart 43210,
homogenized to degree 15. -/
def chartCore0 : Poly :=
  [tm 15 0 0 0 0 (1),
    tm 14 0 0 1 0 (-1),
    tm 13 0 1 1 0 (1),
    tm 12 0 1 2 0 (-1),
    tm 11 0 1 2 1 (-1),
    tm 14 1 0 0 0 (1),
    tm 13 1 0 1 0 (-3),
    tm 13 1 1 0 0 (2),
    tm 12 1 1 1 0 (-1),
    tm 11 1 1 1 1 (3),
    tm 11 1 1 2 0 (-7),
    tm 10 1 1 2 1 (-5),
    tm 11 1 2 1 0 (2),
    tm 10 1 2 2 0 (-2),
    tm 9 1 2 3 0 (-4),
    tm 8 1 2 3 1 (-6),
    tm 7 1 2 3 2 (-2),
    tm 12 2 0 1 0 (-2),
    tm 12 2 1 0 0 (2),
    tm 11 2 1 1 0 (-4),
    tm 10 2 1 1 1 (2),
    tm 10 2 1 2 0 (-8),
    tm 9 2 1 2 1 (-7),
    tm 11 2 2 0 0 (1),
    tm 10 2 2 1 0 (1),
    tm 9 2 2 1 1 (4),
    tm 9 2 2 2 0 (-10),
    tm 8 2 2 2 1 (-4),
    tm 7 2 2 2 2 (3),
    tm 8 2 2 3 0 (-10),
    tm 7 2 2 3 1 (-17),
    tm 6 2 2 3 2 (-6),
    tm 9 2 3 1 0 (1),
    tm 8 2 3 2 0 (-1),
    tm 7 2 3 2 1 (1),
    tm 7 2 3 3 0 (-6),
    tm 6 2 3 3 1 (-8),
    tm 5 2 3 3 2 (-1),
    tm 6 2 3 4 0 (-4),
    tm 5 2 3 4 1 (-10),
    tm 4 2 3 4 2 (-7),
    tm 3 2 3 4 3 (-1),
    tm 10 3 1 1 0 (-2),
    tm 9 3 1 2 0 (-2),
    tm 8 3 1 2 1 (-2),
    tm 10 3 2 0 0 (1),
    tm 9 3 2 1 0 (-1),
    tm 8 3 2 1 1 (2),
    tm 8 3 2 2 0 (-8),
    tm 7 3 2 2 1 (-5),
    tm 6 3 2 2 2 (1),
    tm 7 3 2 3 0 (-6),
    tm 6 3 2 3 1 (-10),
    tm 5 3 2 3 2 (-4),
    tm 8 3 3 1 0 (1),
    tm 7 3 3 1 1 (1),
    tm 7 3 3 2 0 (-3),
    tm 6 3 3 2 1 (1),
    tm 5 3 3 2 2 (2),
    tm 6 3 3 3 0 (-10),
    tm 5 3 3 3 1 (-13),
    tm 4 3 3 3 2 (-2),
    tm 3 3 3 3 3 (1),
    tm 5 3 3 4 0 (-6),
    tm 4 3 3 4 1 (-14),
    tm 3 3 3 4 2 (-10),
    tm 2 3 3 4 3 (-2),
    tm 5 3 4 3 0 (-2),
    tm 4 3 4 3 1 (-2),
    tm 4 3 4 4 0 (-4),
    tm 3 3 4 4 1 (-8),
    tm 2 3 4 4 2 (-4),
    tm 3 3 4 5 0 (-2),
    tm 2 3 4 5 1 (-6),
    tm 1 3 4 5 2 (-6),
    tm 0 3 4 5 3 (-2)]

/-- Chart core 1 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore1 : Poly :=
  [tm 13 0 0 0 0 (2),
    tm 12 0 1 0 0 (2),
    tm 11 0 1 1 0 (2),
    tm 10 0 1 1 1 (2),
    tm 12 1 0 0 0 (3),
    tm 11 1 0 1 0 (-1),
    tm 11 1 1 0 0 (8),
    tm 10 1 1 1 0 (4),
    tm 9 1 1 1 1 (7),
    tm 9 1 1 2 0 (-2),
    tm 8 1 1 2 1 (-2),
    tm 10 1 2 0 0 (6),
    tm 9 1 2 1 0 (8),
    tm 8 1 2 1 1 (10),
    tm 8 1 2 2 0 (1),
    tm 7 1 2 2 1 (5),
    tm 6 1 2 2 2 (4),
    tm 7 1 2 3 0 (-1),
    tm 6 1 2 3 1 (-2),
    tm 5 1 2 3 2 (-1),
    tm 11 2 0 0 0 (1),
    tm 10 2 0 1 0 (-1),
    tm 10 2 1 0 0 (7),
    tm 9 2 1 1 0 (1),
    tm 8 2 1 1 1 (5),
    tm 8 2 1 2 0 (-2),
    tm 7 2 1 2 1 (-3),
    tm 9 2 2 0 0 (10),
    tm 8 2 2 1 0 (10),
    tm 7 2 2 1 1 (17),
    tm 7 2 2 2 0 (-1),
    tm 6 2 2 2 1 (4),
    tm 5 2 2 2 2 (6),
    tm 6 2 2 3 0 (-1),
    tm 5 2 2 3 1 (-4),
    tm 4 2 2 3 2 (-3),
    tm 8 2 3 0 0 (6),
    tm 7 2 3 1 0 (10),
    tm 6 2 3 1 1 (14),
    tm 6 2 3 2 0 (3),
    tm 5 2 3 2 1 (13),
    tm 4 2 3 2 2 (10),
    tm 5 2 3 3 0 (-1),
    tm 4 2 3 3 1 (-1),
    tm 3 2 3 3 2 (2),
    tm 2 2 3 3 3 (2),
    tm 3 2 3 4 1 (-1),
    tm 2 2 3 4 2 (-2),
    tm 1 2 3 4 3 (-1),
    tm 9 3 1 0 0 (1),
    tm 8 3 1 1 0 (-1),
    tm 7 3 1 1 1 (1),
    tm 8 3 2 0 0 (4),
    tm 7 3 2 1 0 (2),
    tm 6 3 2 1 1 (6),
    tm 6 3 2 2 0 (-2),
    tm 4 3 2 2 2 (2),
    tm 7 3 3 0 0 (4),
    tm 6 3 3 1 0 (6),
    tm 5 3 3 1 1 (10),
    tm 5 3 3 2 0 (1),
    tm 4 3 3 2 1 (8),
    tm 3 3 3 2 2 (7),
    tm 4 3 3 3 0 (-1),
    tm 3 3 3 3 1 (-1),
    tm 2 3 3 3 2 (1),
    tm 1 3 3 3 3 (1),
    tm 6 3 4 0 0 (2),
    tm 5 3 4 1 0 (4),
    tm 4 3 4 1 1 (6),
    tm 4 3 4 2 0 (2),
    tm 3 3 4 2 1 (8),
    tm 2 3 4 2 2 (6),
    tm 2 3 4 3 1 (2),
    tm 1 3 4 3 2 (4),
    tm 0 3 4 3 3 (2)]

/-- Chart core 2 of the barycentric order chart 43210,
homogenized to degree 14. -/
def chartCore2 : Poly :=
  [tm 13 0 1 0 0 (1),
    tm 12 0 1 1 0 (1),
    tm 11 0 2 1 0 (1),
    tm 10 0 2 2 0 (1),
    tm 9 0 2 2 1 (1),
    tm 13 1 0 0 0 (-2),
    tm 12 1 1 0 0 (-1),
    tm 11 1 1 1 0 (-3),
    tm 10 1 1 1 1 (-2),
    tm 11 1 2 0 0 (2),
    tm 10 1 2 1 0 (1),
    tm 9 1 2 1 1 (1),
    tm 9 1 2 2 0 (-1),
    tm 8 1 2 2 1 (1),
    tm 9 1 3 1 0 (2),
    tm 8 1 3 2 0 (2),
    tm 7 1 3 2 1 (4),
    tm 6 1 3 3 1 (2),
    tm 5 1 3 3 2 (2),
    tm 12 2 0 0 0 (-4),
    tm 11 2 1 0 0 (-6),
    tm 10 2 1 1 0 (-10),
    tm 9 2 1 1 1 (-8),
    tm 10 2 2 0 0 (-2),
    tm 9 2 2 1 0 (-10),
    tm 8 2 2 1 1 (-8),
    tm 8 2 2 2 0 (-8),
    tm 7 2 2 2 1 (-13),
    tm 6 2 2 2 2 (-4),
    tm 9 2 3 0 0 (1),
    tm 8 2 3 1 0 (-1),
    tm 7 2 3 2 0 (-4),
    tm 6 2 3 2 1 (-4),
    tm 5 2 3 2 2 (-1),
    tm 6 2 3 3 0 (-2),
    tm 5 2 3 3 1 (-5),
    tm 4 2 3 3 2 (-2),
    tm 7 2 4 1 0 (1),
    tm 6 2 4 2 0 (1),
    tm 5 2 4 2 1 (3),
    tm 4 2 4 3 1 (2),
    tm 3 2 4 3 2 (3),
    tm 2 2 4 4 2 (1),
    tm 1 2 4 4 3 (1),
    tm 11 3 0 0 0 (-2),
    tm 10 3 1 0 0 (-4),
    tm 9 3 1 1 0 (-6),
    tm 8 3 1 1 1 (-6),
    tm 9 3 2 0 0 (-4),
    tm 8 3 2 1 0 (-10),
    tm 7 3 2 1 1 (-10),
    tm 7 3 2 2 0 (-6),
    tm 6 3 2 2 1 (-14),
    tm 5 3 2 2 2 (-6),
    tm 8 3 3 0 0 (-1),
    tm 7 3 3 1 0 (-7),
    tm 6 3 3 1 1 (-6),
    tm 6 3 3 2 0 (-8),
    tm 5 3 3 2 1 (-17),
    tm 4 3 3 2 2 (-7),
    tm 5 3 3 3 0 (-2),
    tm 4 3 3 3 1 (-10),
    tm 3 3 3 3 2 (-10),
    tm 2 3 3 3 3 (-2),
    tm 6 3 4 1 0 (-1),
    tm 5 3 4 1 1 (-1),
    tm 5 3 4 2 0 (-3),
    tm 4 3 4 2 1 (-5),
    tm 3 3 4 2 2 (-2),
    tm 4 3 4 3 0 (-2),
    tm 3 3 4 3 1 (-7),
    tm 2 3 4 3 2 (-6),
    tm 1 3 4 3 3 (-1),
    tm 2 3 4 4 1 (-2),
    tm 1 3 4 4 2 (-4),
    tm 0 3 4 4 3 (-2)]

/-- Chart core 3 of the barycentric order chart 43210,
homogenized to degree 15. -/
def chartCore3 : Poly :=
  [tm 15 0 0 0 0 (2),
    tm 14 1 0 0 0 (4),
    tm 13 1 1 0 0 (6),
    tm 12 1 1 1 0 (4),
    tm 11 1 1 1 1 (6),
    tm 13 2 0 0 0 (2),
    tm 12 2 1 0 0 (10),
    tm 11 2 1 1 0 (6),
    tm 10 2 1 1 1 (8),
    tm 11 2 2 0 0 (6),
    tm 10 2 2 1 0 (10),
    tm 9 2 2 1 1 (14),
    tm 9 2 2 2 0 (4),
    tm 8 2 2 2 1 (10),
    tm 7 2 2 2 2 (6),
    tm 11 3 1 0 0 (3),
    tm 10 3 1 1 0 (1),
    tm 9 3 1 1 1 (2),
    tm 10 3 2 0 0 (8),
    tm 9 3 2 1 0 (10),
    tm 8 3 2 1 1 (13),
    tm 8 3 2 2 0 (2),
    tm 7 3 2 2 1 (8),
    tm 6 3 2 2 2 (4),
    tm 9 3 3 0 0 (2),
    tm 8 3 3 1 0 (8),
    tm 7 3 3 1 1 (10),
    tm 7 3 3 2 0 (7),
    tm 6 3 3 2 1 (17),
    tm 5 3 3 2 2 (10),
    tm 6 3 3 3 0 (1),
    tm 5 3 3 3 1 (6),
    tm 4 3 3 3 2 (7),
    tm 3 3 3 3 3 (2),
    tm 10 4 1 0 0 (-1),
    tm 9 4 1 1 0 (-1),
    tm 9 4 2 0 0 (1),
    tm 8 4 2 1 0 (-1),
    tm 7 4 2 1 1 (-1),
    tm 7 4 2 2 0 (-2),
    tm 6 4 2 2 1 (-1),
    tm 8 4 3 0 0 (2),
    tm 7 4 3 1 0 (4),
    tm 6 4 3 1 1 (5),
    tm 6 4 3 2 0 (1),
    tm 5 4 3 2 1 (4),
    tm 4 4 3 2 2 (2),
    tm 5 4 3 3 0 (-1),
    tm 3 4 3 3 2 (1),
    tm 6 4 4 1 0 (2),
    tm 5 4 4 1 1 (2),
    tm 5 4 4 2 0 (3),
    tm 4 4 4 2 1 (7),
    tm 3 4 4 2 2 (4),
    tm 4 4 4 3 0 (1),
    tm 3 4 4 3 1 (5),
    tm 2 4 4 3 2 (6),
    tm 1 4 4 3 3 (2),
    tm 2 4 4 4 1 (1),
    tm 1 4 4 4 2 (2),
    tm 0 4 4 4 3 (1),
    tm 8 5 2 0 0 (-1),
    tm 7 5 2 1 0 (-1),
    tm 6 5 2 1 1 (-1),
    tm 6 5 3 1 0 (-2),
    tm 5 5 3 1 1 (-2),
    tm 5 5 3 2 0 (-2),
    tm 4 5 3 2 1 (-4),
    tm 3 5 3 2 2 (-2),
    tm 4 5 4 2 0 (-1),
    tm 3 5 4 2 1 (-2),
    tm 2 5 4 2 2 (-1),
    tm 3 5 4 3 0 (-1),
    tm 2 5 4 3 1 (-3),
    tm 1 5 4 3 2 (-3),
    tm 0 5 4 3 3 (-1)]

/-- Chart core 4 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore4 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 7 0 0 1 0 (1),
    tm 6 0 1 1 0 (1),
    tm 5 0 1 2 0 (1),
    tm 4 0 1 2 1 (-1),
    tm 7 1 0 0 0 (1),
    tm 6 1 0 1 0 (1),
    tm 6 1 1 0 0 (1),
    tm 5 1 1 1 0 (2),
    tm 4 1 1 1 1 (2),
    tm 4 1 1 2 0 (1),
    tm 4 1 2 1 0 (1),
    tm 3 1 2 2 0 (1),
    tm 1 1 2 3 1 (-1),
    tm 0 1 2 3 2 (-1),
    tm 5 2 1 0 0 (1),
    tm 4 2 1 1 0 (1),
    tm 3 2 1 1 1 (1),
    tm 3 2 2 1 0 (1),
    tm 2 2 2 1 1 (1),
    tm 2 2 2 2 0 (1),
    tm 1 2 2 2 1 (2),
    tm 0 2 2 2 2 (1)]

/-- Chart core 5 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore5 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 7 0 0 1 0 (1),
    tm 6 0 1 1 0 (1),
    tm 5 0 1 2 0 (1),
    tm 4 0 1 2 1 (1),
    tm 7 1 0 0 0 (1),
    tm 6 1 0 1 0 (1),
    tm 6 1 1 0 0 (1),
    tm 5 1 1 1 0 (2),
    tm 4 1 1 2 0 (1),
    tm 3 1 1 2 1 (2),
    tm 4 1 2 1 0 (1),
    tm 3 1 2 2 0 (1),
    tm 2 1 2 2 1 (2),
    tm 1 1 2 3 1 (1),
    tm 0 1 2 3 2 (1),
    tm 5 2 1 0 0 (1),
    tm 4 2 1 1 0 (1),
    tm 3 2 1 1 1 (-1),
    tm 3 2 2 1 0 (1),
    tm 2 2 2 1 1 (-1),
    tm 2 2 2 2 0 (1),
    tm 0 2 2 2 2 (-1)]

/-- Chart core 6 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore6 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 4 0 1 1 0 (1),
    tm 5 1 0 0 0 (1),
    tm 3 1 0 1 1 (-1),
    tm 4 1 1 0 0 (1),
    tm 3 1 1 1 0 (2),
    tm 2 1 1 1 1 (1),
    tm 1 1 1 2 1 (-1),
    tm 0 1 1 2 2 (-1),
    tm 2 1 2 1 0 (1),
    tm 1 1 2 2 0 (1),
    tm 0 1 2 2 1 (1)]

/-- Chart core 7 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore7 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 5 0 0 0 1 (-1),
    tm 5 1 0 0 0 (1),
    tm 4 1 1 0 0 (2),
    tm 3 1 1 0 1 (-1),
    tm 3 1 1 1 0 (1),
    tm 2 1 1 1 1 (1),
    tm 1 1 1 1 2 (-1),
    tm 3 2 1 0 0 (1),
    tm 2 2 2 0 0 (1),
    tm 1 2 2 1 0 (1),
    tm 0 2 2 1 1 (1)]

/-- Chart core 8 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore8 : Poly :=
  [tm 6 0 0 1 0 (1),
    tm 4 1 0 1 1 (-1),
    tm 4 1 1 1 0 (2),
    tm 5 2 0 0 0 (1),
    tm 3 2 1 1 0 (2),
    tm 2 2 2 1 0 (1),
    tm 1 2 2 2 0 (1),
    tm 0 2 2 2 1 (1)]

/-- Chart core 9 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore9 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 0 0 1 0 (-1),
    tm 8 0 1 2 0 (-1),
    tm 7 0 1 2 1 (-1),
    tm 9 1 0 1 0 (-1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (-2),
    tm 7 1 1 1 1 (1),
    tm 7 1 1 2 0 (-2),
    tm 6 1 1 2 1 (-2),
    tm 6 1 2 2 0 (-2),
    tm 5 1 2 2 1 (-2),
    tm 5 1 2 3 0 (-1),
    tm 4 1 2 3 1 (-2),
    tm 3 1 2 3 2 (-1),
    tm 7 2 1 1 0 (-1),
    tm 6 2 1 2 0 (-1),
    tm 5 2 1 2 1 (-1),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (-1),
    tm 5 2 2 1 1 (1),
    tm 5 2 2 2 0 (-2),
    tm 4 2 2 2 1 (-2),
    tm 4 2 2 3 0 (-2),
    tm 3 2 2 3 1 (-3),
    tm 2 2 2 3 2 (-1),
    tm 4 2 3 2 0 (-1),
    tm 3 2 3 2 1 (-1),
    tm 3 2 3 3 0 (-1),
    tm 2 2 3 3 1 (-2),
    tm 1 2 3 3 2 (-1),
    tm 2 2 3 4 0 (-1),
    tm 1 2 3 4 1 (-2),
    tm 0 2 3 4 2 (-1)]

/-- Chart core 10 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore10 : Poly :=
  [tm 10 0 1 0 0 (1),
    tm 10 1 0 0 0 (-1),
    tm 9 1 1 0 0 (-1),
    tm 8 1 1 1 0 (-2),
    tm 7 1 1 1 1 (-1),
    tm 8 1 2 0 0 (2),
    tm 7 1 2 1 0 (-2),
    tm 6 1 2 2 0 (-1),
    tm 5 1 2 2 1 (-1),
    tm 5 1 3 2 0 (-1),
    tm 4 1 3 2 1 (-1),
    tm 9 2 0 0 0 (-1),
    tm 8 2 1 0 0 (-1),
    tm 7 2 1 1 0 (-2),
    tm 6 2 1 1 1 (-2),
    tm 7 2 2 0 0 (-1),
    tm 6 2 2 1 0 (-2),
    tm 5 2 2 1 1 (-2),
    tm 5 2 2 2 0 (-1),
    tm 4 2 2 2 1 (-3),
    tm 3 2 2 2 2 (-1),
    tm 6 2 3 0 0 (1),
    tm 5 2 3 1 0 (-2),
    tm 4 2 3 2 0 (-1),
    tm 3 2 3 2 1 (-3),
    tm 2 2 3 2 2 (-1),
    tm 2 2 3 3 1 (-1),
    tm 1 2 3 3 2 (-1),
    tm 3 2 4 2 0 (-1),
    tm 2 2 4 2 1 (-1),
    tm 1 2 4 3 1 (-1),
    tm 0 2 4 3 2 (-1)]

/-- Chart core 11 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore11 : Poly :=
  [tm 13 0 0 0 0 (1),
    tm 12 1 0 0 0 (1),
    tm 11 1 1 0 0 (2),
    tm 10 1 1 1 0 (1),
    tm 9 1 1 1 1 (2),
    tm 10 2 1 0 0 (2),
    tm 9 2 1 1 0 (1),
    tm 8 2 1 1 1 (1),
    tm 9 2 2 0 0 (1),
    tm 8 2 2 1 0 (2),
    tm 7 2 2 1 1 (3),
    tm 7 2 2 2 0 (1),
    tm 6 2 2 2 1 (2),
    tm 5 2 2 2 2 (1),
    tm 9 3 1 0 0 (-1),
    tm 8 3 2 0 0 (1),
    tm 5 3 2 2 1 (1),
    tm 6 3 3 1 0 (1),
    tm 5 3 3 1 1 (1),
    tm 5 3 3 2 0 (1),
    tm 4 3 3 2 1 (2),
    tm 3 3 3 2 2 (1),
    tm 3 3 3 3 1 (1),
    tm 2 3 3 3 2 (1),
    tm 7 4 2 0 0 (-1),
    tm 6 4 2 1 0 (1),
    tm 5 4 3 1 0 (-1),
    tm 4 4 3 1 1 (-1),
    tm 4 4 3 2 0 (2),
    tm 3 4 3 2 1 (2),
    tm 2 4 4 3 0 (1),
    tm 1 4 4 3 1 (2),
    tm 0 4 4 3 2 (1)]

/-- Chart core 12 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore12 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 6 0 1 1 0 (1),
    tm 6 1 1 0 0 (1),
    tm 5 1 1 1 0 (-1),
    tm 3 1 1 2 1 (1),
    tm 4 1 2 1 0 (1),
    tm 3 1 2 2 0 (-2),
    tm 2 1 2 2 1 (-1),
    tm 1 1 2 3 1 (1),
    tm 0 1 2 3 2 (1),
    tm 1 1 3 3 0 (-1),
    tm 0 1 3 3 1 (-1)]

/-- Chart core 13 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore13 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 5 0 1 1 1 (1),
    tm 6 1 1 0 0 (2),
    tm 5 1 1 1 0 (-1),
    tm 3 1 2 1 1 (1),
    tm 3 1 2 2 0 (-1),
    tm 2 1 2 2 1 (-1),
    tm 1 1 2 2 2 (1),
    tm 4 2 2 0 0 (1),
    tm 3 2 2 1 0 (-1),
    tm 1 2 3 2 0 (-1),
    tm 0 2 3 2 1 (-1)]

/-- Chart core 14 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore14 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 2 0 1 2 1 (-1),
    tm 4 1 1 0 0 (1),
    tm 3 1 1 1 0 (-1),
    tm 1 1 2 2 0 (-1),
    tm 0 1 2 2 1 (-1)]

/-- Chart core 15 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore15 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 4 1 1 0 0 (1),
    tm 3 1 1 1 0 (-1),
    tm 2 1 1 1 1 (-1),
    tm 1 1 2 2 0 (-1),
    tm 0 1 2 2 1 (-1)]

/-- Chart core 16 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore16 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 6 1 1 0 0 (2),
    tm 4 1 1 1 1 (1),
    tm 5 2 1 0 0 (-1),
    tm 4 2 2 0 0 (1),
    tm 3 2 2 1 0 (-2),
    tm 1 2 3 2 0 (-1),
    tm 0 2 3 2 1 (-1)]

/-- Chart core 17 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore17 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 4 1 1 0 0 (1),
    tm 0 1 2 2 1 (-1)]

/-- Chart core 18 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore18 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 9 0 1 0 0 (1),
    tm 8 0 1 1 0 (1),
    tm 7 0 1 1 1 (1),
    tm 9 1 0 0 0 (1),
    tm 8 1 0 1 0 (-1),
    tm 8 1 1 0 0 (2),
    tm 7 1 1 1 0 (2),
    tm 6 1 1 1 1 (2),
    tm 6 1 1 2 0 (-2),
    tm 5 1 1 2 1 (-1),
    tm 7 1 2 0 0 (2),
    tm 6 1 2 1 0 (2),
    tm 5 1 2 1 1 (3),
    tm 5 1 2 2 0 (1),
    tm 4 1 2 2 1 (2),
    tm 3 1 2 2 2 (1),
    tm 4 1 2 3 0 (-1),
    tm 3 1 2 3 1 (-1),
    tm 7 2 1 0 0 (1),
    tm 5 2 1 1 1 (1),
    tm 6 2 2 0 0 (1),
    tm 5 2 2 1 0 (2),
    tm 4 2 2 1 1 (2),
    tm 3 2 2 2 1 (2),
    tm 2 2 2 2 2 (1),
    tm 5 2 3 0 0 (1),
    tm 4 2 3 1 0 (1),
    tm 3 2 3 1 1 (2),
    tm 3 2 3 2 0 (1),
    tm 2 2 3 2 1 (2),
    tm 1 2 3 2 2 (1),
    tm 1 2 3 3 1 (1),
    tm 0 2 3 3 2 (1)]

/-- Chart core 19 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore19 : Poly :=
  [tm 9 0 1 1 0 (1),
    tm 8 0 2 1 0 (-1),
    tm 7 0 2 2 0 (1),
    tm 10 1 0 0 0 (-1),
    tm 9 1 1 0 0 (-1),
    tm 8 1 1 1 0 (-2),
    tm 7 1 1 1 1 (-1),
    tm 6 1 2 1 1 (-1),
    tm 6 1 2 2 0 (-1),
    tm 6 1 3 1 0 (-2),
    tm 5 1 3 2 0 (1),
    tm 4 1 3 2 1 (-2),
    tm 3 1 3 3 1 (1),
    tm 9 2 0 0 0 (-1),
    tm 8 2 1 0 0 (-1),
    tm 7 2 1 1 0 (-2),
    tm 6 2 1 1 1 (-2),
    tm 7 2 2 0 0 (-1),
    tm 6 2 2 1 0 (-2),
    tm 5 2 2 1 1 (-2),
    tm 5 2 2 2 0 (-1),
    tm 4 2 2 2 1 (-3),
    tm 3 2 2 2 2 (-1),
    tm 5 2 3 1 0 (-1),
    tm 4 2 3 1 1 (-1),
    tm 4 2 3 2 0 (-1),
    tm 3 2 3 2 1 (-2),
    tm 2 2 3 2 2 (-1),
    tm 2 2 3 3 1 (-1),
    tm 1 2 3 3 2 (-1),
    tm 4 2 4 1 0 (-1),
    tm 2 2 4 2 1 (-2),
    tm 0 2 4 3 2 (-1)]

/-- Chart core 20 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore20 : Poly :=
  [tm 13 0 0 0 0 (1),
    tm 12 1 0 0 0 (1),
    tm 11 1 1 0 0 (2),
    tm 10 1 1 1 0 (1),
    tm 9 1 1 1 1 (2),
    tm 10 2 1 0 0 (2),
    tm 9 2 1 1 0 (1),
    tm 8 2 1 1 1 (1),
    tm 9 2 2 0 0 (1),
    tm 8 2 2 1 0 (2),
    tm 7 2 2 1 1 (3),
    tm 7 2 2 2 0 (1),
    tm 6 2 2 2 1 (2),
    tm 5 2 2 2 2 (1),
    tm 8 3 1 1 0 (-1),
    tm 8 3 2 0 0 (1),
    tm 7 3 2 1 0 (2),
    tm 6 3 2 1 1 (1),
    tm 6 3 2 2 0 (-2),
    tm 6 3 3 1 0 (1),
    tm 5 3 3 1 1 (1),
    tm 5 3 3 2 0 (2),
    tm 4 3 3 2 1 (3),
    tm 3 3 3 2 2 (1),
    tm 4 3 3 3 0 (-1),
    tm 2 3 3 3 2 (1),
    tm 5 4 3 1 0 (1),
    tm 3 4 3 2 1 (1),
    tm 3 4 4 2 0 (1),
    tm 2 4 4 2 1 (1),
    tm 1 4 4 3 1 (1),
    tm 0 4 4 3 2 (1)]

/-- Chart core 21 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore21 : Poly :=
  [tm 7 0 0 0 0 (1),
    tm 6 0 1 0 0 (-1),
    tm 5 0 1 1 0 (2),
    tm 4 0 2 1 0 (-1),
    tm 3 0 2 2 0 (1),
    tm 3 1 1 1 1 (1),
    tm 4 1 2 0 0 (-1),
    tm 2 1 2 1 1 (-1),
    tm 1 1 2 2 1 (1),
    tm 0 1 2 2 2 (1),
    tm 2 1 3 1 0 (-1),
    tm 0 1 3 2 1 (-1)]

/-- Chart core 22 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore22 : Poly :=
  [tm 7 0 0 0 0 (1),
    tm 6 0 1 0 0 (-1),
    tm 5 0 1 0 1 (1),
    tm 5 0 1 1 0 (1),
    tm 5 1 1 0 0 (1),
    tm 4 1 2 0 0 (-2),
    tm 3 1 2 0 1 (1),
    tm 3 1 2 1 0 (1),
    tm 2 1 2 1 1 (-1),
    tm 1 1 2 1 2 (1),
    tm 2 2 3 0 0 (-1),
    tm 0 2 3 1 1 (-1)]

/-- Chart core 23 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore23 : Poly :=
  [tm 5 0 0 0 0 (1),
    tm 4 0 1 0 0 (-1),
    tm 3 0 1 1 0 (1),
    tm 2 0 1 1 1 (-1),
    tm 2 1 2 0 0 (-1),
    tm 0 1 2 1 1 (-1)]

/-- Chart core 24 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore24 : Poly :=
  [tm 5 0 0 0 0 (1),
    tm 4 0 1 0 0 (-1),
    tm 3 0 1 1 0 (1),
    tm 2 1 1 0 1 (-1),
    tm 2 1 2 0 0 (-1),
    tm 0 1 2 1 1 (-1)]

/-- Chart core 25 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore25 : Poly :=
  [tm 6 0 1 1 0 (1),
    tm 7 1 0 0 0 (-1),
    tm 5 1 1 1 0 (-2),
    tm 4 1 1 1 1 (-1),
    tm 4 1 2 1 0 (2),
    tm 3 1 2 2 0 (-1),
    tm 2 2 3 1 0 (1),
    tm 0 2 3 2 1 (1)]

/-- Chart core 26 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore26 : Poly :=
  [tm 5 0 0 0 0 (1),
    tm 3 0 1 1 0 (1),
    tm 0 1 2 1 1 (-1)]

/-- Chart core 27 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore27 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 7 0 1 2 1 (-1),
    tm 9 1 0 1 0 (-1),
    tm 9 1 1 0 0 (2),
    tm 7 1 1 1 1 (1),
    tm 7 1 1 2 0 (-2),
    tm 6 1 1 2 1 (-1),
    tm 5 1 2 2 1 (-2),
    tm 5 1 2 3 0 (-1),
    tm 4 1 2 3 1 (-1),
    tm 3 1 2 3 2 (-1),
    tm 7 2 1 1 0 (-1),
    tm 6 2 1 2 0 (-1),
    tm 5 2 1 2 1 (-1),
    tm 7 2 2 0 0 (1),
    tm 5 2 2 1 1 (1),
    tm 5 2 2 2 0 (-2),
    tm 4 2 2 2 1 (-1),
    tm 4 2 2 3 0 (-2),
    tm 3 2 2 3 1 (-3),
    tm 2 2 2 3 2 (-1),
    tm 3 2 3 2 1 (-1),
    tm 3 2 3 3 0 (-1),
    tm 2 2 3 3 1 (-1),
    tm 1 2 3 3 2 (-1),
    tm 2 2 3 4 0 (-1),
    tm 1 2 3 4 1 (-2),
    tm 0 2 3 4 2 (-1)]

/-- Chart core 28 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore28 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 9 0 1 0 0 (1),
    tm 8 0 1 1 0 (1),
    tm 7 0 1 1 1 (1),
    tm 8 1 0 1 0 (-1),
    tm 8 1 1 0 0 (2),
    tm 6 1 1 1 1 (1),
    tm 6 1 1 2 0 (-2),
    tm 5 1 1 2 1 (-1),
    tm 7 1 2 0 0 (2),
    tm 6 1 2 1 0 (2),
    tm 5 1 2 1 1 (3),
    tm 4 1 2 2 1 (1),
    tm 3 1 2 2 2 (1),
    tm 4 1 2 3 0 (-1),
    tm 3 1 2 3 1 (-1),
    tm 5 2 1 1 1 (1),
    tm 6 2 2 0 0 (1),
    tm 4 2 2 1 1 (1),
    tm 3 2 2 2 1 (2),
    tm 2 2 2 2 2 (1),
    tm 5 2 3 0 0 (1),
    tm 4 2 3 1 0 (1),
    tm 3 2 3 1 1 (2),
    tm 2 2 3 2 1 (1),
    tm 1 2 3 2 2 (1),
    tm 1 2 3 3 1 (1),
    tm 0 2 3 3 2 (1)]

/-- Chart core 29 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore29 : Poly :=
  [tm 10 0 1 0 0 (1),
    tm 9 0 1 1 0 (1),
    tm 7 0 2 2 0 (1),
    tm 10 1 0 0 0 (-1),
    tm 9 1 1 0 0 (-1),
    tm 8 1 1 1 0 (-2),
    tm 7 1 1 1 1 (-1),
    tm 8 1 2 0 0 (2),
    tm 6 1 2 2 0 (-1),
    tm 5 1 3 2 0 (1),
    tm 4 1 3 2 1 (-1),
    tm 3 1 3 3 1 (1),
    tm 9 2 0 0 0 (-1),
    tm 8 2 1 0 0 (-1),
    tm 7 2 1 1 0 (-2),
    tm 6 2 1 1 1 (-2),
    tm 7 2 2 0 0 (-1),
    tm 6 2 2 1 0 (-2),
    tm 5 2 2 1 1 (-2),
    tm 5 2 2 2 0 (-1),
    tm 4 2 2 2 1 (-3),
    tm 3 2 2 2 2 (-1),
    tm 6 2 3 0 0 (1),
    tm 5 2 3 1 0 (-1),
    tm 4 2 3 2 0 (-1),
    tm 3 2 3 2 1 (-2),
    tm 2 2 3 2 2 (-1),
    tm 2 2 3 3 1 (-1),
    tm 1 2 3 3 2 (-1),
    tm 2 2 4 2 1 (-1),
    tm 0 2 4 3 2 (-1)]

/-- Chart core 30 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore30 : Poly :=
  [tm 13 0 0 0 0 (1),
    tm 12 1 0 0 0 (1),
    tm 11 1 1 0 0 (2),
    tm 10 1 1 1 0 (1),
    tm 9 1 1 1 1 (2),
    tm 10 2 1 0 0 (2),
    tm 9 2 1 1 0 (1),
    tm 8 2 1 1 1 (1),
    tm 9 2 2 0 0 (1),
    tm 8 2 2 1 0 (2),
    tm 7 2 2 1 1 (3),
    tm 7 2 2 2 0 (1),
    tm 6 2 2 2 1 (2),
    tm 5 2 2 2 2 (1),
    tm 9 3 1 0 0 (-1),
    tm 8 3 1 1 0 (-1),
    tm 8 3 2 0 0 (1),
    tm 6 3 2 2 0 (-2),
    tm 6 3 3 1 0 (1),
    tm 5 3 3 1 1 (1),
    tm 5 3 3 2 0 (1),
    tm 4 3 3 2 1 (2),
    tm 3 3 3 2 2 (1),
    tm 4 3 3 3 0 (-1),
    tm 2 3 3 3 2 (1),
    tm 7 4 2 0 0 (-1),
    tm 5 4 3 1 0 (-1),
    tm 4 4 3 1 1 (-1),
    tm 3 4 3 2 1 (1),
    tm 1 4 4 3 1 (1),
    tm 0 4 4 3 2 (1)]

/-- Chart core 31 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore31 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 7 0 0 1 0 (1),
    tm 6 0 1 1 0 (1),
    tm 5 0 1 2 0 (2),
    tm 3 0 2 3 0 (1),
    tm 6 1 1 0 0 (1),
    tm 3 1 1 2 1 (1),
    tm 4 1 2 1 0 (1),
    tm 2 1 2 2 1 (-1),
    tm 1 1 2 3 1 (1),
    tm 0 1 2 3 2 (1),
    tm 0 1 3 3 1 (-1)]

/-- Chart core 32 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore32 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 7 0 0 1 0 (1),
    tm 5 0 1 1 1 (1),
    tm 5 0 1 2 0 (1),
    tm 6 1 1 0 0 (2),
    tm 5 1 1 1 0 (1),
    tm 3 1 2 1 1 (1),
    tm 3 1 2 2 0 (1),
    tm 2 1 2 2 1 (-1),
    tm 1 1 2 2 2 (1),
    tm 4 2 2 0 0 (1),
    tm 0 2 3 2 1 (-1)]

/-- Chart core 33 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore33 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 5 0 0 1 0 (1),
    tm 3 0 1 2 0 (1),
    tm 2 0 1 2 1 (-1),
    tm 4 1 1 0 0 (1),
    tm 0 1 2 2 1 (-1)]

/-- Chart core 34 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore34 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 5 0 0 1 0 (1),
    tm 3 0 1 2 0 (1),
    tm 4 1 1 0 0 (1),
    tm 2 1 1 1 1 (-1),
    tm 0 1 2 2 1 (-1)]

/-- Chart core 35 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore35 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 7 1 0 0 0 (1),
    tm 6 1 1 0 0 (2),
    tm 5 1 1 1 0 (2),
    tm 4 1 1 1 1 (1),
    tm 3 1 2 2 0 (1),
    tm 4 2 2 0 0 (1),
    tm 0 2 3 2 1 (-1)]

/-- Chart core 36 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore36 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 1 0 0 0 (-1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (-1),
    tm 7 1 1 1 1 (1),
    tm 9 2 0 0 0 (-1),
    tm 8 2 1 0 0 (-2),
    tm 7 2 1 1 0 (-2),
    tm 6 2 1 1 1 (-2),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (-2),
    tm 5 2 2 1 1 (1),
    tm 5 2 2 2 0 (-1),
    tm 4 2 2 2 1 (-2),
    tm 7 3 1 0 0 (-1),
    tm 6 3 1 1 0 (-1),
    tm 5 3 1 1 1 (-1),
    tm 6 3 2 0 0 (-1),
    tm 5 3 2 1 0 (-2),
    tm 4 3 2 1 1 (-2),
    tm 4 3 2 2 0 (-2),
    tm 3 3 2 2 1 (-3),
    tm 2 3 2 2 2 (-1),
    tm 4 3 3 1 0 (-1),
    tm 3 3 3 2 0 (-1),
    tm 2 3 3 2 1 (-2),
    tm 2 3 3 3 0 (-1),
    tm 1 3 3 3 1 (-2),
    tm 0 3 3 3 2 (-1)]

/-- Chart core 37 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore37 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 8 0 0 1 0 (-1),
    tm 8 0 1 0 0 (1),
    tm 7 0 1 1 0 (1),
    tm 6 0 1 1 1 (1),
    tm 6 0 1 2 0 (-1),
    tm 5 0 1 2 1 (-1),
    tm 8 1 0 0 0 (1),
    tm 7 1 1 0 0 (2),
    tm 5 1 1 1 1 (2),
    tm 4 1 1 2 1 (-1),
    tm 6 1 2 0 0 (2),
    tm 5 1 2 1 0 (2),
    tm 4 1 2 1 1 (3),
    tm 4 1 2 2 0 (-1),
    tm 2 1 2 2 2 (1),
    tm 2 1 2 3 1 (-1),
    tm 1 1 2 3 2 (-1),
    tm 6 2 1 0 0 (1),
    tm 5 2 1 1 0 (1),
    tm 4 2 1 1 1 (1),
    tm 5 2 2 0 0 (1),
    tm 4 2 2 1 0 (1),
    tm 3 2 2 1 1 (2),
    tm 3 2 2 2 0 (2),
    tm 2 2 2 2 1 (2),
    tm 1 2 2 2 2 (1),
    tm 4 2 3 0 0 (1),
    tm 3 2 3 1 0 (1),
    tm 2 2 3 1 1 (2),
    tm 1 2 3 2 1 (1),
    tm 0 2 3 2 2 (1),
    tm 1 2 3 3 0 (1),
    tm 0 2 3 3 1 (1)]

/-- Chart core 38 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore38 : Poly :=
  [tm 9 0 1 1 0 (1),
    tm 7 1 2 1 0 (2),
    tm 5 1 2 2 1 (2),
    tm 9 2 0 0 0 (-1),
    tm 8 2 1 0 0 (-1),
    tm 7 2 1 1 0 (-2),
    tm 6 2 1 1 1 (-1),
    tm 6 2 2 1 0 (-2),
    tm 5 2 2 1 1 (-1),
    tm 5 2 2 2 0 (-1),
    tm 4 2 2 2 1 (-1),
    tm 5 2 3 1 0 (1),
    tm 4 2 3 2 0 (-1),
    tm 3 2 3 2 1 (2),
    tm 1 2 3 3 2 (1),
    tm 8 3 0 0 0 (-1),
    tm 7 3 1 0 0 (-1),
    tm 6 3 1 1 0 (-2),
    tm 5 3 1 1 1 (-2),
    tm 6 3 2 0 0 (-1),
    tm 5 3 2 1 0 (-2),
    tm 4 3 2 1 1 (-2),
    tm 4 3 2 2 0 (-1),
    tm 3 3 2 2 1 (-3),
    tm 2 3 2 2 2 (-1),
    tm 4 3 3 1 0 (-2),
    tm 3 3 3 1 1 (-1),
    tm 3 3 3 2 0 (-1),
    tm 2 3 3 2 1 (-3),
    tm 1 3 3 2 2 (-1),
    tm 1 3 3 3 1 (-1),
    tm 0 3 3 3 2 (-1),
    tm 2 3 4 2 0 (-1),
    tm 0 3 4 3 1 (-1)]

/-- Chart core 39 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore39 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 6 0 1 1 0 (1),
    tm 6 1 1 0 0 (1),
    tm 4 1 1 1 1 (1),
    tm 4 1 2 1 0 (1),
    tm 2 1 2 2 1 (1),
    tm 5 2 1 0 0 (-1),
    tm 3 2 1 1 1 (1),
    tm 3 2 2 1 0 (-2),
    tm 1 2 2 2 1 (1),
    tm 0 2 2 2 2 (1),
    tm 1 2 3 2 0 (-1)]

/-- Chart core 40 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore40 : Poly :=
  [tm 7 0 0 0 0 (1),
    tm 5 1 1 0 0 (2),
    tm 4 1 1 0 1 (1),
    tm 3 1 1 1 1 (1),
    tm 4 2 1 0 0 (-1),
    tm 3 2 2 0 0 (1),
    tm 2 2 2 0 1 (1),
    tm 2 2 2 1 0 (-1),
    tm 1 2 2 1 1 (1),
    tm 0 2 2 1 2 (1),
    tm 2 3 2 0 0 (-1),
    tm 0 3 3 1 0 (-1)]

/-- Chart core 41 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore41 : Poly :=
  [tm 5 0 0 0 0 (1),
    tm 3 1 1 0 0 (1),
    tm 2 2 1 0 0 (-1),
    tm 0 2 2 1 0 (-1)]

/-- Chart core 42 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore42 : Poly :=
  [tm 5 0 0 0 0 (1),
    tm 3 1 1 0 0 (1),
    tm 1 1 1 1 1 (1),
    tm 2 2 1 0 0 (-1),
    tm 1 2 1 0 1 (-1),
    tm 0 2 2 1 0 (-1)]

/-- Chart core 43 of the barycentric order chart 43210,
homogenized to degree 3. -/
def chartCore43 : Poly :=
  [tm 1 0 0 1 1 (1),
    tm 2 1 0 0 0 (-1),
    tm 0 1 1 1 0 (-1)]

/-- Chart core 44 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore44 : Poly :=
  [tm 5 0 0 1 0 (1),
    tm 3 1 1 1 0 (2),
    tm 1 1 1 2 1 (1),
    tm 4 2 0 0 0 (-1),
    tm 2 2 1 1 0 (-2),
    tm 1 2 1 1 1 (-1),
    tm 1 2 2 1 0 (1),
    tm 0 2 2 2 0 (-1)]

/-- Chart core 45 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore45 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 9 0 1 0 0 (1),
    tm 8 0 1 1 0 (1),
    tm 7 0 1 1 1 (1),
    tm 8 0 2 0 0 (1),
    tm 7 0 2 1 0 (1),
    tm 6 0 2 1 1 (1),
    tm 8 1 1 0 0 (2),
    tm 7 1 2 0 0 (2),
    tm 6 1 2 1 0 (2),
    tm 5 1 2 1 1 (3),
    tm 4 1 2 2 1 (-1),
    tm 6 1 3 0 0 (2),
    tm 5 1 3 1 0 (2),
    tm 4 1 3 1 1 (3),
    tm 3 1 3 2 1 (1),
    tm 2 1 3 2 2 (1),
    tm 2 1 3 3 1 (-1),
    tm 1 1 3 3 2 (-1),
    tm 6 2 2 0 0 (1),
    tm 5 2 2 1 0 (1),
    tm 4 2 2 1 1 (1),
    tm 5 2 3 0 0 (1),
    tm 4 2 3 1 0 (1),
    tm 3 2 3 1 1 (2),
    tm 3 2 3 2 0 (2),
    tm 2 2 3 2 1 (2),
    tm 1 2 3 2 2 (1),
    tm 4 2 4 0 0 (1),
    tm 3 2 4 1 0 (1),
    tm 2 2 4 1 1 (2),
    tm 1 2 4 2 1 (1),
    tm 0 2 4 2 2 (1),
    tm 1 2 4 3 0 (1),
    tm 0 2 4 3 1 (1)]

/-- Chart core 46 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore46 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 7 1 1 1 1 (1),
    tm 5 1 2 2 1 (-1),
    tm 9 2 0 0 0 (1),
    tm 8 2 1 0 0 (1),
    tm 7 2 1 1 0 (2),
    tm 6 2 1 1 1 (1),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (2),
    tm 5 2 2 2 0 (1),
    tm 4 2 2 2 1 (1),
    tm 4 2 3 2 0 (1),
    tm 3 2 3 2 1 (-1),
    tm 1 2 3 3 2 (-1),
    tm 8 3 0 0 0 (1),
    tm 7 3 1 0 0 (1),
    tm 6 3 1 1 0 (2),
    tm 5 3 1 1 1 (2),
    tm 6 3 2 0 0 (1),
    tm 5 3 2 1 0 (2),
    tm 4 3 2 1 1 (2),
    tm 4 3 2 2 0 (1),
    tm 3 3 2 2 1 (3),
    tm 2 3 2 2 2 (1),
    tm 4 3 3 1 0 (2),
    tm 3 3 3 1 1 (1),
    tm 3 3 3 2 0 (1),
    tm 2 3 3 2 1 (3),
    tm 1 3 3 2 2 (1),
    tm 1 3 3 3 1 (1),
    tm 0 3 3 3 2 (1),
    tm 2 3 4 2 0 (1),
    tm 0 3 4 3 1 (1)]

/-- Chart core 47 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore47 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 8 0 1 1 0 (1),
    tm 8 1 1 0 0 (1),
    tm 6 1 2 1 0 (1),
    tm 4 1 2 2 1 (-1),
    tm 2 1 3 3 1 (-1),
    tm 5 2 2 1 0 (1),
    tm 3 2 2 2 1 (-1),
    tm 3 2 3 2 0 (2),
    tm 1 2 3 3 1 (-1),
    tm 0 2 3 3 2 (-1),
    tm 1 2 4 3 0 (1)]

/-- Chart core 48 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore48 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 7 1 1 0 0 (2),
    tm 4 1 2 1 1 (-1),
    tm 3 1 2 2 1 (-1),
    tm 5 2 2 0 0 (1),
    tm 4 2 2 1 0 (1),
    tm 2 2 3 1 1 (-1),
    tm 2 2 3 2 0 (1),
    tm 1 2 3 2 1 (-1),
    tm 0 2 3 2 2 (-1),
    tm 2 3 3 1 0 (1),
    tm 0 3 4 2 0 (1)]

/-- Chart core 49 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore49 : Poly :=
  [tm 7 0 0 0 0 (1),
    tm 5 1 1 0 0 (1),
    tm 1 1 2 2 1 (-1),
    tm 2 2 2 1 0 (1),
    tm 1 2 2 1 1 (1),
    tm 0 2 3 2 0 (1)]

/-- Chart core 50 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore50 : Poly :=
  [tm 7 0 0 0 0 (1),
    tm 5 1 1 0 0 (2),
    tm 1 1 2 2 1 (-1),
    tm 4 2 1 0 0 (1),
    tm 3 2 2 0 0 (1),
    tm 2 2 2 1 0 (2),
    tm 1 2 2 1 1 (1),
    tm 0 2 3 2 0 (1)]

/-- Chart core 51 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore51 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 7 1 1 1 1 (1),
    tm 9 2 0 0 0 (-1),
    tm 7 2 1 1 0 (-2),
    tm 6 2 1 1 1 (-1),
    tm 7 2 2 0 0 (1),
    tm 5 2 2 1 1 (1),
    tm 5 2 2 2 0 (-1),
    tm 4 2 2 2 1 (-1),
    tm 7 3 1 0 0 (-1),
    tm 6 3 1 1 0 (-1),
    tm 5 3 1 1 1 (-1),
    tm 5 3 2 1 0 (-2),
    tm 4 3 2 1 1 (-1),
    tm 4 3 2 2 0 (-2),
    tm 3 3 2 2 1 (-3),
    tm 2 3 2 2 2 (-1),
    tm 3 3 3 2 0 (-1),
    tm 2 3 3 2 1 (-1),
    tm 2 3 3 3 0 (-1),
    tm 1 3 3 3 1 (-2),
    tm 0 3 3 3 2 (-1)]

/-- Chart core 52 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore52 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 8 0 0 1 0 (-1),
    tm 8 0 1 0 0 (1),
    tm 7 0 1 1 0 (1),
    tm 6 0 1 1 1 (1),
    tm 6 0 1 2 0 (-1),
    tm 5 0 1 2 1 (-1),
    tm 8 1 0 0 0 (1),
    tm 7 1 0 1 0 (-1),
    tm 7 1 1 0 0 (2),
    tm 5 1 1 1 1 (2),
    tm 5 1 1 2 0 (-2),
    tm 4 1 1 2 1 (-2),
    tm 6 1 2 0 0 (2),
    tm 5 1 2 1 0 (2),
    tm 4 1 2 1 1 (3),
    tm 4 1 2 2 0 (-1),
    tm 2 1 2 2 2 (1),
    tm 3 1 2 3 0 (-1),
    tm 2 1 2 3 1 (-2),
    tm 1 1 2 3 2 (-1),
    tm 6 2 1 0 0 (1),
    tm 4 2 1 1 1 (1),
    tm 5 2 2 0 0 (1),
    tm 4 2 2 1 0 (1),
    tm 3 2 2 1 1 (2),
    tm 2 2 2 2 1 (1),
    tm 1 2 2 2 2 (1),
    tm 4 2 3 0 0 (1),
    tm 3 2 3 1 0 (1),
    tm 2 2 3 1 1 (2),
    tm 1 2 3 2 1 (1),
    tm 0 2 3 2 2 (1)]

/-- Chart core 53 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore53 : Poly :=
  [tm 9 0 1 1 0 (1),
    tm 8 1 1 1 0 (1),
    tm 7 1 2 1 0 (2),
    tm 6 1 2 2 0 (1),
    tm 5 1 2 2 1 (2),
    tm 9 2 0 0 0 (-1),
    tm 8 2 1 0 0 (-1),
    tm 7 2 1 1 0 (-2),
    tm 6 2 1 1 1 (-1),
    tm 5 2 2 1 1 (-1),
    tm 5 2 2 2 0 (-1),
    tm 5 2 3 1 0 (1),
    tm 4 2 3 2 0 (1),
    tm 3 2 3 2 1 (2),
    tm 2 2 3 3 1 (1),
    tm 1 2 3 3 2 (1),
    tm 8 3 0 0 0 (-1),
    tm 7 3 1 0 0 (-1),
    tm 6 3 1 1 0 (-2),
    tm 5 3 1 1 1 (-2),
    tm 6 3 2 0 0 (-1),
    tm 5 3 2 1 0 (-2),
    tm 4 3 2 1 1 (-2),
    tm 4 3 2 2 0 (-1),
    tm 3 3 2 2 1 (-3),
    tm 2 3 2 2 2 (-1),
    tm 4 3 3 1 0 (-1),
    tm 3 3 3 1 1 (-1),
    tm 3 3 3 2 0 (-1),
    tm 2 3 3 2 1 (-2),
    tm 1 3 3 2 2 (-1),
    tm 1 3 3 3 1 (-1),
    tm 0 3 3 3 2 (-1)]

/-- Chart core 54 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore54 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 9 1 0 0 0 (1),
    tm 8 1 1 0 0 (2),
    tm 7 1 1 1 0 (1),
    tm 6 1 1 1 1 (2),
    tm 7 2 1 0 0 (2),
    tm 5 2 1 1 1 (1),
    tm 6 2 2 0 0 (1),
    tm 5 2 2 1 0 (2),
    tm 4 2 2 1 1 (3),
    tm 3 2 2 2 1 (1),
    tm 2 2 2 2 2 (1),
    tm 5 3 1 1 0 (-1),
    tm 5 3 2 0 0 (1),
    tm 3 3 2 1 1 (1),
    tm 3 3 2 2 0 (-2),
    tm 2 3 2 2 1 (-1),
    tm 3 3 3 1 0 (1),
    tm 2 3 3 1 1 (1),
    tm 1 3 3 2 1 (1),
    tm 0 3 3 2 2 (1),
    tm 1 3 3 3 0 (-1),
    tm 0 3 3 3 1 (-1)]

/-- Chart core 55 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore55 : Poly :=
  [tm 4 0 0 0 0 (1),
    tm 3 1 0 0 0 (1),
    tm 2 1 1 0 0 (1),
    tm 1 1 1 1 0 (1),
    tm 0 1 1 1 1 (1),
    tm 0 2 1 0 1 (-1)]

/-- Chart core 56 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore56 : Poly :=
  [tm 4 0 1 1 0 (1),
    tm 5 1 0 0 0 (1),
    tm 3 1 1 1 0 (2),
    tm 2 1 2 1 0 (2),
    tm 1 1 2 2 0 (1),
    tm 0 1 2 2 1 (1),
    tm 0 2 2 1 1 (-1),
    tm 0 2 3 1 0 (1)]

/-- Chart core 57 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore57 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 9 0 1 0 0 (1),
    tm 8 0 1 1 0 (1),
    tm 7 0 1 1 1 (1),
    tm 8 0 2 0 0 (1),
    tm 7 0 2 1 0 (1),
    tm 6 0 2 1 1 (1),
    tm 8 1 1 0 0 (2),
    tm 7 1 1 1 0 (-1),
    tm 7 1 2 0 0 (2),
    tm 6 1 2 1 0 (2),
    tm 5 1 2 1 1 (3),
    tm 5 1 2 2 0 (-2),
    tm 4 1 2 2 1 (-2),
    tm 6 1 3 0 0 (2),
    tm 5 1 3 1 0 (2),
    tm 4 1 3 1 1 (3),
    tm 3 1 3 2 1 (1),
    tm 2 1 3 2 2 (1),
    tm 3 1 3 3 0 (-1),
    tm 2 1 3 3 1 (-2),
    tm 1 1 3 3 2 (-1),
    tm 6 2 2 0 0 (1),
    tm 4 2 2 1 1 (1),
    tm 5 2 3 0 0 (1),
    tm 4 2 3 1 0 (1),
    tm 3 2 3 1 1 (2),
    tm 2 2 3 2 1 (1),
    tm 1 2 3 2 2 (1),
    tm 4 2 4 0 0 (1),
    tm 3 2 4 1 0 (1),
    tm 2 2 4 1 1 (2),
    tm 1 2 4 2 1 (1),
    tm 0 2 4 2 2 (1)]

/-- Chart core 58 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore58 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (-1),
    tm 7 1 1 1 1 (1),
    tm 6 1 2 2 0 (-1),
    tm 5 1 2 2 1 (-1),
    tm 9 2 0 0 0 (1),
    tm 8 2 1 0 0 (1),
    tm 7 2 1 1 0 (2),
    tm 6 2 1 1 1 (1),
    tm 7 2 2 0 0 (1),
    tm 5 2 2 1 1 (2),
    tm 5 2 2 2 0 (1),
    tm 4 2 3 2 0 (-1),
    tm 3 2 3 2 1 (-1),
    tm 2 2 3 3 1 (-1),
    tm 1 2 3 3 2 (-1),
    tm 8 3 0 0 0 (1),
    tm 7 3 1 0 0 (1),
    tm 6 3 1 1 0 (2),
    tm 5 3 1 1 1 (2),
    tm 6 3 2 0 0 (1),
    tm 5 3 2 1 0 (2),
    tm 4 3 2 1 1 (2),
    tm 4 3 2 2 0 (1),
    tm 3 3 2 2 1 (3),
    tm 2 3 2 2 2 (1),
    tm 4 3 3 1 0 (1),
    tm 3 3 3 1 1 (1),
    tm 3 3 3 2 0 (1),
    tm 2 3 3 2 1 (2),
    tm 1 3 3 2 2 (1),
    tm 1 3 3 3 1 (1),
    tm 0 3 3 3 2 (1)]

/-- Chart core 59 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore59 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 9 1 0 0 0 (1),
    tm 8 1 1 0 0 (2),
    tm 7 1 1 1 0 (1),
    tm 6 1 1 1 1 (2),
    tm 8 2 0 0 0 (1),
    tm 7 2 1 0 0 (2),
    tm 6 2 1 1 0 (2),
    tm 5 2 1 1 1 (2),
    tm 6 2 2 0 0 (1),
    tm 5 2 2 1 0 (2),
    tm 4 2 2 1 1 (3),
    tm 4 2 2 2 0 (1),
    tm 3 2 2 2 1 (2),
    tm 2 2 2 2 2 (1),
    tm 6 3 1 0 0 (1),
    tm 5 3 1 1 0 (-1),
    tm 5 3 2 0 0 (1),
    tm 4 3 2 1 0 (2),
    tm 3 3 2 1 1 (2),
    tm 3 3 2 2 0 (-2),
    tm 2 3 2 2 1 (-1),
    tm 3 3 3 1 0 (1),
    tm 2 3 3 1 1 (1),
    tm 2 3 3 2 0 (1),
    tm 1 3 3 2 1 (2),
    tm 0 3 3 2 2 (1),
    tm 1 3 3 3 0 (-1),
    tm 0 3 3 3 1 (-1)]

/-- Chart core 60 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore60 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 8 0 1 1 0 (1),
    tm 8 1 1 0 0 (1),
    tm 7 1 1 1 0 (-1),
    tm 6 1 2 1 0 (1),
    tm 5 1 2 2 0 (-2),
    tm 4 1 2 2 1 (-1),
    tm 3 1 3 3 0 (-1),
    tm 2 1 3 3 1 (-1),
    tm 3 2 2 2 1 (-1),
    tm 1 2 3 3 1 (-1),
    tm 0 2 3 3 2 (-1)]

/-- Chart core 61 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore61 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 7 1 1 0 0 (2),
    tm 6 1 1 1 0 (-1),
    tm 4 1 2 1 1 (-1),
    tm 4 1 2 2 0 (-1),
    tm 3 1 2 2 1 (-1),
    tm 5 2 2 0 0 (1),
    tm 4 2 2 1 0 (-1),
    tm 2 2 3 1 1 (-1),
    tm 2 2 3 2 0 (-1),
    tm 1 2 3 2 1 (-1),
    tm 0 2 3 2 2 (-1)]

/-- Chart core 62 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore62 : Poly :=
  [tm 5 0 0 0 0 (1),
    tm 3 1 1 0 0 (1),
    tm 2 1 1 1 0 (-1),
    tm 0 1 2 2 0 (-1)]

/-- Chart core 63 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore63 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 4 1 1 0 0 (1),
    tm 3 1 1 1 0 (-1),
    tm 1 1 2 2 0 (-1),
    tm 0 1 2 2 1 (-1),
    tm 0 2 2 1 1 (1)]

/-- Chart core 64 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore64 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 5 1 0 0 0 (-1),
    tm 4 1 1 0 0 (2),
    tm 3 1 1 1 0 (-2),
    tm 1 1 2 2 0 (-1),
    tm 0 1 2 2 1 (-1),
    tm 2 2 2 0 0 (1),
    tm 0 2 2 1 1 (1)]

/-- Chart core 65 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore65 : Poly :=
  [tm 5 0 0 0 0 (1),
    tm 3 0 0 1 1 (-1),
    tm 3 0 1 1 0 (2),
    tm 1 0 1 2 1 (-1),
    tm 0 0 1 2 2 (-1),
    tm 1 0 2 2 0 (1)]

/-- Chart core 66 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore66 : Poly :=
  [tm 4 0 0 0 1 (1),
    tm 4 1 0 0 0 (-1),
    tm 2 1 1 0 1 (1),
    tm 2 1 1 1 0 (-1),
    tm 0 1 1 1 2 (1),
    tm 2 2 1 0 0 (-1),
    tm 0 2 2 1 0 (-1)]

/-- Chart core 67 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore67 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 8 0 1 0 0 (1),
    tm 7 0 1 1 0 (1),
    tm 6 0 1 1 1 (1),
    tm 8 1 0 0 0 (1),
    tm 7 1 0 1 0 (-1),
    tm 7 1 1 0 0 (2),
    tm 6 1 1 1 0 (1),
    tm 5 1 1 1 1 (2),
    tm 5 1 1 2 0 (-2),
    tm 4 1 1 2 1 (-1),
    tm 6 1 2 0 0 (2),
    tm 5 1 2 1 0 (2),
    tm 4 1 2 1 1 (3),
    tm 3 1 2 2 1 (1),
    tm 2 1 2 2 2 (1),
    tm 3 1 2 3 0 (-1),
    tm 2 1 2 3 1 (-1),
    tm 6 2 1 0 0 (1),
    tm 4 2 1 1 1 (1),
    tm 5 2 2 0 0 (1),
    tm 4 2 2 1 0 (1),
    tm 3 2 2 1 1 (2),
    tm 2 2 2 2 1 (1),
    tm 1 2 2 2 2 (1),
    tm 4 2 3 0 0 (1),
    tm 3 2 3 1 0 (1),
    tm 2 2 3 1 1 (2),
    tm 1 2 3 2 1 (1),
    tm 0 2 3 2 2 (1)]

/-- Chart core 68 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore68 : Poly :=
  [tm 8 0 1 1 0 (1),
    tm 6 0 2 2 0 (1),
    tm 9 1 0 0 0 (-1),
    tm 8 1 1 0 0 (-1),
    tm 7 1 1 1 0 (-2),
    tm 6 1 1 1 1 (-1),
    tm 5 1 2 1 1 (-1),
    tm 5 1 2 2 0 (-1),
    tm 4 1 3 2 0 (1),
    tm 2 1 3 3 1 (1),
    tm 8 2 0 0 0 (-1),
    tm 7 2 1 0 0 (-1),
    tm 6 2 1 1 0 (-2),
    tm 5 2 1 1 1 (-2),
    tm 6 2 2 0 0 (-1),
    tm 5 2 2 1 0 (-2),
    tm 4 2 2 1 1 (-2),
    tm 4 2 2 2 0 (-1),
    tm 3 2 2 2 1 (-3),
    tm 2 2 2 2 2 (-1),
    tm 4 2 3 1 0 (-1),
    tm 3 2 3 1 1 (-1),
    tm 3 2 3 2 0 (-1),
    tm 2 2 3 2 1 (-2),
    tm 1 2 3 2 2 (-1),
    tm 1 2 3 3 1 (-1),
    tm 0 2 3 3 2 (-1)]

/-- Chart core 69 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore69 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 1 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (1),
    tm 7 1 1 1 1 (2),
    tm 8 2 1 0 0 (2),
    tm 7 2 1 1 0 (1),
    tm 6 2 1 1 1 (1),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (3),
    tm 5 2 2 2 0 (1),
    tm 4 2 2 2 1 (2),
    tm 3 2 2 2 2 (1),
    tm 6 3 1 1 0 (-1),
    tm 6 3 2 0 0 (1),
    tm 5 3 2 1 0 (1),
    tm 4 3 2 1 1 (1),
    tm 4 3 2 2 0 (-2),
    tm 4 3 3 1 0 (1),
    tm 3 3 3 1 1 (1),
    tm 3 3 3 2 0 (1),
    tm 2 3 3 2 1 (2),
    tm 1 3 3 2 2 (1),
    tm 2 3 3 3 0 (-1),
    tm 0 3 3 3 2 (1)]

/-- Chart core 70 of the barycentric order chart 43210,
homogenized to degree 3. -/
def chartCore70 : Poly :=
  [tm 3 0 0 0 0 (1),
    tm 1 0 1 1 0 (1),
    tm 0 0 1 1 1 (-1)]

/-- Chart core 71 of the barycentric order chart 43210,
homogenized to degree 3. -/
def chartCore71 : Poly :=
  [tm 3 0 0 0 0 (1),
    tm 1 0 1 1 0 (1),
    tm 0 1 1 0 1 (-1)]

/-- Chart core 72 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore72 : Poly :=
  [tm 10 0 0 1 0 (1),
    tm 9 0 1 1 0 (1),
    tm 8 0 1 2 0 (1),
    tm 7 0 1 2 1 (1),
    tm 10 1 0 0 0 (-1),
    tm 9 1 0 1 0 (1),
    tm 7 1 1 1 1 (-1),
    tm 7 1 1 2 0 (2),
    tm 6 1 1 2 1 (2),
    tm 7 1 2 1 0 (2),
    tm 6 1 2 2 0 (1),
    tm 5 1 2 2 1 (2),
    tm 5 1 2 3 0 (1),
    tm 4 1 2 3 1 (2),
    tm 3 1 2 3 2 (1),
    tm 8 2 1 0 0 (-1),
    tm 7 2 1 1 0 (1),
    tm 6 2 1 1 1 (-1),
    tm 6 2 1 2 0 (1),
    tm 5 2 1 2 1 (1),
    tm 6 2 2 1 0 (-1),
    tm 5 2 2 1 1 (-1),
    tm 5 2 2 2 0 (2),
    tm 3 2 2 2 2 (-1),
    tm 4 2 2 3 0 (2),
    tm 3 2 2 3 1 (3),
    tm 2 2 2 3 2 (1),
    tm 5 2 3 1 0 (1),
    tm 3 2 3 2 1 (1),
    tm 3 2 3 3 0 (1),
    tm 2 2 3 3 1 (1),
    tm 2 2 3 4 0 (1),
    tm 1 2 3 4 1 (2),
    tm 0 2 3 4 2 (1)]

/-- Chart core 73 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore73 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 8 0 1 0 0 (1),
    tm 7 0 1 1 0 (1),
    tm 6 0 1 1 1 (1),
    tm 8 1 0 0 0 (1),
    tm 7 1 1 0 0 (2),
    tm 6 1 1 1 0 (2),
    tm 5 1 1 1 1 (2),
    tm 6 1 2 0 0 (2),
    tm 5 1 2 1 0 (2),
    tm 4 1 2 1 1 (3),
    tm 4 1 2 2 0 (1),
    tm 3 1 2 2 1 (2),
    tm 2 1 2 2 2 (1),
    tm 7 2 0 0 0 (-1),
    tm 6 2 1 0 0 (1),
    tm 5 2 1 1 0 (-2),
    tm 4 2 1 1 1 (-1),
    tm 5 2 2 0 0 (1),
    tm 4 2 2 1 0 (2),
    tm 3 2 2 1 1 (2),
    tm 3 2 2 2 0 (-1),
    tm 2 2 2 2 1 (-1),
    tm 4 2 3 0 0 (1),
    tm 3 2 3 1 0 (1),
    tm 2 2 3 1 1 (2),
    tm 2 2 3 2 0 (1),
    tm 1 2 3 2 1 (2),
    tm 0 2 3 2 2 (1)]

/-- Chart core 74 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore74 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 1 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (1),
    tm 7 1 1 1 1 (2),
    tm 8 2 1 0 0 (2),
    tm 7 2 1 1 0 (1),
    tm 6 2 1 1 1 (1),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (3),
    tm 5 2 2 2 0 (1),
    tm 4 2 2 2 1 (2),
    tm 3 2 2 2 2 (1),
    tm 6 3 2 0 0 (1),
    tm 5 3 2 1 0 (2),
    tm 4 3 2 1 1 (1),
    tm 3 3 2 2 1 (1),
    tm 4 3 3 1 0 (1),
    tm 3 3 3 1 1 (1),
    tm 3 3 3 2 0 (2),
    tm 2 3 3 2 1 (3),
    tm 1 3 3 2 2 (1),
    tm 1 3 3 3 1 (1),
    tm 0 3 3 3 2 (1),
    tm 6 4 1 0 0 (-1),
    tm 4 4 2 1 0 (-2),
    tm 3 4 2 1 1 (-2),
    tm 3 4 3 1 0 (1),
    tm 2 4 3 2 0 (-1),
    tm 1 4 3 2 1 (-2),
    tm 0 4 3 2 2 (-1),
    tm 1 4 4 2 0 (1),
    tm 0 4 4 2 1 (1)]

/-- Chart core 75 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore75 : Poly :=
  [tm 6 0 1 1 0 (1),
    tm 4 0 2 2 0 (1),
    tm 7 1 0 0 0 (-1),
    tm 5 1 1 1 0 (-2),
    tm 4 1 1 1 1 (-1),
    tm 3 1 1 2 1 (-1),
    tm 4 1 2 1 0 (1),
    tm 3 1 2 2 0 (-1),
    tm 2 1 2 2 1 (-1),
    tm 1 1 2 3 1 (-1),
    tm 0 1 2 3 2 (-1),
    tm 2 1 3 2 0 (1)]

/-- Chart core 76 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore76 : Poly :=
  [tm 5 0 1 1 0 (1),
    tm 4 0 1 1 1 (-1),
    tm 6 1 0 0 0 (-1),
    tm 4 1 1 1 0 (-1),
    tm 3 1 1 1 1 (-1),
    tm 3 1 2 1 0 (2),
    tm 2 1 2 1 1 (-1),
    tm 0 1 2 2 2 (-1),
    tm 4 2 1 0 0 (-1),
    tm 2 2 2 1 0 (-1),
    tm 1 2 2 1 1 (-1),
    tm 1 2 3 1 0 (1)]

/-- Chart core 77 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore77 : Poly :=
  [tm 2 0 1 1 0 (1),
    tm 0 0 1 2 1 (1),
    tm 3 1 0 0 0 (-1),
    tm 1 1 1 1 0 (-1),
    tm 0 1 1 1 1 (-1),
    tm 0 1 2 1 0 (1)]

/-- Chart core 78 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore78 : Poly :=
  [tm 2 0 1 1 0 (1),
    tm 3 1 0 0 0 (-1),
    tm 1 1 1 1 0 (-1),
    tm 0 1 2 1 0 (1)]

/-- Chart core 79 of the barycentric order chart 43210,
homogenized to degree 2. -/
def chartCore79 : Poly :=
  [tm 2 0 0 0 0 (1),
    tm 0 1 0 0 1 (-1),
    tm 0 1 1 0 0 (1)]

/-- Chart core 80 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore80 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 0 0 1 0 (-1),
    tm 8 0 1 2 0 (-1),
    tm 7 0 1 2 1 (-1),
    tm 10 1 0 0 0 (1),
    tm 9 1 0 1 0 (-1),
    tm 9 1 1 0 0 (2),
    tm 7 1 1 1 1 (2),
    tm 7 1 1 2 0 (-2),
    tm 6 1 1 2 1 (-2),
    tm 6 1 2 2 0 (-1),
    tm 5 1 2 2 1 (-1),
    tm 5 1 2 3 0 (-1),
    tm 4 1 2 3 1 (-2),
    tm 3 1 2 3 2 (-1),
    tm 8 2 1 0 0 (1),
    tm 7 2 1 1 0 (-1),
    tm 6 2 1 1 1 (1),
    tm 6 2 1 2 0 (-1),
    tm 5 2 1 2 1 (-1),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (1),
    tm 5 2 2 1 1 (2),
    tm 5 2 2 2 0 (-2),
    tm 3 2 2 2 2 (1),
    tm 4 2 2 3 0 (-2),
    tm 3 2 2 3 1 (-3),
    tm 2 2 2 3 2 (-1),
    tm 3 2 3 3 0 (-1),
    tm 2 2 3 3 1 (-1),
    tm 2 2 3 4 0 (-1),
    tm 1 2 3 4 1 (-2),
    tm 0 2 3 4 2 (-1)]

/-- Chart core 81 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore81 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 8 0 1 0 0 (1),
    tm 7 0 1 1 0 (1),
    tm 6 0 1 1 1 (1),
    tm 7 1 1 0 0 (2),
    tm 5 1 1 1 1 (1),
    tm 6 1 2 0 0 (2),
    tm 5 1 2 1 0 (2),
    tm 4 1 2 1 1 (3),
    tm 3 1 2 2 1 (1),
    tm 2 1 2 2 2 (1),
    tm 7 2 0 0 0 (-1),
    tm 5 2 1 1 0 (-2),
    tm 4 2 1 1 1 (-1),
    tm 5 2 2 0 0 (1),
    tm 3 2 2 1 1 (1),
    tm 3 2 2 2 0 (-1),
    tm 2 2 2 2 1 (-1),
    tm 4 2 3 0 0 (1),
    tm 3 2 3 1 0 (1),
    tm 2 2 3 1 1 (2),
    tm 1 2 3 2 1 (1),
    tm 0 2 3 2 2 (1)]

/-- Chart core 82 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore82 : Poly :=
  [tm 9 0 1 0 0 (1),
    tm 9 1 0 0 0 (-1),
    tm 7 1 1 1 0 (-2),
    tm 6 1 1 1 1 (-1),
    tm 7 1 2 0 0 (2),
    tm 5 1 2 1 1 (1),
    tm 5 1 2 2 0 (-1),
    tm 4 1 2 2 1 (-1),
    tm 8 2 0 0 0 (-1),
    tm 7 2 1 0 0 (-1),
    tm 6 2 1 1 0 (-2),
    tm 5 2 1 1 1 (-2),
    tm 5 2 2 1 0 (-2),
    tm 4 2 2 1 1 (-1),
    tm 4 2 2 2 0 (-1),
    tm 3 2 2 2 1 (-3),
    tm 2 2 2 2 2 (-1),
    tm 5 2 3 0 0 (1),
    tm 3 2 3 1 1 (1),
    tm 3 2 3 2 0 (-1),
    tm 2 2 3 2 1 (-1),
    tm 1 2 3 3 1 (-1),
    tm 0 2 3 3 2 (-1)]

/-- Chart core 83 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore83 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 1 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (1),
    tm 7 1 1 1 1 (2),
    tm 8 2 1 0 0 (2),
    tm 7 2 1 1 0 (1),
    tm 6 2 1 1 1 (1),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (3),
    tm 5 2 2 2 0 (1),
    tm 4 2 2 2 1 (2),
    tm 3 2 2 2 2 (1),
    tm 7 3 1 0 0 (-1),
    tm 6 3 2 0 0 (1),
    tm 3 3 2 2 1 (1),
    tm 4 3 3 1 0 (1),
    tm 3 3 3 1 1 (1),
    tm 3 3 3 2 0 (1),
    tm 2 3 3 2 1 (2),
    tm 1 3 3 2 2 (1),
    tm 1 3 3 3 1 (1),
    tm 0 3 3 3 2 (1),
    tm 6 4 1 0 0 (-1),
    tm 5 4 2 0 0 (-1),
    tm 4 4 2 1 0 (-2),
    tm 3 4 2 1 1 (-2),
    tm 3 4 3 1 0 (-1),
    tm 2 4 3 1 1 (-1),
    tm 2 4 3 2 0 (-1),
    tm 1 4 3 2 1 (-2),
    tm 0 4 3 2 2 (-1)]

/-- Chart core 84 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore84 : Poly :=
  [tm 4 0 0 0 0 (1),
    tm 0 0 1 2 1 (-1),
    tm 3 1 0 0 0 (1),
    tm 2 1 1 0 0 (1),
    tm 1 1 1 1 0 (1),
    tm 0 1 1 1 1 (1)]

/-- Chart core 85 of the barycentric order chart 43210,
homogenized to degree 12. -/
def chartCore85 : Poly :=
  [tm 12 0 0 0 0 (1),
    tm 10 0 1 1 0 (2),
    tm 9 0 2 1 0 (1),
    tm 8 0 2 2 0 (1),
    tm 7 0 2 2 1 (1),
    tm 10 1 1 0 0 (1),
    tm 9 1 1 1 0 (1),
    tm 8 1 1 1 1 (1),
    tm 8 1 2 1 0 (2),
    tm 7 1 2 1 1 (-1),
    tm 7 1 2 2 0 (2),
    tm 6 1 2 2 1 (3),
    tm 7 1 3 1 0 (2),
    tm 6 1 3 2 0 (1),
    tm 5 1 3 2 1 (2),
    tm 5 1 3 3 0 (1),
    tm 4 1 3 3 1 (2),
    tm 3 1 3 3 2 (1),
    tm 7 2 2 1 0 (1),
    tm 6 2 2 2 0 (1),
    tm 5 2 2 2 1 (1),
    tm 5 2 3 1 1 (-1),
    tm 5 2 3 2 0 (2),
    tm 4 2 3 2 1 (1),
    tm 3 2 3 2 2 (-1),
    tm 4 2 3 3 0 (2),
    tm 3 2 3 3 1 (3),
    tm 2 2 3 3 2 (1),
    tm 5 2 4 1 0 (1),
    tm 3 2 4 2 1 (1),
    tm 3 2 4 3 0 (1),
    tm 2 2 4 3 1 (1),
    tm 2 2 4 4 0 (1),
    tm 1 2 4 4 1 (2),
    tm 0 2 4 4 2 (1)]

/-- Chart core 86 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore86 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 1 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (1),
    tm 7 1 1 1 1 (2),
    tm 8 2 1 0 0 (2),
    tm 7 2 1 1 0 (1),
    tm 6 2 1 1 1 (1),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (3),
    tm 5 2 2 2 0 (1),
    tm 4 2 2 2 1 (2),
    tm 3 2 2 2 2 (1),
    tm 8 3 0 0 0 (1),
    tm 6 3 1 1 0 (2),
    tm 5 3 1 1 1 (1),
    tm 6 3 2 0 0 (1),
    tm 5 3 2 1 0 (2),
    tm 4 3 2 1 1 (1),
    tm 4 3 2 2 0 (1),
    tm 3 3 2 2 1 (2),
    tm 4 3 3 1 0 (1),
    tm 3 3 3 1 1 (1),
    tm 3 3 3 2 0 (2),
    tm 2 3 3 2 1 (3),
    tm 1 3 3 2 2 (1),
    tm 1 3 3 3 1 (1),
    tm 0 3 3 3 2 (1),
    tm 3 4 2 1 1 (-1),
    tm 3 4 3 1 0 (1),
    tm 1 4 3 2 1 (-1),
    tm 0 4 3 2 2 (-1),
    tm 1 4 4 2 0 (1),
    tm 0 4 4 2 1 (1)]

/-- Chart core 87 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore87 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 7 0 1 1 0 (2),
    tm 6 0 2 1 0 (1),
    tm 5 0 2 2 0 (1),
    tm 4 0 3 2 0 (1),
    tm 4 1 2 1 1 (-1),
    tm 3 1 2 2 1 (-1),
    tm 4 1 3 1 0 (1),
    tm 2 1 3 2 1 (-1),
    tm 1 1 3 3 1 (-1),
    tm 0 1 3 3 2 (-1),
    tm 2 1 4 2 0 (1)]

/-- Chart core 88 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore88 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 6 0 1 1 0 (1),
    tm 5 0 2 1 0 (1),
    tm 4 0 2 1 1 (-1),
    tm 6 1 1 0 0 (1),
    tm 4 1 2 1 0 (1),
    tm 3 1 2 1 1 (-1),
    tm 3 1 3 1 0 (2),
    tm 2 1 3 1 1 (-1),
    tm 0 1 3 2 2 (-1),
    tm 1 2 3 1 1 (-1),
    tm 1 2 4 1 0 (1)]

/-- Chart core 89 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore89 : Poly :=
  [tm 5 0 0 0 0 (1),
    tm 3 0 1 1 0 (1),
    tm 2 0 2 1 0 (1),
    tm 0 0 2 2 1 (1),
    tm 0 1 2 1 1 (-1),
    tm 0 1 3 1 0 (1)]

/-- Chart core 90 of the barycentric order chart 43210,
homogenized to degree 12. -/
def chartCore90 : Poly :=
  [tm 12 0 0 0 0 (1),
    tm 11 0 1 0 0 (-1),
    tm 10 0 1 1 0 (2),
    tm 8 0 2 2 0 (1),
    tm 7 0 2 2 1 (1),
    tm 10 1 1 0 0 (1),
    tm 9 1 1 1 0 (1),
    tm 8 1 1 1 1 (1),
    tm 9 1 2 0 0 (-2),
    tm 8 1 2 1 0 (2),
    tm 7 1 2 1 1 (-2),
    tm 7 1 2 2 0 (2),
    tm 6 1 2 2 1 (3),
    tm 6 1 3 2 0 (1),
    tm 5 1 3 2 1 (1),
    tm 5 1 3 3 0 (1),
    tm 4 1 3 3 1 (2),
    tm 3 1 3 3 2 (1),
    tm 7 2 2 1 0 (1),
    tm 6 2 2 2 0 (1),
    tm 5 2 2 2 1 (1),
    tm 7 2 3 0 0 (-1),
    tm 5 2 3 1 1 (-2),
    tm 5 2 3 2 0 (2),
    tm 4 2 3 2 1 (1),
    tm 3 2 3 2 2 (-1),
    tm 4 2 3 3 0 (2),
    tm 3 2 3 3 1 (3),
    tm 2 2 3 3 2 (1),
    tm 3 2 4 3 0 (1),
    tm 2 2 4 3 1 (1),
    tm 2 2 4 4 0 (1),
    tm 1 2 4 4 1 (2),
    tm 0 2 4 4 2 (1)]

/-- Chart core 91 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore91 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 9 0 1 0 0 (-1),
    tm 8 0 1 1 0 (1),
    tm 9 1 0 0 0 (1),
    tm 8 1 1 0 0 (2),
    tm 7 1 1 1 0 (2),
    tm 6 1 1 1 1 (2),
    tm 7 1 2 0 0 (-2),
    tm 6 1 2 1 0 (2),
    tm 5 1 2 1 1 (-1),
    tm 5 1 2 2 0 (1),
    tm 4 1 2 2 1 (2),
    tm 8 2 0 0 0 (1),
    tm 7 2 1 0 0 (1),
    tm 6 2 1 1 0 (2),
    tm 5 2 1 1 1 (2),
    tm 6 2 2 0 0 (1),
    tm 5 2 2 1 0 (2),
    tm 4 2 2 1 1 (2),
    tm 4 2 2 2 0 (1),
    tm 3 2 2 2 1 (3),
    tm 2 2 2 2 2 (1),
    tm 5 2 3 0 0 (-1),
    tm 4 2 3 1 0 (1),
    tm 3 2 3 1 1 (-1),
    tm 3 2 3 2 0 (1),
    tm 2 2 3 2 1 (2),
    tm 1 2 3 3 1 (1),
    tm 0 2 3 3 2 (1)]

/-- Chart core 92 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore92 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 1 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (1),
    tm 7 1 1 1 1 (2),
    tm 8 2 1 0 0 (2),
    tm 7 2 1 1 0 (1),
    tm 6 2 1 1 1 (1),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (3),
    tm 5 2 2 2 0 (1),
    tm 4 2 2 2 1 (2),
    tm 3 2 2 2 2 (1),
    tm 8 3 0 0 0 (1),
    tm 7 3 1 0 0 (-1),
    tm 6 3 1 1 0 (2),
    tm 5 3 1 1 1 (1),
    tm 6 3 2 0 0 (1),
    tm 4 3 2 2 0 (1),
    tm 3 3 2 2 1 (2),
    tm 4 3 3 1 0 (1),
    tm 3 3 3 1 1 (1),
    tm 3 3 3 2 0 (1),
    tm 2 3 3 2 1 (2),
    tm 1 3 3 2 2 (1),
    tm 1 3 3 3 1 (1),
    tm 0 3 3 3 2 (1),
    tm 5 4 2 0 0 (-1),
    tm 3 4 2 1 1 (-1),
    tm 3 4 3 1 0 (-1),
    tm 2 4 3 1 1 (-1),
    tm 1 4 3 2 1 (-1),
    tm 0 4 3 2 2 (-1)]

/-- Chart core 93 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore93 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 8 0 1 0 0 (-1),
    tm 7 0 1 1 0 (2),
    tm 6 0 2 1 0 (-1),
    tm 5 0 2 2 0 (1),
    tm 6 1 2 0 0 (-1),
    tm 4 1 2 1 1 (-1),
    tm 3 1 2 2 1 (-1),
    tm 4 1 3 1 0 (-1),
    tm 2 1 3 2 1 (-1),
    tm 1 1 3 3 1 (-1),
    tm 0 1 3 3 2 (-1)]

/-- Chart core 94 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore94 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 7 0 1 0 0 (-1),
    tm 6 0 1 1 0 (1),
    tm 4 0 2 1 1 (-1),
    tm 6 1 1 0 0 (1),
    tm 5 1 2 0 0 (-2),
    tm 4 1 2 1 0 (1),
    tm 3 1 2 1 1 (-1),
    tm 2 1 3 1 1 (-1),
    tm 0 1 3 2 2 (-1),
    tm 3 2 3 0 0 (-1),
    tm 1 2 3 1 1 (-1)]

/-- Chart core 95 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore95 : Poly :=
  [tm 5 0 0 0 0 (1),
    tm 4 0 1 0 0 (-1),
    tm 3 0 1 1 0 (1),
    tm 0 0 2 2 1 (1),
    tm 2 1 2 0 0 (-1),
    tm 0 1 2 1 1 (-1)]

/-- Chart core 96 of the barycentric order chart 43210,
homogenized to degree 3. -/
def chartCore96 : Poly :=
  [tm 3 0 0 0 0 (1),
    tm 2 0 1 0 0 (-1),
    tm 1 0 1 1 0 (1),
    tm 0 1 2 0 0 (-1)]

/-- Chart core 97 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore97 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 4 0 1 1 0 (1),
    tm 3 1 0 1 1 (-1),
    tm 4 1 1 0 0 (1),
    tm 1 1 1 2 1 (-1),
    tm 0 1 1 2 2 (-1),
    tm 2 1 2 1 0 (1)]

/-- Chart core 98 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore98 : Poly :=
  [tm 5 0 0 0 0 (1),
    tm 4 0 0 0 1 (-1),
    tm 3 1 1 0 0 (2),
    tm 2 1 1 0 1 (-1),
    tm 0 1 1 1 2 (-1),
    tm 1 2 2 0 0 (1)]

/-- Chart core 99 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore99 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 0 0 1 0 (-1),
    tm 8 0 1 2 0 (-1),
    tm 7 0 1 2 1 (-1),
    tm 9 1 0 1 0 (-1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (-1),
    tm 7 1 1 1 1 (1),
    tm 7 1 1 2 0 (-2),
    tm 6 1 1 2 1 (-2),
    tm 6 1 2 2 0 (-1),
    tm 5 1 2 2 1 (-1),
    tm 5 1 2 3 0 (-1),
    tm 4 1 2 3 1 (-2),
    tm 3 1 2 3 2 (-1),
    tm 7 2 1 1 0 (-1),
    tm 6 2 1 2 0 (-1),
    tm 5 2 1 2 1 (-1),
    tm 7 2 2 0 0 (1),
    tm 5 2 2 1 1 (1),
    tm 5 2 2 2 0 (-2),
    tm 4 2 2 2 1 (-1),
    tm 4 2 2 3 0 (-2),
    tm 3 2 2 3 1 (-3),
    tm 2 2 2 3 2 (-1),
    tm 3 2 3 3 0 (-1),
    tm 2 2 3 3 1 (-1),
    tm 2 2 3 4 0 (-1),
    tm 1 2 3 4 1 (-2),
    tm 0 2 3 4 2 (-1)]

/-- Chart core 100 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore100 : Poly :=
  [tm 9 0 1 0 0 (1),
    tm 9 1 0 0 0 (-1),
    tm 8 1 1 0 0 (-1),
    tm 7 1 1 1 0 (-2),
    tm 6 1 1 1 1 (-1),
    tm 7 1 2 0 0 (2),
    tm 6 1 2 1 0 (-1),
    tm 5 1 2 2 0 (-1),
    tm 4 1 2 2 1 (-1),
    tm 8 2 0 0 0 (-1),
    tm 7 2 1 0 0 (-1),
    tm 6 2 1 1 0 (-2),
    tm 5 2 1 1 1 (-2),
    tm 6 2 2 0 0 (-1),
    tm 5 2 2 1 0 (-2),
    tm 4 2 2 1 1 (-2),
    tm 4 2 2 2 0 (-1),
    tm 3 2 2 2 1 (-3),
    tm 2 2 2 2 2 (-1),
    tm 5 2 3 0 0 (1),
    tm 4 2 3 1 0 (-1),
    tm 3 2 3 2 0 (-1),
    tm 2 2 3 2 1 (-2),
    tm 1 2 3 2 2 (-1),
    tm 1 2 3 3 1 (-1),
    tm 0 2 3 3 2 (-1)]

/-- Chart core 101 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore101 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 1 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (1),
    tm 7 1 1 1 1 (2),
    tm 8 2 1 0 0 (2),
    tm 7 2 1 1 0 (1),
    tm 6 2 1 1 1 (1),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (3),
    tm 5 2 2 2 0 (1),
    tm 4 2 2 2 1 (2),
    tm 3 2 2 2 2 (1),
    tm 7 3 1 0 0 (-1),
    tm 6 3 2 0 0 (1),
    tm 3 3 2 2 1 (1),
    tm 4 3 3 1 0 (1),
    tm 3 3 3 1 1 (1),
    tm 3 3 3 2 0 (1),
    tm 2 3 3 2 1 (2),
    tm 1 3 3 2 2 (1),
    tm 1 3 3 3 1 (1),
    tm 0 3 3 3 2 (1),
    tm 5 4 2 0 0 (-1),
    tm 3 4 3 1 0 (-1),
    tm 2 4 3 1 1 (-1)]

/-- Chart core 102 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore102 : Poly :=
  [tm 4 0 0 0 0 (1),
    tm 0 0 1 2 1 (-1),
    tm 2 1 1 0 0 (1)]

/-- Chart core 103 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore103 : Poly :=
  [tm 4 0 0 0 0 (1),
    tm 2 1 1 0 0 (1),
    tm 0 1 1 1 1 (-1)]

/-- Chart core 104 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore104 : Poly :=
  [tm 13 0 0 0 0 (1),
    tm 12 1 0 0 0 (-1),
    tm 11 1 1 0 0 (2),
    tm 10 1 1 1 0 (-2),
    tm 9 1 1 1 1 (1),
    tm 9 1 2 1 0 (-1),
    tm 8 1 2 2 0 (-1),
    tm 7 1 2 2 1 (-1),
    tm 11 2 0 0 0 (-1),
    tm 10 2 1 0 0 (-1),
    tm 9 2 1 1 0 (-3),
    tm 8 2 1 1 1 (-2),
    tm 9 2 2 0 0 (1),
    tm 8 2 2 1 0 (-2),
    tm 7 2 2 1 1 (2),
    tm 7 2 2 2 0 (-3),
    tm 6 2 2 2 1 (-4),
    tm 7 2 3 1 0 (-2),
    tm 6 2 3 2 0 (-1),
    tm 5 2 3 2 1 (-2),
    tm 5 2 3 3 0 (-1),
    tm 4 2 3 3 1 (-2),
    tm 3 2 3 3 2 (-1),
    tm 9 3 1 0 0 (-1),
    tm 8 3 1 1 0 (-1),
    tm 7 3 1 1 1 (-1),
    tm 7 3 2 1 0 (-3),
    tm 6 3 2 1 1 (-1),
    tm 6 3 2 2 0 (-3),
    tm 5 3 2 2 1 (-4),
    tm 4 3 2 2 2 (-1),
    tm 5 3 3 1 1 (1),
    tm 5 3 3 2 0 (-3),
    tm 4 3 3 2 1 (-2),
    tm 3 3 3 2 2 (1),
    tm 4 3 3 3 0 (-3),
    tm 3 3 3 3 1 (-5),
    tm 2 3 3 3 2 (-2),
    tm 5 3 4 1 0 (-1),
    tm 3 3 4 2 1 (-1),
    tm 3 3 4 3 0 (-1),
    tm 2 3 4 3 1 (-1),
    tm 2 3 4 4 0 (-1),
    tm 1 3 4 4 1 (-2),
    tm 0 3 4 4 2 (-1)]

/-- Chart core 105 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore105 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 0 0 1 0 (-1),
    tm 10 0 1 0 0 (1),
    tm 9 0 1 1 0 (2),
    tm 8 0 1 1 1 (1),
    tm 8 0 1 2 0 (-1),
    tm 7 0 1 2 1 (-1),
    tm 8 0 2 1 0 (1),
    tm 7 0 2 2 0 (1),
    tm 6 0 2 2 1 (1),
    tm 10 1 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (1),
    tm 7 1 1 1 1 (2),
    tm 6 1 1 2 1 (-1),
    tm 8 1 2 0 0 (2),
    tm 7 1 2 1 0 (4),
    tm 6 1 2 1 1 (3),
    tm 6 1 2 2 0 (1),
    tm 5 1 2 2 1 (2),
    tm 4 1 2 2 2 (1),
    tm 4 1 2 3 1 (-1),
    tm 3 1 2 3 2 (-1),
    tm 6 1 3 1 0 (2),
    tm 5 1 3 2 0 (2),
    tm 4 1 3 2 1 (3),
    tm 4 1 3 3 0 (1),
    tm 3 1 3 3 1 (2),
    tm 2 1 3 3 2 (1),
    tm 8 2 1 0 0 (1),
    tm 6 2 1 1 1 (1),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (2),
    tm 4 2 2 2 1 (1),
    tm 3 2 2 2 2 (1),
    tm 6 2 3 0 0 (1),
    tm 5 2 3 1 0 (2),
    tm 4 2 3 1 1 (2),
    tm 4 2 3 2 0 (2),
    tm 3 2 3 2 1 (3),
    tm 2 2 3 2 2 (1),
    tm 4 2 4 1 0 (1),
    tm 3 2 4 2 0 (1),
    tm 2 2 4 2 1 (2),
    tm 2 2 4 3 0 (1),
    tm 1 2 4 3 1 (2),
    tm 0 2 4 3 2 (1)]

/-- Chart core 106 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore106 : Poly :=
  [tm 11 0 1 1 0 (1),
    tm 9 1 2 1 0 (2),
    tm 7 1 2 2 1 (2),
    tm 7 1 3 2 0 (-1),
    tm 11 2 0 0 0 (-1),
    tm 10 2 1 0 0 (-1),
    tm 9 2 1 1 0 (-3),
    tm 8 2 1 1 1 (-1),
    tm 8 2 2 1 0 (-2),
    tm 7 2 2 1 1 (-1),
    tm 7 2 2 2 0 (-3),
    tm 6 2 2 2 1 (-2),
    tm 7 2 3 1 0 (1),
    tm 6 2 3 2 0 (-1),
    tm 5 2 3 2 1 (2),
    tm 5 2 3 3 0 (-1),
    tm 4 2 3 3 1 (-1),
    tm 3 2 3 3 2 (1),
    tm 5 2 4 2 0 (-2),
    tm 3 2 4 3 1 (-1),
    tm 10 3 0 0 0 (-1),
    tm 9 3 1 0 0 (-1),
    tm 8 3 1 1 0 (-3),
    tm 7 3 1 1 1 (-2),
    tm 8 3 2 0 0 (-1),
    tm 7 3 2 1 0 (-3),
    tm 6 3 2 1 1 (-2),
    tm 6 3 2 2 0 (-3),
    tm 5 3 2 2 1 (-5),
    tm 4 3 2 2 2 (-1),
    tm 6 3 3 1 0 (-2),
    tm 5 3 3 1 1 (-1),
    tm 5 3 3 2 0 (-3),
    tm 4 3 3 2 1 (-4),
    tm 3 3 3 2 2 (-1),
    tm 4 3 3 3 0 (-1),
    tm 3 3 3 3 1 (-4),
    tm 2 3 3 3 2 (-2),
    tm 4 3 4 2 0 (-1),
    tm 3 3 4 3 0 (-1),
    tm 2 3 4 3 1 (-2),
    tm 1 3 4 4 1 (-1),
    tm 0 3 4 4 2 (-1),
    tm 3 3 5 2 0 (-1),
    tm 1 3 5 3 1 (-1)]

/-- Chart core 107 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore107 : Poly :=
  [tm 13 0 0 0 0 (1),
    tm 11 0 1 1 0 (1),
    tm 12 1 0 0 0 (1),
    tm 11 1 1 0 0 (2),
    tm 10 1 1 1 0 (2),
    tm 9 1 1 1 1 (2),
    tm 9 1 2 1 0 (2),
    tm 8 1 2 2 0 (1),
    tm 7 1 2 2 1 (2),
    tm 10 2 1 0 0 (2),
    tm 8 2 1 1 1 (1),
    tm 9 2 2 0 0 (1),
    tm 8 2 2 1 0 (4),
    tm 7 2 2 1 1 (3),
    tm 7 2 2 2 0 (1),
    tm 6 2 2 2 1 (2),
    tm 5 2 2 2 2 (1),
    tm 7 2 3 1 0 (1),
    tm 6 2 3 2 0 (2),
    tm 5 2 3 2 1 (3),
    tm 5 2 3 3 0 (1),
    tm 4 2 3 3 1 (2),
    tm 3 2 3 3 2 (1),
    tm 8 3 2 0 0 (1),
    tm 6 3 2 1 1 (1),
    tm 6 3 3 1 0 (2),
    tm 5 3 3 1 1 (1),
    tm 5 3 3 2 0 (2),
    tm 4 3 3 2 1 (2),
    tm 3 3 3 2 2 (1),
    tm 3 3 3 3 1 (1),
    tm 4 3 4 2 0 (1),
    tm 3 3 4 2 1 (1),
    tm 3 3 4 3 0 (2),
    tm 2 3 4 3 1 (3),
    tm 1 3 4 3 2 (1),
    tm 1 3 4 4 1 (1),
    tm 0 3 4 4 2 (1),
    tm 3 4 3 2 1 (-1),
    tm 3 4 4 2 0 (1),
    tm 1 4 4 3 1 (-1),
    tm 0 4 4 3 2 (-1),
    tm 1 4 5 3 0 (1),
    tm 0 4 5 3 1 (1)]

/-- Chart core 108 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore108 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 6 1 1 0 0 (1),
    tm 4 1 1 1 1 (1),
    tm 4 1 2 1 0 (-1),
    tm 3 2 1 1 1 (1),
    tm 2 2 2 1 1 (1),
    tm 1 2 2 2 1 (1),
    tm 0 2 2 2 2 (1),
    tm 2 2 3 1 0 (-1)]

/-- Chart core 109 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore109 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 7 1 1 0 0 (2),
    tm 6 1 1 0 1 (1),
    tm 5 1 1 1 1 (1),
    tm 5 1 2 1 0 (-1),
    tm 4 1 2 1 1 (1),
    tm 5 2 2 0 0 (1),
    tm 4 2 2 0 1 (1),
    tm 3 2 2 1 1 (2),
    tm 2 2 2 1 2 (1),
    tm 3 2 3 1 0 (-2),
    tm 2 2 3 1 1 (1),
    tm 0 2 3 2 2 (1),
    tm 1 3 3 1 1 (1),
    tm 1 3 4 1 0 (-1)]

/-- Chart core 110 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore110 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 4 1 1 0 0 (1),
    tm 2 1 2 1 0 (-1),
    tm 0 1 2 2 1 (-1),
    tm 0 2 2 1 1 (1),
    tm 0 2 3 1 0 (-1)]

/-- Chart core 111 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore111 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 4 1 1 0 0 (1),
    tm 2 1 1 1 1 (1),
    tm 2 1 2 1 0 (-1),
    tm 2 2 1 0 1 (-1),
    tm 0 2 3 1 0 (-1)]

/-- Chart core 112 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore112 : Poly :=
  [tm 12 0 0 1 0 (1),
    tm 10 0 1 2 0 (1),
    tm 9 0 1 2 1 (1),
    tm 12 1 0 0 0 (-1),
    tm 11 1 0 1 0 (1),
    tm 10 1 1 1 0 (1),
    tm 9 1 1 1 1 (-1),
    tm 9 1 1 2 0 (2),
    tm 8 1 1 2 1 (2),
    tm 8 1 2 2 0 (2),
    tm 7 1 2 2 1 (1),
    tm 7 1 2 3 0 (1),
    tm 6 1 2 3 1 (2),
    tm 5 1 2 3 2 (1),
    tm 10 2 1 0 0 (-1),
    tm 9 2 1 1 0 (2),
    tm 8 2 1 1 1 (-1),
    tm 8 2 1 2 0 (1),
    tm 7 2 1 2 1 (1),
    tm 8 2 2 1 0 (1),
    tm 7 2 2 1 1 (-1),
    tm 7 2 2 2 0 (4),
    tm 6 2 2 2 1 (2),
    tm 5 2 2 2 2 (-1),
    tm 6 2 2 3 0 (2),
    tm 5 2 2 3 1 (3),
    tm 4 2 2 3 2 (1),
    tm 6 2 3 2 0 (2),
    tm 5 2 3 3 0 (2),
    tm 4 2 3 3 1 (3),
    tm 4 2 3 4 0 (1),
    tm 3 2 3 4 1 (2),
    tm 2 2 3 4 2 (1),
    tm 7 3 2 1 0 (1),
    tm 6 3 2 2 0 (1),
    tm 5 3 2 2 1 (1),
    tm 6 3 3 1 0 (1),
    tm 5 3 3 2 0 (2),
    tm 4 3 3 2 1 (2),
    tm 4 3 3 3 0 (2),
    tm 3 3 3 3 1 (3),
    tm 2 3 3 3 2 (1),
    tm 4 3 4 2 0 (1),
    tm 3 3 4 3 0 (1),
    tm 2 3 4 3 1 (2),
    tm 2 3 4 4 0 (1),
    tm 1 3 4 4 1 (2),
    tm 0 3 4 4 2 (1)]

/-- Chart core 113 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore113 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 0 1 0 0 (1),
    tm 9 0 1 1 0 (1),
    tm 8 0 1 1 1 (1),
    tm 10 1 0 0 0 (1),
    tm 9 1 1 0 0 (3),
    tm 8 1 1 1 0 (1),
    tm 7 1 1 1 1 (2),
    tm 8 1 2 0 0 (3),
    tm 7 1 2 1 0 (3),
    tm 6 1 2 1 1 (4),
    tm 5 1 2 2 1 (1),
    tm 4 1 2 2 2 (1),
    tm 9 2 0 0 0 (-1),
    tm 8 2 1 0 0 (2),
    tm 7 2 1 1 0 (-2),
    tm 6 2 1 1 1 (-1),
    tm 7 2 2 0 0 (3),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (4),
    tm 5 2 2 2 0 (-1),
    tm 4 2 2 2 1 (-2),
    tm 6 2 3 0 0 (3),
    tm 5 2 3 1 0 (3),
    tm 4 2 3 1 1 (5),
    tm 3 2 3 2 1 (2),
    tm 2 2 3 2 2 (2),
    tm 2 2 3 3 1 (-1),
    tm 1 2 3 3 2 (-1),
    tm 6 3 2 0 0 (1),
    tm 5 3 2 1 0 (1),
    tm 4 3 2 1 1 (1),
    tm 5 3 3 0 0 (1),
    tm 4 3 3 1 0 (1),
    tm 3 3 3 1 1 (2),
    tm 3 3 3 2 0 (2),
    tm 2 3 3 2 1 (2),
    tm 1 3 3 2 2 (1),
    tm 4 3 4 0 0 (1),
    tm 3 3 4 1 0 (1),
    tm 2 3 4 1 1 (2),
    tm 1 3 4 2 1 (1),
    tm 0 3 4 2 2 (1),
    tm 1 3 4 3 0 (1),
    tm 0 3 4 3 1 (1)]

/-- Chart core 114 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore114 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 9 0 1 1 0 (2),
    tm 8 0 1 1 1 (1),
    tm 7 0 2 2 0 (1),
    tm 6 0 2 2 1 (1),
    tm 5 0 3 2 1 (-1),
    tm 10 1 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (2),
    tm 7 1 1 1 1 (2),
    tm 8 1 2 0 0 (1),
    tm 7 1 2 1 0 (4),
    tm 6 1 2 1 1 (2),
    tm 6 1 2 2 0 (1),
    tm 5 1 2 2 1 (3),
    tm 4 1 2 2 2 (1),
    tm 6 1 3 1 0 (2),
    tm 5 1 3 1 1 (1),
    tm 5 1 3 2 0 (2),
    tm 4 1 3 2 1 (2),
    tm 3 1 3 3 1 (1),
    tm 2 1 3 3 2 (1),
    tm 4 1 4 2 0 (1),
    tm 3 1 4 2 1 (-1),
    tm 1 1 4 3 2 (-1),
    tm 8 2 1 0 0 (1),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (2),
    tm 6 2 3 0 0 (1),
    tm 5 2 3 1 0 (2),
    tm 4 2 3 1 1 (2),
    tm 4 2 3 2 0 (1),
    tm 3 2 3 2 1 (3),
    tm 2 2 3 2 2 (1),
    tm 4 2 4 1 0 (2),
    tm 3 2 4 1 1 (1),
    tm 3 2 4 2 0 (1),
    tm 2 2 4 2 1 (3),
    tm 1 2 4 2 2 (1),
    tm 1 2 4 3 1 (1),
    tm 0 2 4 3 2 (1),
    tm 2 2 5 2 0 (1),
    tm 0 2 5 3 1 (1)]

/-- Chart core 115 of the barycentric order chart 43210,
homogenized to degree 14. -/
def chartCore115 : Poly :=
  [tm 14 0 0 0 0 (1),
    tm 13 1 0 0 0 (1),
    tm 12 1 1 0 0 (3),
    tm 11 1 1 1 0 (1),
    tm 10 1 1 1 1 (2),
    tm 11 2 1 0 0 (3),
    tm 10 2 1 1 0 (1),
    tm 9 2 1 1 1 (1),
    tm 10 2 2 0 0 (3),
    tm 9 2 2 1 0 (3),
    tm 8 2 2 1 1 (5),
    tm 8 2 2 2 0 (1),
    tm 7 2 2 2 1 (2),
    tm 6 2 2 2 2 (1),
    tm 9 3 2 0 0 (3),
    tm 8 3 2 1 0 (2),
    tm 7 3 2 1 1 (2),
    tm 6 3 2 2 1 (1),
    tm 8 3 3 0 0 (1),
    tm 7 3 3 1 0 (3),
    tm 6 3 3 1 1 (4),
    tm 6 3 3 2 0 (2),
    tm 5 3 3 2 1 (4),
    tm 4 3 3 2 2 (2),
    tm 4 3 3 3 1 (1),
    tm 3 3 3 3 2 (1),
    tm 9 4 1 0 0 (-1),
    tm 7 4 2 1 0 (-2),
    tm 6 4 2 1 1 (-2),
    tm 7 4 3 0 0 (1),
    tm 6 4 3 1 0 (1),
    tm 5 4 3 1 1 (1),
    tm 5 4 3 2 0 (-1),
    tm 4 4 3 2 1 (-2),
    tm 3 4 3 2 2 (-1),
    tm 5 4 4 1 0 (1),
    tm 4 4 4 1 1 (1),
    tm 4 4 4 2 0 (1),
    tm 3 4 4 2 1 (2),
    tm 2 4 4 2 2 (1),
    tm 5 5 3 1 0 (1),
    tm 3 5 4 2 0 (2),
    tm 2 5 4 2 1 (1),
    tm 1 5 5 3 0 (1),
    tm 0 5 5 3 1 (1)]

/-- Chart core 116 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore116 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 7 0 1 1 0 (2),
    tm 6 0 1 1 1 (1),
    tm 5 0 1 2 1 (1),
    tm 5 0 2 2 0 (1),
    tm 4 0 2 2 1 (2),
    tm 3 0 2 3 1 (1),
    tm 2 0 2 3 2 (1),
    tm 2 0 3 3 1 (1),
    tm 5 1 2 1 0 (-1),
    tm 3 1 2 2 1 (1),
    tm 3 1 3 2 0 (-2),
    tm 1 1 3 3 1 (1),
    tm 0 1 3 3 2 (1),
    tm 1 1 4 3 0 (-1)]

/-- Chart core 117 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore117 : Poly :=
  [tm 4 0 1 1 1 (1),
    tm 6 1 0 0 0 (1),
    tm 4 1 1 1 0 (1),
    tm 3 1 1 1 1 (1),
    tm 2 1 2 1 1 (1),
    tm 1 1 2 2 1 (1),
    tm 0 1 2 2 2 (1),
    tm 2 2 2 1 0 (-1),
    tm 0 2 3 2 0 (-1)]

/-- Chart core 118 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore118 : Poly :=
  [tm 3 0 1 2 1 (1),
    tm 6 1 0 0 0 (-1),
    tm 4 1 1 1 0 (-1),
    tm 3 1 1 1 1 (-1),
    tm 2 2 2 1 0 (1),
    tm 0 2 3 2 0 (1)]

/-- Chart core 119 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore119 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 4 0 1 1 0 (1),
    tm 1 0 2 2 1 (1),
    tm 2 1 2 1 0 (-1),
    tm 1 1 2 1 1 (-1),
    tm 0 1 3 2 0 (-1)]

/-- Chart core 120 of the barycentric order chart 43210,
homogenized to degree 15. -/
def chartCore120 : Poly :=
  [tm 15 0 0 0 0 (1),
    tm 13 1 1 0 0 (2),
    tm 12 1 1 1 0 (1),
    tm 11 1 1 1 1 (1),
    tm 11 1 2 1 0 (-1),
    tm 10 1 2 2 0 (2),
    tm 8 1 3 3 0 (1),
    tm 7 1 3 3 1 (1),
    tm 11 2 1 1 0 (1),
    tm 11 2 2 0 0 (1),
    tm 10 2 2 1 0 (1),
    tm 9 2 2 1 1 (1),
    tm 9 2 2 2 0 (3),
    tm 8 2 2 2 1 (2),
    tm 9 2 3 1 0 (-2),
    tm 8 2 3 2 0 (2),
    tm 7 2 3 2 1 (-2),
    tm 7 2 3 3 0 (3),
    tm 6 2 3 3 1 (4),
    tm 6 2 4 3 0 (1),
    tm 5 2 4 3 1 (1),
    tm 5 2 4 4 0 (1),
    tm 4 2 4 4 1 (2),
    tm 3 2 4 4 2 (1),
    tm 9 3 2 1 0 (1),
    tm 8 3 2 2 0 (1),
    tm 7 3 2 2 1 (1),
    tm 7 3 3 2 0 (3),
    tm 6 3 3 2 1 (1),
    tm 6 3 3 3 0 (3),
    tm 5 3 3 3 1 (4),
    tm 4 3 3 3 2 (1),
    tm 7 3 4 1 0 (-1),
    tm 5 3 4 2 1 (-2),
    tm 5 3 4 3 0 (3),
    tm 4 3 4 3 1 (2),
    tm 3 3 4 3 2 (-1),
    tm 4 3 4 4 0 (3),
    tm 3 3 4 4 1 (5),
    tm 2 3 4 4 2 (2),
    tm 3 3 5 4 0 (1),
    tm 2 3 5 4 1 (1),
    tm 2 3 5 5 0 (1),
    tm 1 3 5 5 1 (2),
    tm 0 3 5 5 2 (1)]

/-- Chart core 121 of the barycentric order chart 43210,
homogenized to degree 12. -/
def chartCore121 : Poly :=
  [tm 12 0 0 0 0 (1),
    tm 11 0 1 0 0 (1),
    tm 10 0 1 1 0 (1),
    tm 9 0 1 1 1 (1),
    tm 10 0 2 0 0 (1),
    tm 9 0 2 1 0 (2),
    tm 8 0 2 1 1 (1),
    tm 8 0 3 1 0 (1),
    tm 7 0 3 2 0 (1),
    tm 6 0 3 2 1 (1),
    tm 10 1 1 0 0 (2),
    tm 9 1 2 0 0 (2),
    tm 8 1 2 1 0 (2),
    tm 7 1 2 1 1 (3),
    tm 6 1 2 2 1 (-1),
    tm 8 1 3 0 0 (2),
    tm 7 1 3 1 0 (4),
    tm 6 1 3 1 1 (3),
    tm 5 1 3 2 1 (2),
    tm 4 1 3 2 2 (1),
    tm 4 1 3 3 1 (-1),
    tm 3 1 3 3 2 (-1),
    tm 6 1 4 1 0 (2),
    tm 5 1 4 2 0 (2),
    tm 4 1 4 2 1 (3),
    tm 3 1 4 3 1 (1),
    tm 2 1 4 3 2 (1),
    tm 8 2 2 0 0 (1),
    tm 6 2 2 1 1 (1),
    tm 7 2 3 0 0 (1),
    tm 6 2 3 1 0 (1),
    tm 5 2 3 1 1 (2),
    tm 4 2 3 2 1 (1),
    tm 3 2 3 2 2 (1),
    tm 6 2 4 0 0 (1),
    tm 5 2 4 1 0 (2),
    tm 4 2 4 1 1 (2),
    tm 3 2 4 2 1 (2),
    tm 2 2 4 2 2 (1),
    tm 4 2 5 1 0 (1),
    tm 3 2 5 2 0 (1),
    tm 2 2 5 2 1 (2),
    tm 1 2 5 3 1 (1),
    tm 0 2 5 3 2 (1)]

/-- Chart core 122 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore122 : Poly :=
  [tm 13 0 0 0 0 (1),
    tm 11 1 1 0 0 (2),
    tm 9 1 1 1 1 (1),
    tm 9 1 2 1 0 (-1),
    tm 7 1 2 2 1 (-1),
    tm 11 2 0 0 0 (1),
    tm 10 2 1 0 0 (1),
    tm 9 2 1 1 0 (3),
    tm 8 2 1 1 1 (1),
    tm 9 2 2 0 0 (1),
    tm 8 2 2 1 0 (2),
    tm 7 2 2 1 1 (2),
    tm 7 2 2 2 0 (3),
    tm 6 2 2 2 1 (2),
    tm 7 2 3 1 0 (-2),
    tm 6 2 3 2 0 (1),
    tm 5 2 3 2 1 (-2),
    tm 5 2 3 3 0 (1),
    tm 4 2 3 3 1 (1),
    tm 3 2 3 3 2 (-1),
    tm 10 3 0 0 0 (1),
    tm 9 3 1 0 0 (1),
    tm 8 3 1 1 0 (3),
    tm 7 3 1 1 1 (2),
    tm 8 3 2 0 0 (1),
    tm 7 3 2 1 0 (3),
    tm 6 3 2 1 1 (2),
    tm 6 3 2 2 0 (3),
    tm 5 3 2 2 1 (5),
    tm 4 3 2 2 2 (1),
    tm 6 3 3 1 0 (2),
    tm 5 3 3 1 1 (1),
    tm 5 3 3 2 0 (3),
    tm 4 3 3 2 1 (4),
    tm 3 3 3 2 2 (1),
    tm 4 3 3 3 0 (1),
    tm 3 3 3 3 1 (4),
    tm 2 3 3 3 2 (2),
    tm 5 3 4 1 0 (-1),
    tm 4 3 4 2 0 (1),
    tm 3 3 4 2 1 (-1),
    tm 3 3 4 3 0 (1),
    tm 2 3 4 3 1 (2),
    tm 1 3 4 4 1 (1),
    tm 0 3 4 4 2 (1)]

/-- Chart core 123 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore123 : Poly :=
  [tm 13 0 0 0 0 (1),
    tm 11 0 1 1 0 (1),
    tm 12 1 0 0 0 (1),
    tm 11 1 1 0 0 (2),
    tm 10 1 1 1 0 (2),
    tm 9 1 1 1 1 (2),
    tm 9 1 2 1 0 (2),
    tm 8 1 2 2 0 (1),
    tm 7 1 2 2 1 (2),
    tm 11 2 0 0 0 (1),
    tm 10 2 1 0 0 (2),
    tm 9 2 1 1 0 (2),
    tm 8 2 1 1 1 (2),
    tm 9 2 2 0 0 (1),
    tm 8 2 2 1 0 (4),
    tm 7 2 2 1 1 (3),
    tm 7 2 2 2 0 (2),
    tm 6 2 2 2 1 (3),
    tm 5 2 2 2 2 (1),
    tm 7 2 3 1 0 (1),
    tm 6 2 3 2 0 (2),
    tm 5 2 3 2 1 (3),
    tm 5 2 3 3 0 (1),
    tm 4 2 3 3 1 (2),
    tm 3 2 3 3 2 (1),
    tm 9 3 1 0 0 (1),
    tm 8 3 2 0 0 (1),
    tm 7 3 2 1 0 (1),
    tm 6 3 2 1 1 (2),
    tm 6 3 3 1 0 (2),
    tm 5 3 3 1 1 (1),
    tm 5 3 3 2 0 (1),
    tm 4 3 3 2 1 (2),
    tm 3 3 3 2 2 (1),
    tm 3 3 3 3 1 (1),
    tm 4 3 4 2 0 (1),
    tm 3 3 4 2 1 (1),
    tm 3 3 4 3 0 (1),
    tm 2 3 4 3 1 (2),
    tm 1 3 4 3 2 (1),
    tm 1 3 4 4 1 (1),
    tm 0 3 4 4 2 (1),
    tm 5 4 3 1 0 (-1),
    tm 3 4 3 2 1 (-1),
    tm 3 4 4 2 0 (-1),
    tm 2 4 4 2 1 (-1),
    tm 1 4 4 3 1 (-1),
    tm 0 4 4 3 2 (-1)]

/-- Chart core 124 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore124 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 8 1 1 0 0 (1),
    tm 6 1 2 1 0 (-1),
    tm 4 1 2 2 1 (-1),
    tm 3 2 2 2 1 (-1),
    tm 4 2 3 1 0 (-1),
    tm 2 2 3 2 1 (-1),
    tm 1 2 3 3 1 (-1),
    tm 0 2 3 3 2 (-1)]

/-- Chart core 125 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore125 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 7 1 2 1 0 (-1),
    tm 6 1 2 1 1 (-1),
    tm 5 1 2 2 1 (-1),
    tm 4 1 3 2 1 (-1),
    tm 7 2 2 0 0 (1),
    tm 5 2 3 1 0 (-2),
    tm 4 2 3 1 1 (-1),
    tm 3 2 3 2 1 (-2),
    tm 2 2 3 2 2 (-1),
    tm 2 2 4 2 1 (-1),
    tm 0 2 4 3 2 (-1),
    tm 3 3 4 1 0 (-1),
    tm 1 3 4 2 1 (-1)]

/-- Chart core 126 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore126 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 6 1 1 0 0 (1),
    tm 4 1 2 1 0 (-1),
    tm 0 1 3 3 1 (1),
    tm 2 2 3 1 0 (-1),
    tm 0 2 3 2 1 (-1)]

/-- Chart core 127 of the barycentric order chart 43210,
homogenized to degree 14. -/
def chartCore127 : Poly :=
  [tm 14 0 0 0 0 (1),
    tm 12 0 1 1 0 (2),
    tm 10 0 2 2 0 (1),
    tm 9 0 2 2 1 (1),
    tm 12 1 1 0 0 (1),
    tm 11 1 1 1 0 (1),
    tm 10 1 1 1 1 (1),
    tm 10 1 2 1 0 (2),
    tm 9 1 2 1 1 (-1),
    tm 9 1 2 2 0 (2),
    tm 8 1 2 2 1 (3),
    tm 8 1 3 2 0 (1),
    tm 7 1 3 2 1 (1),
    tm 7 1 3 3 0 (1),
    tm 6 1 3 3 1 (2),
    tm 5 1 3 3 2 (1),
    tm 9 2 2 1 0 (2),
    tm 8 2 2 2 0 (1),
    tm 7 2 2 2 1 (1),
    tm 7 2 3 1 1 (-1),
    tm 7 2 3 2 0 (4),
    tm 6 2 3 2 1 (2),
    tm 5 2 3 2 2 (-1),
    tm 6 2 3 3 0 (2),
    tm 5 2 3 3 1 (3),
    tm 4 2 3 3 2 (1),
    tm 5 2 4 3 0 (2),
    tm 4 2 4 3 1 (2),
    tm 4 2 4 4 0 (1),
    tm 3 2 4 4 1 (2),
    tm 2 2 4 4 2 (1),
    tm 7 3 3 1 0 (1),
    tm 6 3 3 2 0 (1),
    tm 5 3 3 2 1 (1),
    tm 5 3 4 2 0 (2),
    tm 4 3 4 2 1 (1),
    tm 4 3 4 3 0 (2),
    tm 3 3 4 3 1 (3),
    tm 2 3 4 3 2 (1),
    tm 3 3 5 3 0 (1),
    tm 2 3 5 3 1 (1),
    tm 2 3 5 4 0 (1),
    tm 1 3 5 4 1 (2),
    tm 0 3 5 4 2 (1)]

/-- Chart core 128 of the barycentric order chart 43210,
homogenized to degree 12. -/
def chartCore128 : Poly :=
  [tm 11 0 1 0 0 (1),
    tm 10 0 2 0 0 (1),
    tm 9 0 2 1 0 (1),
    tm 8 0 2 1 1 (1),
    tm 11 1 0 0 0 (1),
    tm 10 1 1 0 0 (1),
    tm 9 1 1 1 0 (2),
    tm 8 1 1 1 1 (1),
    tm 9 1 2 0 0 (3),
    tm 8 1 2 1 0 (1),
    tm 7 1 2 1 1 (2),
    tm 7 1 2 2 0 (1),
    tm 6 1 2 2 1 (1),
    tm 8 1 3 0 0 (3),
    tm 7 1 3 1 0 (3),
    tm 6 1 3 1 1 (4),
    tm 5 1 3 2 1 (1),
    tm 4 1 3 2 2 (1),
    tm 8 2 2 0 0 (2),
    tm 7 2 2 1 0 (-1),
    tm 7 2 3 0 0 (3),
    tm 6 2 3 1 0 (2),
    tm 5 2 3 1 1 (4),
    tm 5 2 3 2 0 (-2),
    tm 4 2 3 2 1 (-2),
    tm 6 2 4 0 0 (3),
    tm 5 2 4 1 0 (3),
    tm 4 2 4 1 1 (5),
    tm 3 2 4 2 1 (2),
    tm 2 2 4 2 2 (2),
    tm 3 2 4 3 0 (-1),
    tm 2 2 4 3 1 (-2),
    tm 1 2 4 3 2 (-1),
    tm 6 3 3 0 0 (1),
    tm 4 3 3 1 1 (1),
    tm 5 3 4 0 0 (1),
    tm 4 3 4 1 0 (1),
    tm 3 3 4 1 1 (2),
    tm 2 3 4 2 1 (1),
    tm 1 3 4 2 2 (1),
    tm 4 3 5 0 0 (1),
    tm 3 3 5 1 0 (1),
    tm 2 3 5 1 1 (2),
    tm 1 3 5 2 1 (1),
    tm 0 3 5 2 2 (1)]

/-- Chart core 129 of the barycentric order chart 43210,
homogenized to degree 12. -/
def chartCore129 : Poly :=
  [tm 12 0 0 0 0 (1),
    tm 10 0 1 1 0 (1),
    tm 11 1 0 0 0 (1),
    tm 10 1 1 0 0 (2),
    tm 9 1 1 1 0 (2),
    tm 8 1 1 1 1 (2),
    tm 8 1 2 1 0 (1),
    tm 7 1 2 2 0 (1),
    tm 6 1 2 2 1 (2),
    tm 6 1 3 2 0 (-1),
    tm 5 1 3 2 1 (-1),
    tm 10 2 0 0 0 (1),
    tm 9 2 1 0 0 (2),
    tm 8 2 1 1 0 (2),
    tm 7 2 1 1 1 (2),
    tm 8 2 2 0 0 (2),
    tm 7 2 2 1 0 (4),
    tm 6 2 2 1 1 (3),
    tm 6 2 2 2 0 (1),
    tm 5 2 2 2 1 (3),
    tm 4 2 2 2 2 (1),
    tm 6 2 3 1 0 (1),
    tm 5 2 3 1 1 (1),
    tm 5 2 3 2 0 (2),
    tm 4 2 3 2 1 (2),
    tm 3 2 3 3 1 (1),
    tm 2 2 3 3 2 (1),
    tm 4 2 4 2 0 (-1),
    tm 3 2 4 2 1 (-1),
    tm 2 2 4 3 1 (-1),
    tm 1 2 4 3 2 (-1),
    tm 8 3 1 0 0 (1),
    tm 7 3 2 0 0 (1),
    tm 6 3 2 1 0 (2),
    tm 5 3 2 1 1 (2),
    tm 6 3 3 0 0 (1),
    tm 5 3 3 1 0 (2),
    tm 4 3 3 1 1 (2),
    tm 4 3 3 2 0 (1),
    tm 3 3 3 2 1 (3),
    tm 2 3 3 2 2 (1),
    tm 4 3 4 1 0 (1),
    tm 3 3 4 1 1 (1),
    tm 3 3 4 2 0 (1),
    tm 2 3 4 2 1 (2),
    tm 1 3 4 2 2 (1),
    tm 1 3 4 3 1 (1),
    tm 0 3 4 3 2 (1)]

/-- Chart core 130 of the barycentric order chart 43210,
homogenized to degree 12. -/
def chartCore130 : Poly :=
  [tm 12 0 0 0 0 (1),
    tm 11 1 0 0 0 (1),
    tm 10 1 1 0 0 (3),
    tm 9 1 1 1 0 (1),
    tm 8 1 1 1 1 (2),
    tm 9 2 1 0 0 (3),
    tm 8 2 1 1 0 (1),
    tm 7 2 1 1 1 (1),
    tm 8 2 2 0 0 (3),
    tm 7 2 2 1 0 (3),
    tm 6 2 2 1 1 (5),
    tm 6 2 2 2 0 (1),
    tm 5 2 2 2 1 (2),
    tm 4 2 2 2 2 (1),
    tm 9 3 0 0 0 (1),
    tm 7 3 1 1 0 (2),
    tm 6 3 1 1 1 (1),
    tm 7 3 2 0 0 (3),
    tm 6 3 2 1 0 (2),
    tm 5 3 2 1 1 (2),
    tm 5 3 2 2 0 (1),
    tm 4 3 2 2 1 (2),
    tm 6 3 3 0 0 (1),
    tm 5 3 3 1 0 (3),
    tm 4 3 3 1 1 (4),
    tm 4 3 3 2 0 (2),
    tm 3 3 3 2 1 (4),
    tm 2 3 3 2 2 (2),
    tm 2 3 3 3 1 (1),
    tm 1 3 3 3 2 (1),
    tm 5 4 2 1 0 (-1),
    tm 4 4 2 1 1 (-1),
    tm 5 4 3 0 0 (1),
    tm 4 4 3 1 0 (1),
    tm 3 4 3 1 1 (1),
    tm 3 4 3 2 0 (-2),
    tm 2 4 3 2 1 (-2),
    tm 1 4 3 2 2 (-1),
    tm 3 4 4 1 0 (1),
    tm 2 4 4 1 1 (1),
    tm 2 4 4 2 0 (1),
    tm 1 4 4 2 1 (2),
    tm 0 4 4 2 2 (1),
    tm 1 4 4 3 0 (-1),
    tm 0 4 4 3 1 (-1)]

/-- Chart core 131 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore131 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 9 0 1 1 0 (2),
    tm 7 0 2 2 0 (1),
    tm 7 1 2 1 0 (-1),
    tm 6 1 2 1 1 (-1),
    tm 5 1 2 2 1 (-1),
    tm 5 1 3 2 0 (-2),
    tm 4 1 3 2 1 (-2),
    tm 3 1 3 3 1 (-1),
    tm 2 1 3 3 2 (-1),
    tm 3 1 4 3 0 (-1),
    tm 2 1 4 3 1 (-1),
    tm 3 2 3 2 1 (-1),
    tm 1 2 4 3 1 (-1),
    tm 0 2 4 3 2 (-1)]

/-- Chart core 132 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore132 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 6 0 1 1 0 (1),
    tm 4 0 2 1 1 (-1),
    tm 4 1 2 1 0 (-1),
    tm 3 1 2 1 1 (-1),
    tm 2 1 3 1 1 (-1),
    tm 2 1 3 2 0 (-1),
    tm 1 1 3 2 1 (-1),
    tm 0 1 3 2 2 (-1)]

/-- Chart core 133 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore133 : Poly :=
  [tm 7 0 0 0 0 (1),
    tm 5 0 1 1 0 (1),
    tm 3 1 2 1 0 (-1),
    tm 1 1 3 2 0 (-1),
    tm 0 1 3 2 1 (-1),
    tm 0 2 3 1 1 (1)]

/-- Chart core 134 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore134 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 8 0 1 1 0 (1),
    tm 7 0 1 1 1 (1),
    tm 9 1 0 0 0 (1),
    tm 8 1 1 0 0 (1),
    tm 7 1 1 1 0 (2),
    tm 6 1 1 1 1 (2),
    tm 6 1 2 1 0 (1),
    tm 5 1 2 2 0 (1),
    tm 4 1 2 2 1 (2),
    tm 3 1 2 2 2 (1),
    tm 7 2 1 0 0 (1),
    tm 6 2 1 1 0 (1),
    tm 5 2 1 1 1 (1),
    tm 5 2 2 1 0 (2),
    tm 4 2 2 1 1 (1),
    tm 4 2 2 2 0 (2),
    tm 3 2 2 2 1 (3),
    tm 2 2 2 2 2 (1),
    tm 3 2 3 1 1 (-1),
    tm 3 2 3 2 0 (1),
    tm 2 2 3 2 1 (1),
    tm 1 2 3 2 2 (-1),
    tm 2 2 3 3 0 (1),
    tm 1 2 3 3 1 (2),
    tm 0 2 3 3 2 (1)]

/-- Chart core 135 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore135 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 9 0 1 0 0 (1),
    tm 8 0 1 1 0 (1),
    tm 7 0 1 1 1 (1),
    tm 9 1 0 0 0 (1),
    tm 8 1 1 0 0 (2),
    tm 7 1 1 1 0 (1),
    tm 6 1 1 1 1 (2),
    tm 7 1 2 0 0 (2),
    tm 6 1 2 1 0 (2),
    tm 5 1 2 1 1 (3),
    tm 4 1 2 2 1 (1),
    tm 3 1 2 2 2 (1),
    tm 7 2 1 0 0 (1),
    tm 5 2 1 1 1 (1),
    tm 6 2 2 0 0 (1),
    tm 5 2 2 1 0 (1),
    tm 4 2 2 1 1 (2),
    tm 2 2 2 2 2 (1),
    tm 5 2 3 0 0 (1),
    tm 4 2 3 1 0 (1),
    tm 3 2 3 1 1 (2),
    tm 2 2 3 2 1 (1),
    tm 1 2 3 2 2 (1),
    tm 1 2 3 3 1 (-1),
    tm 0 2 3 3 2 (-1)]

/-- Chart core 136 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore136 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 9 0 1 0 0 (1),
    tm 8 0 1 1 0 (2),
    tm 7 0 1 1 1 (1),
    tm 7 0 2 1 0 (1),
    tm 6 0 2 1 1 (1),
    tm 6 0 2 2 0 (1),
    tm 5 0 2 2 1 (1),
    tm 4 0 3 2 1 (-1),
    tm 9 1 0 0 0 (1),
    tm 8 1 1 0 0 (1),
    tm 7 1 1 1 0 (2),
    tm 6 1 1 1 1 (2),
    tm 7 1 2 0 0 (1),
    tm 6 1 2 1 0 (2),
    tm 5 1 2 1 1 (2),
    tm 5 1 2 2 0 (1),
    tm 4 1 2 2 1 (3),
    tm 3 1 2 2 2 (1),
    tm 5 1 3 1 0 (1),
    tm 4 1 3 1 1 (1),
    tm 4 1 3 2 0 (1),
    tm 3 1 3 2 1 (2),
    tm 2 1 3 2 2 (1),
    tm 2 1 3 3 1 (1),
    tm 1 1 3 3 2 (1),
    tm 2 1 4 2 1 (-1),
    tm 0 1 4 3 2 (-1)]

/-- Chart core 137 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore137 : Poly :=
  [tm 13 0 0 0 0 (1),
    tm 12 1 0 0 0 (1),
    tm 11 1 1 0 0 (2),
    tm 10 1 1 1 0 (1),
    tm 9 1 1 1 1 (2),
    tm 10 2 1 0 0 (2),
    tm 9 2 1 1 0 (1),
    tm 8 2 1 1 1 (1),
    tm 9 2 2 0 0 (1),
    tm 8 2 2 1 0 (2),
    tm 7 2 2 1 1 (3),
    tm 7 2 2 2 0 (1),
    tm 6 2 2 2 1 (2),
    tm 5 2 2 2 2 (1),
    tm 8 3 2 0 0 (1),
    tm 7 3 2 1 0 (1),
    tm 6 3 2 1 1 (1),
    tm 5 3 2 2 1 (1),
    tm 6 3 3 1 0 (1),
    tm 5 3 3 1 1 (1),
    tm 5 3 3 2 0 (1),
    tm 4 3 3 2 1 (2),
    tm 3 3 3 2 2 (1),
    tm 3 3 3 3 1 (1),
    tm 2 3 3 3 2 (1),
    tm 3 4 3 2 1 (-1),
    tm 1 4 4 3 1 (-1),
    tm 0 4 4 3 2 (-1)]

/-- Chart core 138 of the barycentric order chart 43210,
homogenized to degree 2. -/
def chartCore138 : Poly :=
  [tm 2 0 0 0 0 (1),
    tm 0 1 1 0 0 (-1)]

/-- Chart core 139 of the barycentric order chart 43210,
homogenized to degree 2. -/
def chartCore139 : Poly :=
  [tm 2 0 0 0 0 (1),
    tm 0 0 1 1 0 (-1)]

/-- Chart core 140 of the barycentric order chart 43210,
homogenized to degree 12. -/
def chartCore140 : Poly :=
  [tm 11 0 0 1 0 (1),
    tm 10 1 0 1 0 (-1),
    tm 9 1 0 1 1 (-1),
    tm 9 1 1 1 0 (2),
    tm 8 1 1 2 0 (-1),
    tm 10 2 0 0 0 (1),
    tm 9 2 0 1 0 (-1),
    tm 7 2 1 1 1 (-1),
    tm 7 2 1 2 0 (-2),
    tm 6 2 1 2 1 (-2),
    tm 5 2 1 2 2 (-1),
    tm 7 2 2 1 0 (1),
    tm 6 2 2 2 0 (-1),
    tm 5 2 2 3 0 (-1),
    tm 4 2 2 3 1 (-2),
    tm 3 2 2 3 2 (-1),
    tm 8 3 1 0 0 (1),
    tm 7 3 1 1 0 (-1),
    tm 6 3 1 1 1 (1),
    tm 6 3 1 2 0 (-1),
    tm 5 3 1 2 1 (-1),
    tm 6 3 2 1 0 (1),
    tm 5 3 2 2 0 (-2),
    tm 4 3 2 3 0 (-2),
    tm 3 3 2 3 1 (-3),
    tm 2 3 2 3 2 (-1),
    tm 3 3 3 3 0 (-1),
    tm 2 3 3 3 1 (-1),
    tm 2 3 3 4 0 (-1),
    tm 1 3 3 4 1 (-2),
    tm 0 3 3 4 2 (-1)]

/-- Chart core 141 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore141 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 8 0 0 1 0 (-1),
    tm 8 0 1 0 0 (1),
    tm 7 0 1 1 0 (1),
    tm 6 0 1 1 1 (1),
    tm 6 0 1 2 0 (-1),
    tm 5 0 1 2 1 (-1),
    tm 8 1 0 0 0 (1),
    tm 6 1 0 1 1 (1),
    tm 7 1 1 0 0 (2),
    tm 5 1 1 1 1 (2),
    tm 4 1 1 2 1 (1),
    tm 3 1 1 2 2 (1),
    tm 6 1 2 0 0 (2),
    tm 5 1 2 1 0 (2),
    tm 4 1 2 1 1 (3),
    tm 4 1 2 2 0 (-1),
    tm 2 1 2 2 2 (1),
    tm 7 2 0 0 0 (-1),
    tm 6 2 1 0 0 (1),
    tm 5 2 1 1 0 (-2),
    tm 5 2 2 0 0 (1),
    tm 4 2 2 1 0 (1),
    tm 3 2 2 1 1 (2),
    tm 3 2 2 2 0 (-1),
    tm 1 2 2 2 2 (1),
    tm 4 2 3 0 0 (1),
    tm 3 2 3 1 0 (1),
    tm 2 2 3 1 1 (2),
    tm 1 2 3 2 1 (1),
    tm 0 2 3 2 2 (1)]

/-- Chart core 142 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore142 : Poly :=
  [tm 9 0 1 1 0 (1),
    tm 7 1 1 1 1 (-1),
    tm 7 1 2 1 0 (2),
    tm 5 1 2 2 1 (1),
    tm 9 2 0 0 0 (-1),
    tm 7 2 1 1 0 (-2),
    tm 6 2 1 1 1 (-1),
    tm 5 2 2 1 1 (-2),
    tm 5 2 2 2 0 (-1),
    tm 4 2 2 2 1 (-1),
    tm 3 2 2 2 2 (-1),
    tm 5 2 3 1 0 (1),
    tm 3 2 3 2 1 (1),
    tm 8 3 0 0 0 (-1),
    tm 7 3 1 0 0 (-1),
    tm 6 3 1 1 0 (-2),
    tm 5 3 1 1 1 (-2),
    tm 5 3 2 1 0 (-2),
    tm 4 3 2 1 1 (-1),
    tm 4 3 2 2 0 (-1),
    tm 3 3 2 2 1 (-3),
    tm 2 3 2 2 2 (-1),
    tm 3 3 3 1 1 (-1),
    tm 3 3 3 2 0 (-1),
    tm 2 3 3 2 1 (-1),
    tm 1 3 3 2 2 (-1),
    tm 1 3 3 3 1 (-1),
    tm 0 3 3 3 2 (-1)]

/-- Chart core 143 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore143 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 1 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (1),
    tm 7 1 1 1 1 (2),
    tm 8 2 1 0 0 (2),
    tm 6 2 1 1 1 (1),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (3),
    tm 4 2 2 2 1 (1),
    tm 3 2 2 2 2 (1),
    tm 5 3 1 1 1 (1),
    tm 6 3 2 0 0 (1),
    tm 4 3 2 1 1 (1),
    tm 3 3 2 2 1 (2),
    tm 2 3 2 2 2 (1),
    tm 4 3 3 1 0 (1),
    tm 3 3 3 1 1 (1),
    tm 2 3 3 2 1 (1),
    tm 1 3 3 2 2 (1),
    tm 1 3 3 3 1 (1),
    tm 0 3 3 3 2 (1),
    tm 6 4 1 0 0 (-1),
    tm 4 4 2 1 0 (-2),
    tm 3 4 2 1 1 (-1),
    tm 2 4 3 2 0 (-1),
    tm 1 4 3 2 1 (-1)]

/-- Chart core 144 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore144 : Poly :=
  [tm 8 0 0 1 0 (1),
    tm 6 0 1 2 0 (1),
    tm 6 1 0 1 1 (-1),
    tm 6 1 1 1 0 (1),
    tm 4 1 1 2 1 (-1),
    tm 4 1 2 2 0 (1),
    tm 7 2 0 0 0 (1),
    tm 5 2 1 1 0 (2),
    tm 3 2 1 2 1 (1),
    tm 3 2 2 2 0 (1),
    tm 1 2 2 3 1 (1),
    tm 0 2 2 3 2 (1)]

/-- Chart core 145 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore145 : Poly :=
  [tm 7 0 0 1 0 (1),
    tm 5 1 0 1 1 (-1),
    tm 5 1 1 1 0 (2),
    tm 4 1 1 1 1 (1),
    tm 6 2 0 0 0 (1),
    tm 4 2 1 1 0 (1),
    tm 3 2 1 1 1 (-1),
    tm 3 2 2 1 0 (1),
    tm 2 2 2 1 1 (1),
    tm 0 2 2 2 2 (1),
    tm 4 3 1 0 0 (1),
    tm 2 3 2 1 0 (1)]

/-- Chart core 146 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore146 : Poly :=
  [tm 4 0 0 1 0 (1),
    tm 2 1 0 1 1 (-1),
    tm 2 1 1 1 0 (1),
    tm 0 1 1 2 1 (-1),
    tm 3 2 0 0 0 (1),
    tm 1 2 1 1 0 (1)]

/-- Chart core 147 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore147 : Poly :=
  [tm 4 0 0 1 0 (1),
    tm 2 1 0 1 1 (-1),
    tm 2 1 1 1 0 (1),
    tm 3 2 0 0 0 (1),
    tm 1 2 1 1 0 (1),
    tm 0 2 1 1 1 (-1)]

/-- Chart core 148 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore148 : Poly :=
  [tm 13 0 0 0 0 (1),
    tm 11 1 1 0 0 (2),
    tm 10 1 1 1 0 (1),
    tm 9 1 1 1 1 (2),
    tm 8 1 2 2 0 (1),
    tm 7 1 2 2 1 (1),
    tm 10 2 1 0 0 (-1),
    tm 9 2 1 1 0 (1),
    tm 9 2 2 0 0 (1),
    tm 7 2 2 1 1 (2),
    tm 7 2 2 2 0 (2),
    tm 6 2 2 2 1 (2),
    tm 5 2 2 2 2 (1),
    tm 6 2 3 2 0 (1),
    tm 5 2 3 2 1 (1),
    tm 5 2 3 3 0 (1),
    tm 4 2 3 3 1 (2),
    tm 3 2 3 3 2 (1),
    tm 8 3 2 0 0 (-1),
    tm 7 3 2 1 0 (1),
    tm 6 3 2 1 1 (-1),
    tm 6 3 2 2 0 (1),
    tm 5 3 2 2 1 (1),
    tm 6 3 3 1 0 (-1),
    tm 5 3 3 2 0 (2),
    tm 4 3 3 3 0 (2),
    tm 3 3 3 3 1 (3),
    tm 2 3 3 3 2 (1),
    tm 3 3 4 3 0 (1),
    tm 2 3 4 3 1 (1),
    tm 2 3 4 4 0 (1),
    tm 1 3 4 4 1 (2),
    tm 0 3 4 4 2 (1)]

/-- Chart core 149 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore149 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 9 0 1 0 0 (1),
    tm 8 0 1 1 0 (1),
    tm 7 0 1 1 1 (1),
    tm 8 0 2 0 0 (1),
    tm 7 0 2 1 0 (1),
    tm 6 0 2 1 1 (1),
    tm 8 1 1 0 0 (2),
    tm 6 1 1 1 1 (1),
    tm 7 1 2 0 0 (2),
    tm 6 1 2 1 0 (2),
    tm 5 1 2 1 1 (3),
    tm 4 1 2 2 1 (1),
    tm 3 1 2 2 2 (1),
    tm 6 1 3 0 0 (2),
    tm 5 1 3 1 0 (2),
    tm 4 1 3 1 1 (3),
    tm 3 1 3 2 1 (1),
    tm 2 1 3 2 2 (1),
    tm 7 2 1 0 0 (-1),
    tm 6 2 2 0 0 (1),
    tm 5 2 2 1 0 (-2),
    tm 5 2 3 0 0 (1),
    tm 4 2 3 1 0 (1),
    tm 3 2 3 1 1 (2),
    tm 3 2 3 2 0 (-1),
    tm 1 2 3 2 2 (1),
    tm 4 2 4 0 0 (1),
    tm 3 2 4 1 0 (1),
    tm 2 2 4 1 1 (2),
    tm 1 2 4 2 1 (1),
    tm 0 2 4 2 2 (1)]

/-- Chart core 150 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore150 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 1 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (1),
    tm 7 1 1 1 1 (2),
    tm 9 2 0 0 0 (1),
    tm 8 2 1 0 0 (2),
    tm 7 2 1 1 0 (2),
    tm 6 2 1 1 1 (2),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (3),
    tm 5 2 2 2 0 (1),
    tm 4 2 2 2 1 (2),
    tm 3 2 2 2 2 (1),
    tm 7 3 1 0 0 (1),
    tm 5 3 1 1 1 (1),
    tm 6 3 2 0 0 (1),
    tm 5 3 2 1 0 (2),
    tm 4 3 2 1 1 (2),
    tm 3 3 2 2 1 (2),
    tm 2 3 2 2 2 (1),
    tm 4 3 3 1 0 (1),
    tm 3 3 3 1 1 (1),
    tm 3 3 3 2 0 (1),
    tm 2 3 3 2 1 (2),
    tm 1 3 3 2 2 (1),
    tm 1 3 3 3 1 (1),
    tm 0 3 3 3 2 (1),
    tm 6 4 1 0 0 (-1),
    tm 4 4 2 1 0 (-2),
    tm 3 4 2 1 1 (-1),
    tm 2 4 3 2 0 (-1),
    tm 1 4 3 2 1 (-1)]

/-- Chart core 151 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore151 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 8 0 1 1 0 (1),
    tm 8 1 1 0 0 (1),
    tm 6 1 1 1 1 (1),
    tm 6 1 2 1 0 (1),
    tm 4 1 2 2 1 (1),
    tm 7 2 1 0 0 (-1),
    tm 5 2 2 1 0 (-2),
    tm 3 2 2 2 1 (-1),
    tm 3 2 3 2 0 (-1),
    tm 1 2 3 3 1 (-1),
    tm 0 2 3 3 2 (-1)]

/-- Chart core 152 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore152 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 7 1 1 0 0 (2),
    tm 5 1 1 1 1 (1),
    tm 4 1 2 1 1 (-1),
    tm 6 2 1 0 0 (-1),
    tm 5 2 2 0 0 (1),
    tm 4 2 2 1 0 (-1),
    tm 3 2 2 1 1 (1),
    tm 2 2 3 1 1 (-1),
    tm 0 2 3 2 2 (-1),
    tm 4 3 2 0 0 (-1),
    tm 2 3 3 1 0 (-1)]

/-- Chart core 153 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore153 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 4 1 1 0 0 (1),
    tm 2 1 1 1 1 (1),
    tm 0 1 2 2 1 (1),
    tm 3 2 1 0 0 (-1),
    tm 1 2 2 1 0 (-1)]

/-- Chart core 154 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore154 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 4 1 1 0 0 (1),
    tm 2 1 1 1 1 (1),
    tm 3 2 1 0 0 (-1),
    tm 1 2 2 1 0 (-1),
    tm 0 2 2 1 1 (1)]

/-- Chart core 155 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore155 : Poly :=
  [tm 11 0 1 1 0 (1),
    tm 12 1 0 0 0 (-1),
    tm 10 1 1 1 0 (-2),
    tm 9 1 1 1 1 (-1),
    tm 9 1 2 1 0 (2),
    tm 8 1 2 2 0 (-1),
    tm 10 2 1 0 0 (-1),
    tm 9 2 1 1 0 (-1),
    tm 8 2 1 1 1 (-1),
    tm 8 2 2 1 0 (-2),
    tm 7 2 2 1 1 (-1),
    tm 7 2 2 2 0 (-2),
    tm 6 2 2 2 1 (-3),
    tm 5 2 2 2 2 (-1),
    tm 7 2 3 1 0 (1),
    tm 6 2 3 2 0 (-1),
    tm 5 2 3 3 0 (-1),
    tm 4 2 3 3 1 (-2),
    tm 3 2 3 3 2 (-1),
    tm 7 3 2 1 0 (-1),
    tm 6 3 2 2 0 (-1),
    tm 5 3 2 2 1 (-1),
    tm 5 3 3 2 0 (-2),
    tm 4 3 3 2 1 (-1),
    tm 4 3 3 3 0 (-2),
    tm 3 3 3 3 1 (-3),
    tm 2 3 3 3 2 (-1),
    tm 3 3 4 3 0 (-1),
    tm 2 3 4 3 1 (-1),
    tm 2 3 4 4 0 (-1),
    tm 1 3 4 4 1 (-2),
    tm 0 3 4 4 2 (-1)]

/-- Chart core 156 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore156 : Poly :=
  [tm 9 0 1 0 0 (1),
    tm 8 0 1 1 0 (-1),
    tm 8 0 2 0 0 (1),
    tm 7 0 2 1 0 (1),
    tm 6 0 2 1 1 (1),
    tm 6 0 2 2 0 (-1),
    tm 5 0 2 2 1 (-1),
    tm 9 1 0 0 0 (1),
    tm 8 1 1 0 0 (1),
    tm 7 1 1 1 0 (2),
    tm 6 1 1 1 1 (2),
    tm 7 1 2 0 0 (2),
    tm 5 1 2 1 1 (2),
    tm 5 1 2 2 0 (1),
    tm 4 1 2 2 1 (2),
    tm 3 1 2 2 2 (1),
    tm 6 1 3 0 0 (2),
    tm 5 1 3 1 0 (2),
    tm 4 1 3 1 1 (3),
    tm 4 1 3 2 0 (-1),
    tm 2 1 3 2 2 (1),
    tm 6 2 2 0 0 (1),
    tm 4 2 2 1 1 (1),
    tm 5 2 3 0 0 (1),
    tm 4 2 3 1 0 (1),
    tm 3 2 3 1 1 (2),
    tm 2 2 3 2 1 (1),
    tm 1 2 3 2 2 (1),
    tm 4 2 4 0 0 (1),
    tm 3 2 4 1 0 (1),
    tm 2 2 4 1 1 (2),
    tm 1 2 4 2 1 (1),
    tm 0 2 4 2 2 (1)]

/-- Chart core 157 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore157 : Poly :=
  [tm 9 0 1 1 0 (1),
    tm 10 1 0 0 0 (-1),
    tm 8 1 1 1 0 (-1),
    tm 7 1 1 1 1 (-1),
    tm 7 1 2 1 0 (2),
    tm 5 1 2 2 1 (1),
    tm 9 2 0 0 0 (-1),
    tm 8 2 1 0 0 (-2),
    tm 7 2 1 1 0 (-2),
    tm 6 2 1 1 1 (-2),
    tm 6 2 2 1 0 (-2),
    tm 5 2 2 1 1 (-2),
    tm 5 2 2 2 0 (-1),
    tm 4 2 2 2 1 (-2),
    tm 3 2 2 2 2 (-1),
    tm 5 2 3 1 0 (1),
    tm 3 2 3 2 1 (1),
    tm 8 3 0 0 0 (-1),
    tm 7 3 1 0 0 (-1),
    tm 6 3 1 1 0 (-2),
    tm 5 3 1 1 1 (-2),
    tm 6 3 2 0 0 (-1),
    tm 5 3 2 1 0 (-2),
    tm 4 3 2 1 1 (-2),
    tm 4 3 2 2 0 (-1),
    tm 3 3 2 2 1 (-3),
    tm 2 3 2 2 2 (-1),
    tm 4 3 3 1 0 (-1),
    tm 3 3 3 1 1 (-1),
    tm 3 3 3 2 0 (-1),
    tm 2 3 3 2 1 (-2),
    tm 1 3 3 2 2 (-1),
    tm 1 3 3 3 1 (-1),
    tm 0 3 3 3 2 (-1)]

/-- Chart core 158 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore158 : Poly :=
  [tm 8 0 1 1 0 (1),
    tm 6 0 2 2 0 (1),
    tm 9 1 0 0 0 (-1),
    tm 7 1 1 1 0 (-2),
    tm 6 1 1 1 1 (-1),
    tm 6 1 2 1 0 (1),
    tm 5 1 2 2 0 (-1),
    tm 4 1 2 2 1 (-1),
    tm 4 1 3 2 0 (1),
    tm 3 2 2 2 1 (1),
    tm 1 2 3 3 1 (1),
    tm 0 2 3 3 2 (1)]

/-- Chart core 159 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore159 : Poly :=
  [tm 7 0 1 1 0 (1),
    tm 8 1 0 0 0 (-1),
    tm 6 1 1 1 0 (-1),
    tm 5 1 1 1 1 (-1),
    tm 5 1 2 1 0 (2),
    tm 4 1 2 1 1 (1),
    tm 6 2 1 0 0 (-1),
    tm 4 2 2 1 0 (-1),
    tm 3 2 2 1 1 (-1),
    tm 3 2 3 1 0 (1),
    tm 2 2 3 1 1 (1),
    tm 0 2 3 2 2 (1)]

/-- Chart core 160 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore160 : Poly :=
  [tm 4 0 1 1 0 (1),
    tm 5 1 0 0 0 (-1),
    tm 3 1 1 1 0 (-1),
    tm 2 1 1 1 1 (-1),
    tm 2 1 2 1 0 (1),
    tm 0 1 2 2 1 (-1)]

/-- Chart core 161 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore161 : Poly :=
  [tm 4 0 1 1 0 (1),
    tm 5 1 0 0 0 (-1),
    tm 3 1 1 1 0 (-1),
    tm 2 1 1 1 1 (-1),
    tm 2 1 2 1 0 (1),
    tm 0 2 2 1 1 (-1)]

/-- Chart core 162 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore162 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 8 0 1 1 0 (1),
    tm 9 1 0 0 0 (1),
    tm 8 1 1 0 0 (1),
    tm 7 1 1 1 0 (2),
    tm 6 1 1 1 1 (1),
    tm 6 1 2 1 0 (1),
    tm 5 1 2 2 0 (1),
    tm 4 1 2 2 1 (1),
    tm 3 2 2 2 1 (-1),
    tm 1 2 3 3 1 (-1),
    tm 0 2 3 3 2 (-1)]

/-- Chart core 163 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore163 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 8 1 0 0 0 (1),
    tm 7 1 1 0 0 (2),
    tm 6 1 1 1 0 (1),
    tm 5 1 1 1 1 (1),
    tm 4 1 2 1 1 (-1),
    tm 6 2 1 0 0 (1),
    tm 5 2 2 0 0 (1),
    tm 4 2 2 1 0 (1),
    tm 3 2 2 1 1 (1),
    tm 2 2 3 1 1 (-1),
    tm 0 2 3 2 2 (-1)]

/-- Chart core 164 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore164 : Poly :=
  [tm 11 0 1 1 0 (1),
    tm 12 1 0 0 0 (-1),
    tm 11 1 1 0 0 (-1),
    tm 10 1 1 1 0 (-2),
    tm 9 1 1 1 1 (-2),
    tm 9 1 2 1 0 (2),
    tm 8 1 2 2 0 (-1),
    tm 11 2 0 0 0 (-1),
    tm 10 2 1 0 0 (-1),
    tm 9 2 1 1 0 (-3),
    tm 8 2 1 1 1 (-2),
    tm 9 2 2 0 0 (-2),
    tm 8 2 2 1 0 (-2),
    tm 7 2 2 1 1 (-4),
    tm 7 2 2 2 0 (-3),
    tm 6 2 2 2 1 (-4),
    tm 5 2 2 2 2 (-2),
    tm 7 2 3 1 0 (1),
    tm 6 2 3 2 0 (-1),
    tm 5 2 3 3 0 (-1),
    tm 4 2 3 3 1 (-2),
    tm 3 2 3 3 2 (-1),
    tm 9 3 1 0 0 (-1),
    tm 8 3 1 1 0 (-1),
    tm 7 3 1 1 1 (-1),
    tm 7 3 2 1 0 (-3),
    tm 6 3 2 1 1 (-1),
    tm 6 3 2 2 0 (-3),
    tm 5 3 2 2 1 (-4),
    tm 4 3 2 2 2 (-1),
    tm 7 3 3 0 0 (-1),
    tm 5 3 3 1 1 (-2),
    tm 5 3 3 2 0 (-3),
    tm 4 3 3 2 1 (-2),
    tm 3 3 3 2 2 (-1),
    tm 4 3 3 3 0 (-3),
    tm 3 3 3 3 1 (-5),
    tm 2 3 3 3 2 (-2),
    tm 3 3 4 3 0 (-1),
    tm 2 3 4 3 1 (-1),
    tm 2 3 4 4 0 (-1),
    tm 1 3 4 4 1 (-2),
    tm 0 3 4 4 2 (-1)]

/-- Chart core 165 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore165 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 0 1 0 0 (1),
    tm 9 0 1 1 0 (2),
    tm 8 0 1 1 1 (1),
    tm 8 0 1 2 0 (-1),
    tm 8 0 2 1 0 (1),
    tm 7 0 2 2 0 (1),
    tm 6 0 2 2 1 (1),
    tm 6 0 2 3 0 (-1),
    tm 5 0 2 3 1 (-1),
    tm 10 1 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (3),
    tm 7 1 1 1 1 (2),
    tm 6 1 1 2 1 (1),
    tm 8 1 2 0 0 (2),
    tm 7 1 2 1 0 (4),
    tm 6 1 2 1 1 (3),
    tm 6 1 2 2 0 (1),
    tm 5 1 2 2 1 (4),
    tm 4 1 2 2 2 (1),
    tm 4 1 2 3 1 (1),
    tm 3 1 2 3 2 (1),
    tm 6 1 3 1 0 (2),
    tm 5 1 3 2 0 (2),
    tm 4 1 3 2 1 (3),
    tm 4 1 3 3 0 (-1),
    tm 2 1 3 3 2 (1),
    tm 8 2 1 0 0 (1),
    tm 6 2 1 1 1 (1),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (3),
    tm 5 2 2 1 1 (2),
    tm 4 2 2 2 1 (3),
    tm 3 2 2 2 2 (1),
    tm 6 2 3 0 0 (1),
    tm 5 2 3 1 0 (2),
    tm 4 2 3 1 1 (2),
    tm 4 2 3 2 0 (2),
    tm 3 2 3 2 1 (4),
    tm 2 2 3 2 2 (1),
    tm 2 2 3 3 1 (2),
    tm 1 2 3 3 2 (2),
    tm 4 2 4 1 0 (1),
    tm 3 2 4 2 0 (1),
    tm 2 2 4 2 1 (2),
    tm 1 2 4 3 1 (1),
    tm 0 2 4 3 2 (1)]

/-- Chart core 166 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore166 : Poly :=
  [tm 9 0 2 2 0 (1),
    tm 9 1 2 1 0 (-1),
    tm 7 1 2 2 1 (-1),
    tm 7 1 3 2 0 (2),
    tm 5 1 3 3 1 (1),
    tm 11 2 0 0 0 (-1),
    tm 10 2 1 0 0 (-1),
    tm 9 2 1 1 0 (-3),
    tm 8 2 1 1 1 (-1),
    tm 8 2 2 1 0 (-2),
    tm 7 2 2 1 1 (-1),
    tm 7 2 2 2 0 (-3),
    tm 6 2 2 2 1 (-2),
    tm 7 2 3 1 0 (-2),
    tm 6 2 3 2 0 (-1),
    tm 5 2 3 2 1 (-4),
    tm 5 2 3 3 0 (-1),
    tm 4 2 3 3 1 (-1),
    tm 3 2 3 3 2 (-1),
    tm 5 2 4 2 0 (1),
    tm 3 2 4 3 1 (1),
    tm 10 3 0 0 0 (-1),
    tm 9 3 1 0 0 (-1),
    tm 8 3 1 1 0 (-3),
    tm 7 3 1 1 1 (-2),
    tm 8 3 2 0 0 (-1),
    tm 7 3 2 1 0 (-3),
    tm 6 3 2 1 1 (-2),
    tm 6 3 2 2 0 (-3),
    tm 5 3 2 2 1 (-5),
    tm 4 3 2 2 2 (-1),
    tm 6 3 3 1 0 (-2),
    tm 5 3 3 1 1 (-1),
    tm 5 3 3 2 0 (-3),
    tm 4 3 3 2 1 (-4),
    tm 3 3 3 2 2 (-1),
    tm 4 3 3 3 0 (-1),
    tm 3 3 3 3 1 (-4),
    tm 2 3 3 3 2 (-2),
    tm 5 3 4 1 0 (-1),
    tm 4 3 4 2 0 (-1),
    tm 3 3 4 2 1 (-3),
    tm 3 3 4 3 0 (-1),
    tm 2 3 4 3 1 (-2),
    tm 1 3 4 3 2 (-2),
    tm 1 3 4 4 1 (-1),
    tm 0 3 4 4 2 (-1)]

/-- Chart core 167 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore167 : Poly :=
  [tm 6 0 0 1 0 (1),
    tm 6 1 0 0 0 (-1),
    tm 4 1 0 1 1 (-1),
    tm 4 1 1 1 0 (1),
    tm 3 2 0 1 1 (1),
    tm 4 2 1 0 0 (-1),
    tm 2 2 1 1 1 (-1),
    tm 1 2 1 2 1 (1),
    tm 0 2 1 2 2 (1)]

/-- Chart core 168 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore168 : Poly :=
  [tm 7 0 0 1 0 (1),
    tm 7 1 0 0 0 (-1),
    tm 6 1 0 0 1 (1),
    tm 5 1 0 1 1 (-1),
    tm 5 1 1 1 0 (2),
    tm 4 1 1 1 1 (1),
    tm 5 2 1 0 0 (-2),
    tm 4 2 1 0 1 (1),
    tm 3 2 1 1 1 (-2),
    tm 2 2 1 1 2 (1),
    tm 3 2 2 1 0 (1),
    tm 2 2 2 1 1 (1),
    tm 0 2 2 2 2 (1),
    tm 3 3 2 0 0 (-1),
    tm 1 3 2 1 1 (-1)]

/-- Chart core 169 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore169 : Poly :=
  [tm 4 0 0 1 0 (1),
    tm 4 1 0 0 0 (-1),
    tm 2 1 0 1 1 (-2),
    tm 2 1 1 1 0 (1),
    tm 0 1 1 2 1 (-1),
    tm 2 2 1 0 0 (-1),
    tm 0 2 1 1 1 (-1)]

/-- Chart core 170 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore170 : Poly :=
  [tm 4 0 0 1 0 (1),
    tm 4 1 0 0 0 (-1),
    tm 2 1 0 1 1 (-1),
    tm 2 1 1 1 0 (1),
    tm 2 2 0 0 1 (-1),
    tm 2 2 1 0 0 (-1),
    tm 0 2 1 1 1 (-2)]

/-- Chart core 171 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore171 : Poly :=
  [tm 12 0 0 1 0 (1),
    tm 10 0 1 2 0 (1),
    tm 9 0 1 2 1 (1),
    tm 11 1 0 1 0 (1),
    tm 10 1 1 1 0 (3),
    tm 9 1 1 1 1 (1),
    tm 9 1 1 2 0 (2),
    tm 8 1 1 2 1 (2),
    tm 8 1 2 2 0 (3),
    tm 7 1 2 2 1 (3),
    tm 7 1 2 3 0 (1),
    tm 6 1 2 3 1 (2),
    tm 5 1 2 3 2 (1),
    tm 10 2 1 0 0 (-1),
    tm 9 2 1 1 0 (2),
    tm 8 2 1 2 0 (1),
    tm 7 2 1 2 1 (1),
    tm 8 2 2 1 0 (1),
    tm 7 2 2 1 1 (1),
    tm 7 2 2 2 0 (4),
    tm 6 2 2 2 1 (4),
    tm 5 2 2 2 2 (1),
    tm 6 2 2 3 0 (2),
    tm 5 2 2 3 1 (3),
    tm 4 2 2 3 2 (1),
    tm 6 2 3 2 0 (2),
    tm 5 2 3 2 1 (2),
    tm 5 2 3 3 0 (2),
    tm 4 2 3 3 1 (4),
    tm 3 2 3 3 2 (2),
    tm 4 2 3 4 0 (1),
    tm 3 2 3 4 1 (2),
    tm 2 2 3 4 2 (1),
    tm 8 3 2 0 0 (-1),
    tm 7 3 2 1 0 (1),
    tm 6 3 2 1 1 (-1),
    tm 6 3 2 2 0 (1),
    tm 5 3 2 2 1 (1),
    tm 6 3 3 1 0 (-1),
    tm 5 3 3 2 0 (2),
    tm 4 3 3 3 0 (2),
    tm 3 3 3 3 1 (3),
    tm 2 3 3 3 2 (1),
    tm 3 3 4 3 0 (1),
    tm 2 3 4 3 1 (1),
    tm 2 3 4 4 0 (1),
    tm 1 3 4 4 1 (2),
    tm 0 3 4 4 2 (1)]

/-- Chart core 172 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore172 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 0 1 0 0 (1),
    tm 9 0 1 1 0 (1),
    tm 8 0 1 1 1 (1),
    tm 10 1 0 0 0 (1),
    tm 9 1 1 0 0 (3),
    tm 8 1 1 1 0 (1),
    tm 7 1 1 1 1 (2),
    tm 8 1 2 0 0 (3),
    tm 7 1 2 1 0 (3),
    tm 6 1 2 1 1 (4),
    tm 5 1 2 2 1 (1),
    tm 4 1 2 2 2 (1),
    tm 8 2 1 0 0 (2),
    tm 7 2 1 1 0 (1),
    tm 6 2 1 1 1 (2),
    tm 7 2 2 0 0 (3),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (4),
    tm 5 2 2 2 0 (2),
    tm 4 2 2 2 1 (4),
    tm 3 2 2 2 2 (2),
    tm 6 2 3 0 0 (3),
    tm 5 2 3 1 0 (3),
    tm 4 2 3 1 1 (5),
    tm 3 2 3 2 1 (2),
    tm 2 2 3 2 2 (2),
    tm 3 2 3 3 0 (1),
    tm 2 2 3 3 1 (2),
    tm 1 2 3 3 2 (1),
    tm 7 3 1 0 0 (-1),
    tm 6 3 2 0 0 (1),
    tm 5 3 2 1 0 (-2),
    tm 5 3 3 0 0 (1),
    tm 4 3 3 1 0 (1),
    tm 3 3 3 1 1 (2),
    tm 3 3 3 2 0 (-1),
    tm 1 3 3 2 2 (1),
    tm 4 3 4 0 0 (1),
    tm 3 3 4 1 0 (1),
    tm 2 3 4 1 1 (2),
    tm 1 3 4 2 1 (1),
    tm 0 3 4 2 2 (1)]

/-- Chart core 173 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore173 : Poly :=
  [tm 13 0 0 0 0 (1),
    tm 12 1 0 0 0 (1),
    tm 11 1 1 0 0 (3),
    tm 10 1 1 1 0 (1),
    tm 9 1 1 1 1 (2),
    tm 10 2 1 0 0 (3),
    tm 9 2 1 1 0 (1),
    tm 8 2 1 1 1 (1),
    tm 9 2 2 0 0 (3),
    tm 8 2 2 1 0 (3),
    tm 7 2 2 1 1 (5),
    tm 7 2 2 2 0 (1),
    tm 6 2 2 2 1 (2),
    tm 5 2 2 2 2 (1),
    tm 8 3 2 0 0 (3),
    tm 7 3 2 1 0 (2),
    tm 6 3 2 1 1 (2),
    tm 5 3 2 2 1 (1),
    tm 7 3 3 0 0 (1),
    tm 6 3 3 1 0 (3),
    tm 5 3 3 1 1 (4),
    tm 5 3 3 2 0 (2),
    tm 4 3 3 2 1 (4),
    tm 3 3 3 2 2 (2),
    tm 3 3 3 3 1 (1),
    tm 2 3 3 3 2 (1),
    tm 6 4 2 1 0 (1),
    tm 5 4 2 1 1 (1),
    tm 6 4 3 0 0 (1),
    tm 5 4 3 1 0 (1),
    tm 4 4 3 1 1 (1),
    tm 4 4 3 2 0 (2),
    tm 3 4 3 2 1 (4),
    tm 2 4 3 2 2 (1),
    tm 4 4 4 1 0 (1),
    tm 3 4 4 1 1 (1),
    tm 3 4 4 2 0 (1),
    tm 2 4 4 2 1 (2),
    tm 1 4 4 2 2 (1),
    tm 2 4 4 3 0 (1),
    tm 1 4 4 3 1 (3),
    tm 0 4 4 3 2 (2),
    tm 6 5 2 0 0 (-1),
    tm 4 5 3 1 0 (-2),
    tm 3 5 3 1 1 (-1),
    tm 2 5 4 2 0 (-1),
    tm 1 5 4 2 1 (-1)]

/-- Chart core 174 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore174 : Poly :=
  [tm 7 0 0 1 0 (1),
    tm 6 0 0 1 1 (1),
    tm 5 0 0 2 1 (-1),
    tm 5 0 1 2 0 (2),
    tm 4 0 1 2 1 (2),
    tm 3 0 1 3 1 (-1),
    tm 2 0 1 3 2 (-1),
    tm 3 0 2 3 0 (1),
    tm 2 0 2 3 1 (1),
    tm 7 1 0 0 0 (-1),
    tm 5 1 1 1 0 (-2),
    tm 3 1 1 2 1 (-1),
    tm 3 1 2 2 0 (-1),
    tm 1 1 2 3 1 (-1),
    tm 0 1 2 3 2 (-1)]

/-- Chart core 175 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore175 : Poly :=
  [tm 4 0 0 1 1 (1),
    tm 4 1 0 1 0 (-1),
    tm 3 1 0 1 1 (-1),
    tm 2 1 1 1 1 (1),
    tm 2 1 1 2 0 (-1),
    tm 1 1 1 2 1 (-1),
    tm 0 1 1 2 2 (1),
    tm 4 2 0 0 0 (1),
    tm 2 2 1 1 0 (1)]

/-- Chart core 176 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore176 : Poly :=
  [tm 2 0 0 2 1 (1),
    tm 3 1 0 1 0 (1),
    tm 2 1 0 1 1 (1),
    tm 1 1 1 2 0 (1),
    tm 0 1 1 2 1 (2),
    tm 3 2 0 0 0 (-1),
    tm 1 2 1 1 0 (-1)]

/-- Chart core 177 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore177 : Poly :=
  [tm 3 0 0 1 0 (1),
    tm 2 0 0 1 1 (2),
    tm 1 0 1 2 0 (1),
    tm 0 0 1 2 1 (1),
    tm 3 1 0 0 0 (-1),
    tm 1 1 1 1 0 (-1),
    tm 0 1 1 1 1 (1)]

/-- Chart core 178 of the barycentric order chart 43210,
homogenized to degree 14. -/
def chartCore178 : Poly :=
  [tm 13 0 0 1 0 (1),
    tm 13 1 0 0 0 (-1),
    tm 12 1 0 1 0 (1),
    tm 11 1 1 1 0 (2),
    tm 10 1 1 2 0 (2),
    tm 9 1 1 2 1 (3),
    tm 8 1 2 3 0 (1),
    tm 7 1 2 3 1 (1),
    tm 11 2 0 1 0 (1),
    tm 11 2 1 0 0 (-2),
    tm 10 2 1 1 0 (1),
    tm 9 2 1 1 1 (-1),
    tm 9 2 1 2 0 (3),
    tm 8 2 1 2 1 (2),
    tm 9 2 2 1 0 (1),
    tm 8 2 2 2 0 (2),
    tm 7 2 2 2 1 (4),
    tm 7 2 2 3 0 (3),
    tm 6 2 2 3 1 (4),
    tm 5 2 2 3 2 (2),
    tm 6 2 3 3 0 (1),
    tm 5 2 3 3 1 (1),
    tm 5 2 3 4 0 (1),
    tm 4 2 3 4 1 (2),
    tm 3 2 3 4 2 (1),
    tm 9 3 1 1 0 (1),
    tm 8 3 1 2 0 (1),
    tm 7 3 1 2 1 (1),
    tm 9 3 2 0 0 (-1),
    tm 7 3 2 1 1 (-1),
    tm 7 3 2 2 0 (3),
    tm 6 3 2 2 1 (1),
    tm 6 3 2 3 0 (3),
    tm 5 3 2 3 1 (4),
    tm 4 3 2 3 2 (1),
    tm 5 3 3 2 1 (1),
    tm 5 3 3 3 0 (3),
    tm 4 3 3 3 1 (2),
    tm 3 3 3 3 2 (1),
    tm 4 3 3 4 0 (3),
    tm 3 3 3 4 1 (5),
    tm 2 3 3 4 2 (2),
    tm 3 3 4 4 0 (1),
    tm 2 3 4 4 1 (1),
    tm 2 3 4 5 0 (1),
    tm 1 3 4 5 1 (2),
    tm 0 3 4 5 2 (1)]

/-- Chart core 179 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore179 : Poly :=
  [tm 11 0 1 1 0 (1),
    tm 11 1 1 0 0 (-1),
    tm 9 1 2 1 0 (2),
    tm 7 1 2 2 1 (2),
    tm 11 2 0 0 0 (1),
    tm 10 2 1 0 0 (1),
    tm 9 2 1 1 0 (3),
    tm 8 2 1 1 1 (1),
    tm 9 2 2 0 0 (-2),
    tm 8 2 2 1 0 (2),
    tm 7 2 2 2 0 (3),
    tm 6 2 2 2 1 (2),
    tm 7 2 3 1 0 (1),
    tm 6 2 3 2 0 (1),
    tm 5 2 3 2 1 (4),
    tm 5 2 3 3 0 (1),
    tm 4 2 3 3 1 (1),
    tm 3 2 3 3 2 (1),
    tm 10 3 0 0 0 (1),
    tm 9 3 1 0 0 (1),
    tm 8 3 1 1 0 (3),
    tm 7 3 1 1 1 (2),
    tm 8 3 2 0 0 (1),
    tm 7 3 2 1 0 (3),
    tm 6 3 2 1 1 (2),
    tm 6 3 2 2 0 (3),
    tm 5 3 2 2 1 (5),
    tm 4 3 2 2 2 (1),
    tm 7 3 3 0 0 (-1),
    tm 6 3 3 1 0 (2),
    tm 5 3 3 2 0 (3),
    tm 4 3 3 2 1 (4),
    tm 3 3 3 2 2 (1),
    tm 4 3 3 3 0 (1),
    tm 3 3 3 3 1 (4),
    tm 2 3 3 3 2 (2),
    tm 4 3 4 2 0 (1),
    tm 3 3 4 2 1 (2),
    tm 3 3 4 3 0 (1),
    tm 2 3 4 3 1 (2),
    tm 1 3 4 3 2 (2),
    tm 1 3 4 4 1 (1),
    tm 0 3 4 4 2 (1)]

/-- Chart core 180 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore180 : Poly :=
  [tm 13 0 0 0 0 (1),
    tm 11 0 1 1 0 (1),
    tm 12 1 0 0 0 (1),
    tm 11 1 1 0 0 (2),
    tm 10 1 1 1 0 (2),
    tm 9 1 1 1 1 (2),
    tm 9 1 2 1 0 (2),
    tm 8 1 2 2 0 (1),
    tm 7 1 2 2 1 (2),
    tm 10 2 1 0 0 (2),
    tm 9 2 1 1 0 (2),
    tm 8 2 1 1 1 (1),
    tm 9 2 2 0 0 (1),
    tm 8 2 2 1 0 (4),
    tm 7 2 2 1 1 (3),
    tm 7 2 2 2 0 (3),
    tm 6 2 2 2 1 (4),
    tm 5 2 2 2 2 (1),
    tm 7 2 3 1 0 (1),
    tm 6 2 3 2 0 (2),
    tm 5 2 3 2 1 (3),
    tm 5 2 3 3 0 (1),
    tm 4 2 3 3 1 (2),
    tm 3 2 3 3 2 (1),
    tm 9 3 1 0 0 (-1),
    tm 8 3 2 0 0 (1),
    tm 7 3 2 1 0 (1),
    tm 5 3 2 2 1 (2),
    tm 6 3 3 1 0 (2),
    tm 5 3 3 1 1 (1),
    tm 5 3 3 2 0 (3),
    tm 4 3 3 2 1 (4),
    tm 3 3 3 2 2 (1),
    tm 3 3 3 3 1 (3),
    tm 2 3 3 3 2 (2),
    tm 4 3 4 2 0 (1),
    tm 3 3 4 2 1 (1),
    tm 3 3 4 3 0 (1),
    tm 2 3 4 3 1 (2),
    tm 1 3 4 3 2 (1),
    tm 1 3 4 4 1 (1),
    tm 0 3 4 4 2 (1),
    tm 7 4 2 0 0 (-1),
    tm 5 4 3 1 0 (-1),
    tm 4 4 3 1 1 (-1),
    tm 3 4 3 2 1 (1),
    tm 1 4 4 3 1 (1),
    tm 0 4 4 3 2 (1)]

/-- Chart core 181 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore181 : Poly :=
  [tm 8 0 0 1 0 (1),
    tm 8 1 0 0 0 (-1),
    tm 6 1 1 1 0 (1),
    tm 4 1 1 2 1 (1),
    tm 6 2 1 0 0 (-1),
    tm 3 2 1 2 1 (-1),
    tm 2 2 2 2 1 (1),
    tm 1 2 2 3 1 (-1),
    tm 0 2 2 3 2 (-1)]

/-- Chart core 182 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore182 : Poly :=
  [tm 9 0 0 1 0 (1),
    tm 9 1 0 0 0 (-1),
    tm 7 1 1 1 0 (2),
    tm 6 1 1 1 1 (-1),
    tm 5 1 1 2 1 (1),
    tm 4 1 2 2 1 (-1),
    tm 7 2 1 0 0 (-2),
    tm 5 2 2 1 0 (1),
    tm 4 2 2 1 1 (-1),
    tm 3 2 2 2 1 (2),
    tm 2 2 2 2 2 (-1),
    tm 2 2 3 2 1 (-1),
    tm 0 2 3 3 2 (-1),
    tm 5 3 2 0 0 (-1),
    tm 1 3 3 2 1 (1)]

/-- Chart core 183 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore183 : Poly :=
  [tm 6 0 0 1 0 (1),
    tm 6 1 0 0 0 (-1),
    tm 4 1 1 1 0 (1),
    tm 2 1 1 2 1 (2),
    tm 0 1 2 3 1 (1),
    tm 4 2 1 0 0 (-1),
    tm 0 2 2 2 1 (1)]

/-- Chart core 184 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore184 : Poly :=
  [tm 6 0 0 1 0 (1),
    tm 6 1 0 0 0 (-1),
    tm 4 1 1 1 0 (1),
    tm 2 1 1 2 1 (1),
    tm 4 2 1 0 0 (-1),
    tm 2 2 1 1 1 (1),
    tm 0 2 2 2 1 (2)]

/-- Chart core 185 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore185 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 0 1 0 0 (1),
    tm 9 0 1 1 0 (1),
    tm 8 0 1 1 1 (1),
    tm 10 1 0 0 0 (1),
    tm 9 1 0 1 0 (-1),
    tm 9 1 1 0 0 (3),
    tm 8 1 1 1 0 (1),
    tm 7 1 1 1 1 (2),
    tm 7 1 1 2 0 (-2),
    tm 6 1 1 2 1 (-1),
    tm 8 1 2 0 0 (3),
    tm 7 1 2 1 0 (3),
    tm 6 1 2 1 1 (4),
    tm 5 1 2 2 1 (1),
    tm 4 1 2 2 2 (1),
    tm 5 1 2 3 0 (-1),
    tm 4 1 2 3 1 (-1),
    tm 9 2 0 0 0 (1),
    tm 8 2 1 0 0 (2),
    tm 7 2 1 1 0 (2),
    tm 6 2 1 1 1 (3),
    tm 7 2 2 0 0 (3),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (4),
    tm 5 2 2 2 0 (1),
    tm 4 2 2 2 1 (4),
    tm 3 2 2 2 2 (2),
    tm 6 2 3 0 0 (3),
    tm 5 2 3 1 0 (3),
    tm 4 2 3 1 1 (5),
    tm 3 2 3 2 1 (2),
    tm 2 2 3 2 2 (2),
    tm 2 2 3 3 1 (1),
    tm 1 2 3 3 2 (1),
    tm 6 3 2 0 0 (1),
    tm 4 3 2 1 1 (1),
    tm 5 3 3 0 0 (1),
    tm 4 3 3 1 0 (1),
    tm 3 3 3 1 1 (2),
    tm 2 3 3 2 1 (1),
    tm 1 3 3 2 2 (1),
    tm 4 3 4 0 0 (1),
    tm 3 3 4 1 0 (1),
    tm 2 3 4 1 1 (2),
    tm 1 3 4 2 1 (1),
    tm 0 3 4 2 2 (1)]

/-- Chart core 186 of the barycentric order chart 43210,
homogenized to degree 12. -/
def chartCore186 : Poly :=
  [tm 10 0 1 1 0 (1),
    tm 8 0 2 2 0 (1),
    tm 11 1 0 0 0 (-1),
    tm 10 1 1 0 0 (-2),
    tm 9 1 1 1 0 (-2),
    tm 8 1 1 1 1 (-1),
    tm 8 1 2 1 0 (-1),
    tm 7 1 2 1 1 (-2),
    tm 7 1 2 2 0 (-1),
    tm 6 1 3 2 0 (1),
    tm 5 1 3 2 1 (-1),
    tm 4 1 3 3 1 (1),
    tm 10 2 0 0 0 (-1),
    tm 9 2 1 0 0 (-2),
    tm 8 2 1 1 0 (-2),
    tm 7 2 1 1 1 (-2),
    tm 8 2 2 0 0 (-3),
    tm 7 2 2 1 0 (-4),
    tm 6 2 2 1 1 (-4),
    tm 6 2 2 2 0 (-1),
    tm 5 2 2 2 1 (-3),
    tm 4 2 2 2 2 (-1),
    tm 6 2 3 1 0 (-3),
    tm 5 2 3 1 1 (-3),
    tm 5 2 3 2 0 (-2),
    tm 4 2 3 2 1 (-4),
    tm 3 2 3 2 2 (-2),
    tm 3 2 3 3 1 (-1),
    tm 2 2 3 3 2 (-1),
    tm 3 2 4 2 1 (-1),
    tm 1 2 4 3 2 (-1),
    tm 8 3 1 0 0 (-1),
    tm 7 3 2 0 0 (-1),
    tm 6 3 2 1 0 (-2),
    tm 5 3 2 1 1 (-2),
    tm 6 3 3 0 0 (-1),
    tm 5 3 3 1 0 (-2),
    tm 4 3 3 1 1 (-2),
    tm 4 3 3 2 0 (-1),
    tm 3 3 3 2 1 (-3),
    tm 2 3 3 2 2 (-1),
    tm 4 3 4 1 0 (-1),
    tm 3 3 4 1 1 (-1),
    tm 3 3 4 2 0 (-1),
    tm 2 3 4 2 1 (-2),
    tm 1 3 4 2 2 (-1),
    tm 1 3 4 3 1 (-1),
    tm 0 3 4 3 2 (-1)]

/-- Chart core 187 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore187 : Poly :=
  [tm 13 0 0 0 0 (1),
    tm 12 1 0 0 0 (1),
    tm 11 1 1 0 0 (3),
    tm 10 1 1 1 0 (1),
    tm 9 1 1 1 1 (2),
    tm 10 2 1 0 0 (3),
    tm 9 2 1 1 0 (1),
    tm 8 2 1 1 1 (1),
    tm 9 2 2 0 0 (3),
    tm 8 2 2 1 0 (3),
    tm 7 2 2 1 1 (5),
    tm 7 2 2 2 0 (1),
    tm 6 2 2 2 1 (2),
    tm 5 2 2 2 2 (1),
    tm 8 3 1 1 0 (-1),
    tm 8 3 2 0 0 (3),
    tm 7 3 2 1 0 (2),
    tm 6 3 2 1 1 (2),
    tm 6 3 2 2 0 (-2),
    tm 7 3 3 0 0 (1),
    tm 6 3 3 1 0 (3),
    tm 5 3 3 1 1 (4),
    tm 5 3 3 2 0 (2),
    tm 4 3 3 2 1 (4),
    tm 3 3 3 2 2 (2),
    tm 4 3 3 3 0 (-1),
    tm 2 3 3 3 2 (1),
    tm 8 4 1 0 0 (1),
    tm 6 4 2 1 0 (2),
    tm 5 4 2 1 1 (2),
    tm 6 4 3 0 0 (1),
    tm 5 4 3 1 0 (1),
    tm 4 4 3 1 1 (1),
    tm 4 4 3 2 0 (1),
    tm 3 4 3 2 1 (4),
    tm 2 4 3 2 2 (1),
    tm 4 4 4 1 0 (1),
    tm 3 4 4 1 1 (1),
    tm 3 4 4 2 0 (1),
    tm 2 4 4 2 1 (2),
    tm 1 4 4 2 2 (1),
    tm 1 4 4 3 1 (2),
    tm 0 4 4 3 2 (2)]

/-- Chart core 188 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore188 : Poly :=
  [tm 9 0 0 1 0 (1),
    tm 7 0 1 2 0 (2),
    tm 5 0 2 3 0 (1),
    tm 9 1 0 0 0 (-1),
    tm 7 1 1 1 0 (-2),
    tm 6 1 1 1 1 (-1),
    tm 5 1 1 2 1 (1),
    tm 5 1 2 2 0 (-1),
    tm 4 1 2 2 1 (-2),
    tm 3 1 2 3 1 (1),
    tm 2 1 2 3 2 (1),
    tm 2 1 3 3 1 (-1),
    tm 3 2 2 2 1 (1),
    tm 1 2 3 3 1 (1),
    tm 0 2 3 3 2 (1)]

/-- Chart core 189 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore189 : Poly :=
  [tm 6 0 0 1 0 (1),
    tm 4 0 1 1 1 (1),
    tm 4 0 1 2 0 (1),
    tm 6 1 0 0 0 (-1),
    tm 4 1 1 1 0 (-1),
    tm 3 1 1 1 1 (-1),
    tm 2 1 2 1 1 (1),
    tm 1 1 2 2 1 (-1),
    tm 0 1 2 2 2 (1)]

/-- Chart core 190 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore190 : Poly :=
  [tm 5 0 0 1 0 (1),
    tm 3 0 1 2 0 (1),
    tm 2 0 1 2 1 (-1),
    tm 5 1 0 0 0 (-1),
    tm 3 1 1 1 0 (-1),
    tm 2 1 1 1 1 (-1),
    tm 0 1 2 2 1 (-2)]

/-- Chart core 191 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore191 : Poly :=
  [tm 5 0 0 1 0 (1),
    tm 3 0 1 2 0 (1),
    tm 5 1 0 0 0 (-1),
    tm 3 1 1 1 0 (-1),
    tm 2 1 1 1 1 (-2),
    tm 0 1 2 2 1 (-1),
    tm 0 2 2 1 1 (-1)]

/-- Chart core 192 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore192 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 1 0 0 0 (-1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (-1),
    tm 9 2 0 0 0 (-1),
    tm 8 2 1 0 0 (-1),
    tm 7 2 1 1 0 (-2),
    tm 6 2 1 1 1 (-2),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (-1),
    tm 5 2 2 2 0 (-1),
    tm 4 2 2 2 1 (-2),
    tm 3 2 2 2 2 (-1),
    tm 7 3 1 0 0 (-1),
    tm 6 3 1 1 0 (-1),
    tm 5 3 1 1 1 (-1),
    tm 5 3 2 1 0 (-2),
    tm 4 3 2 1 1 (-1),
    tm 4 3 2 2 0 (-2),
    tm 3 3 2 2 1 (-3),
    tm 2 3 2 2 2 (-1),
    tm 3 3 3 2 0 (-1),
    tm 2 3 3 2 1 (-1),
    tm 2 3 3 3 0 (-1),
    tm 1 3 3 3 1 (-2),
    tm 0 3 3 3 2 (-1)]

/-- Chart core 193 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore193 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 8 0 0 1 0 (-1),
    tm 8 0 1 0 0 (1),
    tm 7 0 1 1 0 (1),
    tm 6 0 1 1 1 (1),
    tm 6 0 1 2 0 (-1),
    tm 5 0 1 2 1 (-1),
    tm 8 1 0 0 0 (1),
    tm 7 1 1 0 0 (2),
    tm 5 1 1 1 1 (2),
    tm 6 1 2 0 0 (2),
    tm 5 1 2 1 0 (2),
    tm 4 1 2 1 1 (3),
    tm 4 1 2 2 0 (-1),
    tm 2 1 2 2 2 (1),
    tm 6 2 1 0 0 (1),
    tm 4 2 1 1 1 (1),
    tm 5 2 2 0 0 (1),
    tm 4 2 2 1 0 (1),
    tm 3 2 2 1 1 (2),
    tm 2 2 2 2 1 (1),
    tm 1 2 2 2 2 (1),
    tm 4 2 3 0 0 (1),
    tm 3 2 3 1 0 (1),
    tm 2 2 3 1 1 (2),
    tm 1 2 3 2 1 (1),
    tm 0 2 3 2 2 (1)]

/-- Chart core 194 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore194 : Poly :=
  [tm 9 0 1 1 0 (1),
    tm 7 1 2 1 0 (2),
    tm 5 1 2 2 1 (1),
    tm 9 2 0 0 0 (-1),
    tm 8 2 1 0 0 (-1),
    tm 7 2 1 1 0 (-2),
    tm 6 2 1 1 1 (-1),
    tm 6 2 2 1 0 (-1),
    tm 5 2 2 1 1 (-1),
    tm 5 2 2 2 0 (-1),
    tm 4 2 2 2 1 (-1),
    tm 5 2 3 1 0 (1),
    tm 3 2 3 2 1 (1),
    tm 8 3 0 0 0 (-1),
    tm 7 3 1 0 0 (-1),
    tm 6 3 1 1 0 (-2),
    tm 5 3 1 1 1 (-2),
    tm 6 3 2 0 0 (-1),
    tm 5 3 2 1 0 (-2),
    tm 4 3 2 1 1 (-2),
    tm 4 3 2 2 0 (-1),
    tm 3 3 2 2 1 (-3),
    tm 2 3 2 2 2 (-1),
    tm 4 3 3 1 0 (-1),
    tm 3 3 3 1 1 (-1),
    tm 3 3 3 2 0 (-1),
    tm 2 3 3 2 1 (-2),
    tm 1 3 3 2 2 (-1),
    tm 1 3 3 3 1 (-1),
    tm 0 3 3 3 2 (-1)]

/-- Chart core 195 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore195 : Poly :=
  [tm 4 0 0 0 0 (1),
    tm 2 1 1 0 0 (1),
    tm 0 2 1 0 1 (-1)]

/-- Chart core 196 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore196 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 8 0 1 1 0 (1),
    tm 8 1 1 0 0 (1),
    tm 6 1 2 1 0 (1),
    tm 3 2 2 2 1 (-1),
    tm 1 2 3 3 1 (-1),
    tm 0 2 3 3 2 (-1)]

/-- Chart core 197 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore197 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 7 1 1 0 0 (2),
    tm 4 1 2 1 1 (-1),
    tm 5 2 2 0 0 (1),
    tm 2 2 3 1 1 (-1),
    tm 0 2 3 2 2 (-1)]

/-- Chart core 198 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore198 : Poly :=
  [tm 4 0 0 0 0 (1),
    tm 2 0 1 1 0 (1),
    tm 3 1 0 0 0 (-1),
    tm 1 1 1 1 0 (-1),
    tm 0 1 1 1 1 (-1)]

/-- Chart core 199 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore199 : Poly :=
  [tm 4 0 0 0 0 (1),
    tm 3 0 0 1 0 (-1),
    tm 2 1 1 0 0 (1),
    tm 1 1 1 1 0 (-1),
    tm 0 1 1 1 1 (1)]

/-- Chart core 200 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore200 : Poly :=
  [tm 10 0 0 1 0 (1),
    tm 8 0 1 2 0 (1),
    tm 7 0 1 2 1 (1),
    tm 10 1 0 0 0 (-1),
    tm 9 1 0 1 0 (1),
    tm 7 1 1 2 0 (2),
    tm 6 1 1 2 1 (2),
    tm 6 1 2 2 0 (1),
    tm 5 1 2 2 1 (1),
    tm 5 1 2 3 0 (1),
    tm 4 1 2 3 1 (2),
    tm 3 1 2 3 2 (1),
    tm 8 2 1 0 0 (-1),
    tm 7 2 1 1 0 (1),
    tm 6 2 1 1 1 (-1),
    tm 6 2 1 2 0 (1),
    tm 5 2 1 2 1 (1),
    tm 6 2 2 1 0 (-1),
    tm 5 2 2 2 0 (2),
    tm 4 2 2 3 0 (2),
    tm 3 2 2 3 1 (3),
    tm 2 2 2 3 2 (1),
    tm 3 2 3 3 0 (1),
    tm 2 2 3 3 1 (1),
    tm 2 2 3 4 0 (1),
    tm 1 2 3 4 1 (2),
    tm 0 2 3 4 2 (1)]

/-- Chart core 201 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore201 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 8 0 1 0 0 (1),
    tm 7 0 1 1 0 (1),
    tm 6 0 1 1 1 (1),
    tm 8 1 0 0 0 (1),
    tm 7 1 1 0 0 (2),
    tm 6 1 1 1 0 (1),
    tm 5 1 1 1 1 (2),
    tm 6 1 2 0 0 (2),
    tm 5 1 2 1 0 (2),
    tm 4 1 2 1 1 (3),
    tm 3 1 2 2 1 (1),
    tm 2 1 2 2 2 (1),
    tm 7 2 0 0 0 (-1),
    tm 6 2 1 0 0 (1),
    tm 5 2 1 1 0 (-2),
    tm 5 2 2 0 0 (1),
    tm 4 2 2 1 0 (1),
    tm 3 2 2 1 1 (2),
    tm 3 2 2 2 0 (-1),
    tm 1 2 2 2 2 (1),
    tm 4 2 3 0 0 (1),
    tm 3 2 3 1 0 (1),
    tm 2 2 3 1 1 (2),
    tm 1 2 3 2 1 (1),
    tm 0 2 3 2 2 (1)]

/-- Chart core 202 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore202 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 1 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (1),
    tm 7 1 1 1 1 (2),
    tm 8 2 1 0 0 (2),
    tm 7 2 1 1 0 (1),
    tm 6 2 1 1 1 (1),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (3),
    tm 5 2 2 2 0 (1),
    tm 4 2 2 2 1 (2),
    tm 3 2 2 2 2 (1),
    tm 6 3 2 0 0 (1),
    tm 5 3 2 1 0 (1),
    tm 4 3 2 1 1 (1),
    tm 3 3 2 2 1 (1),
    tm 4 3 3 1 0 (1),
    tm 3 3 3 1 1 (1),
    tm 3 3 3 2 0 (1),
    tm 2 3 3 2 1 (2),
    tm 1 3 3 2 2 (1),
    tm 1 3 3 3 1 (1),
    tm 0 3 3 3 2 (1),
    tm 6 4 1 0 0 (-1),
    tm 4 4 2 1 0 (-2),
    tm 3 4 2 1 1 (-1),
    tm 2 4 3 2 0 (-1),
    tm 1 4 3 2 1 (-1)]

/-- Chart core 203 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore203 : Poly :=
  [tm 0 0 1 2 1 (1),
    tm 3 1 0 0 0 (-1),
    tm 1 1 1 1 0 (-1)]

/-- Chart core 204 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore204 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 7 0 1 1 0 (2),
    tm 5 0 2 2 0 (1),
    tm 3 1 2 2 1 (-1),
    tm 1 1 3 3 1 (-1),
    tm 0 1 3 3 2 (-1)]

/-- Chart core 205 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore205 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 6 0 1 1 0 (1),
    tm 4 0 2 1 1 (-1),
    tm 6 1 1 0 0 (1),
    tm 4 1 2 1 0 (1),
    tm 2 1 3 1 1 (-1),
    tm 0 1 3 2 2 (-1)]

/-- Chart core 206 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore206 : Poly :=
  [tm 4 0 0 0 0 (1),
    tm 3 0 0 1 0 (-1),
    tm 2 0 1 1 0 (1),
    tm 1 0 1 2 0 (-1),
    tm 0 0 1 2 1 (-1)]

/-- Chart core 207 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore207 : Poly :=
  [tm 4 0 0 0 0 (1),
    tm 3 1 0 0 0 (-1),
    tm 2 1 1 0 0 (1),
    tm 0 1 1 1 1 (1),
    tm 1 2 1 0 0 (-1)]

/-- Chart core 208 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore208 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 9 0 0 0 1 (-1),
    tm 8 0 1 1 0 (1),
    tm 7 0 1 1 1 (1),
    tm 9 1 0 0 0 (1),
    tm 8 1 1 0 0 (1),
    tm 7 1 1 0 1 (-1),
    tm 7 1 1 1 0 (2),
    tm 6 1 1 1 1 (2),
    tm 5 1 1 1 2 (-1),
    tm 6 1 2 1 0 (1),
    tm 5 1 2 1 1 (1),
    tm 5 1 2 2 0 (1),
    tm 4 1 2 2 1 (2),
    tm 3 1 2 2 2 (1),
    tm 7 2 1 0 0 (1),
    tm 6 2 1 1 0 (1),
    tm 5 2 1 1 1 (1),
    tm 5 2 2 1 0 (2),
    tm 4 2 2 1 1 (1),
    tm 4 2 2 2 0 (2),
    tm 3 2 2 2 1 (3),
    tm 2 2 2 2 2 (1),
    tm 3 2 3 2 0 (1),
    tm 2 2 3 2 1 (1),
    tm 2 2 3 3 0 (1),
    tm 1 2 3 3 1 (2),
    tm 0 2 3 3 2 (1)]

/-- Chart core 209 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore209 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 8 0 1 0 0 (1),
    tm 7 0 1 1 0 (1),
    tm 6 0 1 1 1 (1),
    tm 8 1 0 0 0 (1),
    tm 6 1 0 1 1 (-1),
    tm 7 1 1 0 0 (2),
    tm 6 1 1 1 0 (1),
    tm 5 1 1 1 1 (2),
    tm 4 1 1 2 1 (-1),
    tm 3 1 1 2 2 (-1),
    tm 6 1 2 0 0 (2),
    tm 5 1 2 1 0 (2),
    tm 4 1 2 1 1 (3),
    tm 3 1 2 2 1 (1),
    tm 2 1 2 2 2 (1),
    tm 6 2 1 0 0 (1),
    tm 4 2 1 1 1 (1),
    tm 5 2 2 0 0 (1),
    tm 4 2 2 1 0 (1),
    tm 3 2 2 1 1 (2),
    tm 2 2 2 2 1 (1),
    tm 1 2 2 2 2 (1),
    tm 4 2 3 0 0 (1),
    tm 3 2 3 1 0 (1),
    tm 2 2 3 1 1 (2),
    tm 1 2 3 2 1 (1),
    tm 0 2 3 2 2 (1)]

/-- Chart core 210 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore210 : Poly :=
  [tm 7 0 1 1 1 (1),
    tm 9 1 0 0 0 (-1),
    tm 8 1 1 0 0 (-1),
    tm 7 1 1 1 0 (-2),
    tm 6 1 1 1 1 (-1),
    tm 6 1 2 1 0 (-1),
    tm 5 1 2 2 0 (-1),
    tm 4 1 2 2 1 (-1),
    tm 3 1 2 2 2 (1),
    tm 8 2 0 0 0 (-1),
    tm 7 2 1 0 0 (-1),
    tm 6 2 1 1 0 (-2),
    tm 5 2 1 1 1 (-2),
    tm 6 2 2 0 0 (-1),
    tm 5 2 2 1 0 (-2),
    tm 4 2 2 1 1 (-2),
    tm 4 2 2 2 0 (-1),
    tm 3 2 2 2 1 (-3),
    tm 2 2 2 2 2 (-1),
    tm 4 2 3 1 0 (-1),
    tm 3 2 3 1 1 (-1),
    tm 3 2 3 2 0 (-1),
    tm 2 2 3 2 1 (-2),
    tm 1 2 3 2 2 (-1),
    tm 1 2 3 3 1 (-1),
    tm 0 2 3 3 2 (-1)]

/-- Chart core 211 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore211 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 1 0 0 0 (1),
    tm 9 1 1 0 0 (2),
    tm 8 1 1 1 0 (1),
    tm 7 1 1 1 1 (2),
    tm 8 2 1 0 0 (2),
    tm 7 2 1 1 0 (1),
    tm 6 2 1 1 1 (1),
    tm 7 2 2 0 0 (1),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (3),
    tm 5 2 2 2 0 (1),
    tm 4 2 2 2 1 (2),
    tm 3 2 2 2 2 (1),
    tm 5 3 1 1 1 (-1),
    tm 6 3 2 0 0 (1),
    tm 5 3 2 1 0 (1),
    tm 4 3 2 1 1 (1),
    tm 2 3 2 2 2 (-1),
    tm 4 3 3 1 0 (1),
    tm 3 3 3 1 1 (1),
    tm 3 3 3 2 0 (1),
    tm 2 3 3 2 1 (2),
    tm 1 3 3 2 2 (1),
    tm 1 3 3 3 1 (1),
    tm 0 3 3 3 2 (1)]

/-- Chart core 212 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore212 : Poly :=
  [tm 10 0 0 0 0 (2),
    tm 9 0 0 0 1 (-1),
    tm 8 0 1 1 0 (2),
    tm 7 0 1 1 1 (2),
    tm 9 1 0 0 0 (2),
    tm 8 1 1 0 0 (2),
    tm 7 1 1 0 1 (-1),
    tm 7 1 1 1 0 (4),
    tm 6 1 1 1 1 (4),
    tm 5 1 1 1 2 (-1),
    tm 6 1 2 1 0 (2),
    tm 5 1 2 1 1 (1),
    tm 5 1 2 2 0 (2),
    tm 4 1 2 2 1 (4),
    tm 3 1 2 2 2 (2),
    tm 7 2 1 0 0 (2),
    tm 6 2 1 1 0 (2),
    tm 5 2 1 1 1 (2),
    tm 5 2 2 1 0 (4),
    tm 4 2 2 1 1 (2),
    tm 4 2 2 2 0 (4),
    tm 3 2 2 2 1 (6),
    tm 2 2 2 2 2 (2),
    tm 3 2 3 1 1 (-1),
    tm 3 2 3 2 0 (2),
    tm 2 2 3 2 1 (2),
    tm 1 2 3 2 2 (-1),
    tm 2 2 3 3 0 (2),
    tm 1 2 3 3 1 (4),
    tm 0 2 3 3 2 (2)]

/-- Chart core 213 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore213 : Poly :=
  [tm 10 0 0 0 0 (2),
    tm 9 0 1 0 0 (2),
    tm 8 0 1 1 0 (2),
    tm 7 0 1 1 1 (2),
    tm 9 1 0 0 0 (2),
    tm 7 1 0 1 1 (-1),
    tm 8 1 1 0 0 (4),
    tm 7 1 1 1 0 (2),
    tm 6 1 1 1 1 (4),
    tm 5 1 1 2 1 (-1),
    tm 4 1 1 2 2 (-1),
    tm 7 1 2 0 0 (4),
    tm 6 1 2 1 0 (4),
    tm 5 1 2 1 1 (6),
    tm 4 1 2 2 1 (2),
    tm 3 1 2 2 2 (2),
    tm 7 2 1 0 0 (2),
    tm 5 2 1 1 1 (2),
    tm 6 2 2 0 0 (2),
    tm 5 2 2 1 0 (2),
    tm 4 2 2 1 1 (4),
    tm 3 2 2 2 1 (1),
    tm 2 2 2 2 2 (2),
    tm 5 2 3 0 0 (2),
    tm 4 2 3 1 0 (2),
    tm 3 2 3 1 1 (4),
    tm 2 2 3 2 1 (2),
    tm 1 2 3 2 2 (2),
    tm 1 2 3 3 1 (-1),
    tm 0 2 3 3 2 (-1)]

/-- Chart core 214 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore214 : Poly :=
  [tm 8 0 1 1 1 (1),
    tm 10 1 0 0 0 (-2),
    tm 9 1 1 0 0 (-2),
    tm 8 1 1 1 0 (-4),
    tm 7 1 1 1 1 (-2),
    tm 7 1 2 1 0 (-2),
    tm 6 1 2 1 1 (-1),
    tm 6 1 2 2 0 (-2),
    tm 5 1 2 2 1 (-2),
    tm 4 1 2 2 2 (1),
    tm 4 1 3 2 1 (1),
    tm 9 2 0 0 0 (-2),
    tm 8 2 1 0 0 (-2),
    tm 7 2 1 1 0 (-4),
    tm 6 2 1 1 1 (-4),
    tm 7 2 2 0 0 (-2),
    tm 6 2 2 1 0 (-4),
    tm 5 2 2 1 1 (-4),
    tm 5 2 2 2 0 (-2),
    tm 4 2 2 2 1 (-6),
    tm 3 2 2 2 2 (-2),
    tm 5 2 3 1 0 (-2),
    tm 4 2 3 1 1 (-2),
    tm 4 2 3 2 0 (-2),
    tm 3 2 3 2 1 (-4),
    tm 2 2 3 2 2 (-2),
    tm 2 2 3 3 1 (-2),
    tm 1 2 3 3 2 (-2),
    tm 2 2 4 2 1 (1),
    tm 0 2 4 3 2 (1)]

/-- Chart core 215 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore215 : Poly :=
  [tm 13 0 0 0 0 (2),
    tm 12 1 0 0 0 (2),
    tm 11 1 1 0 0 (4),
    tm 10 1 1 1 0 (2),
    tm 9 1 1 1 1 (4),
    tm 10 2 1 0 0 (4),
    tm 9 2 1 1 0 (2),
    tm 8 2 1 1 1 (2),
    tm 9 2 2 0 0 (2),
    tm 8 2 2 1 0 (4),
    tm 7 2 2 1 1 (6),
    tm 7 2 2 2 0 (2),
    tm 6 2 2 2 1 (4),
    tm 5 2 2 2 2 (2),
    tm 7 3 1 1 1 (-1),
    tm 8 3 2 0 0 (2),
    tm 7 3 2 1 0 (2),
    tm 6 3 2 1 1 (2),
    tm 5 3 2 2 1 (1),
    tm 4 3 2 2 2 (-1),
    tm 6 3 3 1 0 (2),
    tm 5 3 3 1 1 (2),
    tm 5 3 3 2 0 (2),
    tm 4 3 3 2 1 (4),
    tm 3 3 3 2 2 (2),
    tm 3 3 3 3 1 (2),
    tm 2 3 3 3 2 (2),
    tm 3 4 3 2 1 (-1),
    tm 1 4 4 3 1 (-1),
    tm 0 4 4 3 2 (-1)]

/-- Chart core 216 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore216 : Poly :=
  [tm 4 0 0 0 0 (1),
    tm 2 0 1 1 0 (-2),
    tm 0 1 2 1 0 (1)]

/-- Chart core 217 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore217 : Poly :=
  [tm 4 0 0 0 0 (1),
    tm 2 1 1 0 0 (-2),
    tm 0 1 2 1 0 (1)]

/-- Chart core 218 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore218 : Poly :=
  [tm 5 0 0 0 0 (2),
    tm 3 0 1 1 0 (2),
    tm 2 0 1 1 1 (1),
    tm 0 1 2 1 1 (-1)]

/-- Chart core 219 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore219 : Poly :=
  [tm 6 0 0 0 0 (2),
    tm 4 1 1 0 0 (2),
    tm 2 1 1 1 1 (1),
    tm 0 1 2 2 1 (-1)]

/-- Chart core 220 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore220 : Poly :=
  [tm 2 0 0 1 1 (1),
    tm 3 1 0 0 0 (-2),
    tm 1 1 1 1 0 (-2),
    tm 0 1 1 1 1 (-1)]

/-- Chart core 221 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore221 : Poly :=
  [tm 4 0 0 0 0 (2),
    tm 2 1 0 0 1 (-1),
    tm 2 1 1 0 0 (2),
    tm 0 1 1 1 1 (1)]

/-- Chart core 222 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore222 : Poly :=
  [tm 4 0 0 1 0 (1),
    tm 2 0 1 2 0 (1),
    tm 4 1 0 0 0 (1),
    tm 3 1 0 1 0 (-2),
    tm 2 1 1 1 0 (1),
    tm 1 1 1 2 0 (-2),
    tm 0 1 1 2 1 (-2)]

/-- Chart core 223 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore223 : Poly :=
  [tm 4 0 0 0 0 (2),
    tm 3 0 0 1 0 (-1),
    tm 3 1 0 0 0 (-1),
    tm 2 1 1 0 0 (2),
    tm 1 1 1 1 0 (-1),
    tm 0 1 1 1 1 (2),
    tm 1 2 1 0 0 (-1)]

/-- Chart core 224 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore224 : Poly :=
  [tm 10 0 0 1 0 (2),
    tm 8 0 1 2 0 (2),
    tm 7 0 1 2 1 (2),
    tm 10 1 0 0 0 (-1),
    tm 9 1 0 1 0 (2),
    tm 8 1 1 1 0 (2),
    tm 7 1 1 2 0 (4),
    tm 6 1 1 2 1 (4),
    tm 6 1 2 2 0 (3),
    tm 5 1 2 2 1 (2),
    tm 5 1 2 3 0 (2),
    tm 4 1 2 3 1 (4),
    tm 3 1 2 3 2 (2),
    tm 8 2 1 0 0 (-1),
    tm 7 2 1 1 0 (2),
    tm 6 2 1 1 1 (-1),
    tm 6 2 1 2 0 (2),
    tm 5 2 1 2 1 (2),
    tm 5 2 2 2 0 (4),
    tm 4 2 2 2 1 (2),
    tm 4 2 2 3 0 (4),
    tm 3 2 2 3 1 (6),
    tm 2 2 2 3 2 (2),
    tm 4 2 3 2 0 (1),
    tm 3 2 3 3 0 (2),
    tm 2 2 3 3 1 (3),
    tm 2 2 3 4 0 (2),
    tm 1 2 3 4 1 (4),
    tm 0 2 3 4 2 (2)]

/-- Chart core 225 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore225 : Poly :=
  [tm 9 0 0 0 0 (2),
    tm 8 0 1 0 0 (2),
    tm 7 0 1 1 0 (2),
    tm 6 0 1 1 1 (2),
    tm 8 1 0 0 0 (2),
    tm 7 1 1 0 0 (4),
    tm 6 1 1 1 0 (2),
    tm 5 1 1 1 1 (4),
    tm 6 1 2 0 0 (4),
    tm 5 1 2 1 0 (4),
    tm 4 1 2 1 1 (6),
    tm 3 1 2 2 1 (2),
    tm 2 1 2 2 2 (2),
    tm 7 2 0 0 0 (-1),
    tm 6 2 1 0 0 (2),
    tm 5 2 1 1 0 (-1),
    tm 4 2 1 1 1 (1),
    tm 5 2 2 0 0 (2),
    tm 4 2 2 1 0 (2),
    tm 3 2 2 1 1 (4),
    tm 3 2 2 2 0 (1),
    tm 2 2 2 2 1 (2),
    tm 1 2 2 2 2 (2),
    tm 4 2 3 0 0 (2),
    tm 3 2 3 1 0 (2),
    tm 2 2 3 1 1 (4),
    tm 1 2 3 2 1 (2),
    tm 0 2 3 2 2 (2),
    tm 1 2 3 3 0 (1),
    tm 0 2 3 3 1 (1)]

/-- Chart core 226 of the barycentric order chart 43210,
homogenized to degree 12. -/
def chartCore226 : Poly :=
  [tm 12 0 0 0 0 (2),
    tm 11 1 0 0 0 (2),
    tm 10 1 1 0 0 (4),
    tm 9 1 1 1 0 (2),
    tm 8 1 1 1 1 (4),
    tm 9 2 1 0 0 (4),
    tm 8 2 1 1 0 (2),
    tm 7 2 1 1 1 (2),
    tm 8 2 2 0 0 (2),
    tm 7 2 2 1 0 (4),
    tm 6 2 2 1 1 (6),
    tm 6 2 2 2 0 (2),
    tm 5 2 2 2 1 (4),
    tm 4 2 2 2 2 (2),
    tm 7 3 2 0 0 (2),
    tm 6 3 2 1 0 (2),
    tm 5 3 2 1 1 (2),
    tm 4 3 2 2 1 (2),
    tm 5 3 3 1 0 (2),
    tm 4 3 3 1 1 (2),
    tm 4 3 3 2 0 (2),
    tm 3 3 3 2 1 (4),
    tm 2 3 3 2 2 (2),
    tm 2 3 3 3 1 (2),
    tm 1 3 3 3 2 (2),
    tm 7 4 1 0 0 (-1),
    tm 5 4 2 1 0 (-1),
    tm 4 4 2 1 1 (-1),
    tm 3 4 3 2 0 (1),
    tm 1 4 4 3 0 (1),
    tm 0 4 4 3 1 (1)]

/-- Chart core 227 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore227 : Poly :=
  [tm 7 0 0 0 0 (1),
    tm 5 0 1 1 0 (1),
    tm 3 0 1 2 1 (2),
    tm 3 0 2 2 0 (-1),
    tm 1 0 2 3 1 (2),
    tm 0 0 2 3 2 (2),
    tm 1 0 3 3 0 (-1)]

/-- Chart core 228 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore228 : Poly :=
  [tm 4 0 1 1 1 (2),
    tm 6 1 0 0 0 (1),
    tm 2 1 2 1 1 (2),
    tm 2 1 2 2 0 (-1),
    tm 0 1 2 2 2 (2),
    tm 4 2 1 0 0 (1),
    tm 0 2 3 2 0 (-1)]

/-- Chart core 229 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore229 : Poly :=
  [tm 1 0 1 2 1 (2),
    tm 4 1 0 0 0 (-1),
    tm 0 1 2 2 0 (1)]

/-- Chart core 230 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore230 : Poly :=
  [tm 4 0 0 0 0 (1),
    tm 1 0 1 1 1 (-2),
    tm 0 0 2 2 0 (-1)]

/-- Chart core 231 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore231 : Poly :=
  [tm 9 0 1 0 0 (2),
    tm 8 0 2 0 0 (2),
    tm 7 0 2 1 0 (2),
    tm 6 0 2 1 1 (2),
    tm 9 1 0 0 0 (1),
    tm 8 1 1 0 0 (2),
    tm 7 1 1 1 0 (1),
    tm 6 1 1 1 1 (1),
    tm 7 1 2 0 0 (4),
    tm 6 1 2 1 0 (2),
    tm 5 1 2 1 1 (4),
    tm 5 1 2 2 0 (-1),
    tm 6 1 3 0 0 (4),
    tm 5 1 3 1 0 (4),
    tm 4 1 3 1 1 (6),
    tm 3 1 3 2 1 (2),
    tm 2 1 3 2 2 (2),
    tm 3 1 3 3 0 (-1),
    tm 2 1 3 3 1 (-1),
    tm 6 2 2 0 0 (2),
    tm 4 2 2 1 1 (2),
    tm 5 2 3 0 0 (2),
    tm 4 2 3 1 0 (2),
    tm 3 2 3 1 1 (4),
    tm 2 2 3 2 1 (2),
    tm 1 2 3 2 2 (2),
    tm 4 2 4 0 0 (2),
    tm 3 2 4 1 0 (2),
    tm 2 2 4 1 1 (4),
    tm 1 2 4 2 1 (2),
    tm 0 2 4 2 2 (2)]

/-- Chart core 232 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore232 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 6 0 2 2 0 (-1),
    tm 9 1 0 0 0 (2),
    tm 8 1 1 0 0 (3),
    tm 7 1 1 1 0 (4),
    tm 6 1 1 1 1 (3),
    tm 6 1 2 1 0 (2),
    tm 5 1 2 1 1 (2),
    tm 5 1 2 2 0 (2),
    tm 4 1 2 2 1 (2),
    tm 4 1 3 2 0 (-1),
    tm 2 1 3 3 1 (-1),
    tm 8 2 0 0 0 (2),
    tm 7 2 1 0 0 (2),
    tm 6 2 1 1 0 (4),
    tm 5 2 1 1 1 (4),
    tm 6 2 2 0 0 (2),
    tm 5 2 2 1 0 (4),
    tm 4 2 2 1 1 (4),
    tm 4 2 2 2 0 (2),
    tm 3 2 2 2 1 (6),
    tm 2 2 2 2 2 (2),
    tm 4 2 3 1 0 (2),
    tm 3 2 3 1 1 (2),
    tm 3 2 3 2 0 (2),
    tm 2 2 3 2 1 (4),
    tm 1 2 3 2 2 (2),
    tm 1 2 3 3 1 (2),
    tm 0 2 3 3 2 (2)]

/-- Chart core 233 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore233 : Poly :=
  [tm 11 0 0 0 0 (2),
    tm 10 1 0 0 0 (2),
    tm 9 1 1 0 0 (4),
    tm 8 1 1 1 0 (2),
    tm 7 1 1 1 1 (4),
    tm 8 2 1 0 0 (4),
    tm 7 2 1 1 0 (2),
    tm 6 2 1 1 1 (2),
    tm 7 2 2 0 0 (2),
    tm 6 2 2 1 0 (4),
    tm 5 2 2 1 1 (6),
    tm 5 2 2 2 0 (2),
    tm 4 2 2 2 1 (4),
    tm 3 2 2 2 2 (2),
    tm 8 3 0 0 0 (1),
    tm 6 3 1 1 0 (1),
    tm 5 3 1 1 1 (1),
    tm 6 3 2 0 0 (2),
    tm 5 3 2 1 0 (2),
    tm 4 3 2 1 1 (2),
    tm 4 3 2 2 0 (-1),
    tm 3 3 2 2 1 (2),
    tm 4 3 3 1 0 (2),
    tm 3 3 3 1 1 (2),
    tm 3 3 3 2 0 (2),
    tm 2 3 3 2 1 (4),
    tm 1 3 3 2 2 (2),
    tm 2 3 3 3 0 (-1),
    tm 1 3 3 3 1 (1),
    tm 0 3 3 3 2 (2)]

/-- Chart core 234 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore234 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 7 0 1 1 0 (1),
    tm 5 0 2 2 0 (-1),
    tm 3 0 3 3 0 (-1),
    tm 3 1 2 2 1 (-2),
    tm 1 1 3 3 1 (-2),
    tm 0 1 3 3 2 (-2)]

/-- Chart core 235 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore235 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 4 0 2 1 1 (-2),
    tm 4 0 2 2 0 (-1),
    tm 6 1 1 0 0 (1),
    tm 2 1 3 1 1 (-2),
    tm 2 1 3 2 0 (-1),
    tm 0 1 3 2 2 (-2)]

/-- Chart core 236 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore236 : Poly :=
  [tm 5 0 0 0 0 (1),
    tm 1 0 2 2 0 (-1),
    tm 0 0 2 2 1 (2)]

/-- Chart core 237 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore237 : Poly :=
  [tm 5 0 0 0 0 (1),
    tm 1 0 2 2 0 (-1),
    tm 0 1 2 1 1 (2)]

/-- Chart core 238 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore238 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 10 1 0 0 0 (-2),
    tm 9 1 1 0 0 (1),
    tm 8 1 1 1 0 (-2),
    tm 7 1 1 1 1 (-1),
    tm 9 2 0 0 0 (-2),
    tm 8 2 1 0 0 (-2),
    tm 7 2 1 1 0 (-4),
    tm 6 2 1 1 1 (-4),
    tm 7 2 2 0 0 (-1),
    tm 6 2 2 1 0 (-2),
    tm 5 2 2 1 1 (-2),
    tm 5 2 2 2 0 (-2),
    tm 4 2 2 2 1 (-4),
    tm 3 2 2 2 2 (-2),
    tm 7 3 1 0 0 (-2),
    tm 6 3 1 1 0 (-2),
    tm 5 3 1 1 1 (-2),
    tm 5 3 2 1 0 (-4),
    tm 4 3 2 1 1 (-2),
    tm 4 3 2 2 0 (-4),
    tm 3 3 2 2 1 (-6),
    tm 2 3 2 2 2 (-2),
    tm 5 3 3 0 0 (-1),
    tm 3 3 3 1 1 (-1),
    tm 3 3 3 2 0 (-2),
    tm 2 3 3 2 1 (-2),
    tm 2 3 3 3 0 (-2),
    tm 1 3 3 3 1 (-4),
    tm 0 3 3 3 2 (-2)]

/-- Chart core 239 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore239 : Poly :=
  [tm 9 0 0 0 0 (2),
    tm 8 0 0 1 0 (-1),
    tm 8 0 1 0 0 (2),
    tm 7 0 1 1 0 (2),
    tm 6 0 1 1 1 (2),
    tm 6 0 1 2 0 (-1),
    tm 5 0 1 2 1 (-1),
    tm 8 1 0 0 0 (2),
    tm 7 1 1 0 0 (4),
    tm 6 1 1 1 0 (2),
    tm 5 1 1 1 1 (4),
    tm 6 1 2 0 0 (4),
    tm 5 1 2 1 0 (4),
    tm 4 1 2 1 1 (6),
    tm 3 1 2 2 1 (2),
    tm 2 1 2 2 2 (2),
    tm 6 2 1 0 0 (2),
    tm 4 2 1 1 1 (2),
    tm 5 2 2 0 0 (2),
    tm 4 2 2 1 0 (3),
    tm 3 2 2 1 1 (4),
    tm 2 2 2 2 1 (2),
    tm 1 2 2 2 2 (2),
    tm 4 2 3 0 0 (2),
    tm 3 2 3 1 0 (2),
    tm 2 2 3 1 1 (4),
    tm 2 2 3 2 0 (1),
    tm 1 2 3 2 1 (3),
    tm 0 2 3 2 2 (2)]

/-- Chart core 240 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore240 : Poly :=
  [tm 9 0 1 1 0 (1),
    tm 7 1 2 1 0 (1),
    tm 5 1 2 2 1 (1),
    tm 9 2 0 0 0 (-2),
    tm 8 2 1 0 0 (-2),
    tm 7 2 1 1 0 (-4),
    tm 6 2 1 1 1 (-2),
    tm 6 2 2 1 0 (-2),
    tm 5 2 2 1 1 (-2),
    tm 5 2 2 2 0 (-2),
    tm 4 2 2 2 1 (-2),
    tm 5 2 3 1 0 (-1),
    tm 8 3 0 0 0 (-2),
    tm 7 3 1 0 0 (-2),
    tm 6 3 1 1 0 (-4),
    tm 5 3 1 1 1 (-4),
    tm 6 3 2 0 0 (-2),
    tm 5 3 2 1 0 (-4),
    tm 4 3 2 1 1 (-4),
    tm 4 3 2 2 0 (-2),
    tm 3 3 2 2 1 (-6),
    tm 2 3 2 2 2 (-2),
    tm 4 3 3 1 0 (-2),
    tm 3 3 3 1 1 (-2),
    tm 3 3 3 2 0 (-2),
    tm 2 3 3 2 1 (-4),
    tm 1 3 3 2 2 (-2),
    tm 1 3 3 3 1 (-2),
    tm 0 3 3 3 2 (-2),
    tm 3 3 4 1 0 (-1),
    tm 1 3 4 2 1 (-1)]

/-- Chart core 241 of the barycentric order chart 43210,
homogenized to degree 8. -/
def chartCore241 : Poly :=
  [tm 8 0 0 0 0 (1),
    tm 6 0 1 1 0 (1),
    tm 3 2 1 1 1 (2),
    tm 4 2 2 0 0 (-1),
    tm 1 2 2 2 1 (2),
    tm 0 2 2 2 2 (2),
    tm 2 2 3 1 0 (-1)]

/-- Chart core 242 of the barycentric order chart 43210,
homogenized to degree 7. -/
def chartCore242 : Poly :=
  [tm 7 0 0 0 0 (1),
    tm 5 1 1 0 0 (1),
    tm 4 1 1 0 1 (2),
    tm 3 2 2 0 0 (-1),
    tm 2 2 2 0 1 (2),
    tm 0 2 2 1 2 (2),
    tm 1 3 3 0 0 (-1)]

/-- Chart core 243 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore243 : Poly :=
  [tm 4 0 0 0 0 (1),
    tm 0 1 1 1 1 (-2),
    tm 0 2 2 0 0 (-1)]

/-- Chart core 244 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore244 : Poly :=
  [tm 4 0 0 0 0 (1),
    tm 0 2 1 0 1 (-2),
    tm 0 2 2 0 0 (-1)]

/-- Chart core 245 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore245 : Poly :=
  [tm 13 0 0 0 0 (1),
    tm 11 1 1 0 0 (1),
    tm 10 1 1 1 0 (2),
    tm 9 1 1 1 1 (1),
    tm 8 1 2 2 0 (2),
    tm 7 1 2 2 1 (2),
    tm 9 2 1 1 0 (2),
    tm 9 2 2 0 0 (-1),
    tm 8 2 2 1 0 (2),
    tm 7 2 2 2 0 (4),
    tm 6 2 2 2 1 (4),
    tm 6 2 3 2 0 (2),
    tm 5 2 3 2 1 (2),
    tm 5 2 3 3 0 (2),
    tm 4 2 3 3 1 (4),
    tm 3 2 3 3 2 (2),
    tm 7 3 2 1 0 (2),
    tm 6 3 2 2 0 (2),
    tm 5 3 2 2 1 (2),
    tm 7 3 3 0 0 (-1),
    tm 5 3 3 1 1 (-1),
    tm 5 3 3 2 0 (4),
    tm 4 3 3 2 1 (2),
    tm 4 3 3 3 0 (4),
    tm 3 3 3 3 1 (6),
    tm 2 3 3 3 2 (2),
    tm 3 3 4 3 0 (2),
    tm 2 3 4 3 1 (2),
    tm 2 3 4 4 0 (2),
    tm 1 3 4 4 1 (4),
    tm 0 3 4 4 2 (2)]

/-- Chart core 246 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore246 : Poly :=
  [tm 11 0 0 0 0 (1),
    tm 9 1 1 0 0 (1),
    tm 7 1 1 1 1 (1),
    tm 9 2 0 0 0 (2),
    tm 8 2 1 0 0 (2),
    tm 7 2 1 1 0 (4),
    tm 6 2 1 1 1 (2),
    tm 7 2 2 0 0 (-1),
    tm 6 2 2 1 0 (2),
    tm 5 2 2 1 1 (2),
    tm 5 2 2 2 0 (2),
    tm 4 2 2 2 1 (2),
    tm 8 3 0 0 0 (2),
    tm 7 3 1 0 0 (2),
    tm 6 3 1 1 0 (4),
    tm 5 3 1 1 1 (4),
    tm 6 3 2 0 0 (2),
    tm 5 3 2 1 0 (4),
    tm 4 3 2 1 1 (4),
    tm 4 3 2 2 0 (2),
    tm 3 3 2 2 1 (6),
    tm 2 3 2 2 2 (2),
    tm 5 3 3 0 0 (-1),
    tm 4 3 3 1 0 (2),
    tm 3 3 3 1 1 (1),
    tm 3 3 3 2 0 (2),
    tm 2 3 3 2 1 (4),
    tm 1 3 3 2 2 (2),
    tm 1 3 3 3 1 (2),
    tm 0 3 3 3 2 (2)]

/-- Chart core 247 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore247 : Poly :=
  [tm 11 0 0 0 0 (2),
    tm 10 1 0 0 0 (2),
    tm 9 1 1 0 0 (4),
    tm 8 1 1 1 0 (2),
    tm 7 1 1 1 1 (4),
    tm 9 2 0 0 0 (1),
    tm 8 2 1 0 0 (4),
    tm 7 2 1 1 0 (3),
    tm 6 2 1 1 1 (3),
    tm 7 2 2 0 0 (2),
    tm 6 2 2 1 0 (4),
    tm 5 2 2 1 1 (6),
    tm 5 2 2 2 0 (2),
    tm 4 2 2 2 1 (4),
    tm 3 2 2 2 2 (2),
    tm 6 3 2 0 0 (2),
    tm 5 3 2 1 0 (2),
    tm 4 3 2 1 1 (2),
    tm 3 3 2 2 1 (2),
    tm 4 3 3 1 0 (2),
    tm 3 3 3 1 1 (2),
    tm 3 3 3 2 0 (2),
    tm 2 3 3 2 1 (4),
    tm 1 3 3 2 2 (2),
    tm 1 3 3 3 1 (2),
    tm 0 3 3 3 2 (2),
    tm 5 4 2 0 0 (-1),
    tm 3 4 3 1 0 (-1),
    tm 2 4 3 1 1 (-1)]

/-- Chart core 248 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore248 : Poly :=
  [tm 10 0 0 0 0 (1),
    tm 8 0 1 1 0 (1),
    tm 6 2 2 0 0 (-1),
    tm 3 2 2 2 1 (-2),
    tm 4 2 3 1 0 (-1),
    tm 1 2 3 3 1 (-2),
    tm 0 2 3 3 2 (-2)]

/-- Chart core 249 of the barycentric order chart 43210,
homogenized to degree 9. -/
def chartCore249 : Poly :=
  [tm 9 0 0 0 0 (1),
    tm 7 1 1 0 0 (1),
    tm 4 1 2 1 1 (-2),
    tm 5 2 2 0 0 (-1),
    tm 2 2 3 1 1 (-2),
    tm 0 2 3 2 2 (-2),
    tm 3 3 3 0 0 (-1)]

/-- Chart core 250 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore250 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 0 1 2 2 1 (2),
    tm 2 2 2 0 0 (-1)]

/-- Chart core 251 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore251 : Poly :=
  [tm 6 0 0 0 0 (1),
    tm 2 2 2 0 0 (-1),
    tm 0 2 2 1 1 (2)]

/-- Chart core 252 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore252 : Poly :=
  [tm 10 0 0 0 0 (3),
    tm 9 0 0 0 1 (-2),
    tm 8 0 1 1 0 (3),
    tm 7 0 1 1 1 (3),
    tm 9 1 0 0 0 (3),
    tm 8 1 1 0 0 (3),
    tm 7 1 1 0 1 (-2),
    tm 7 1 1 1 0 (6),
    tm 6 1 1 1 1 (6),
    tm 5 1 1 1 2 (-2),
    tm 6 1 2 1 0 (3),
    tm 5 1 2 1 1 (2),
    tm 5 1 2 2 0 (3),
    tm 4 1 2 2 1 (6),
    tm 3 1 2 2 2 (3),
    tm 7 2 1 0 0 (3),
    tm 6 2 1 1 0 (3),
    tm 5 2 1 1 1 (3),
    tm 5 2 2 1 0 (6),
    tm 4 2 2 1 1 (3),
    tm 4 2 2 2 0 (6),
    tm 3 2 2 2 1 (9),
    tm 2 2 2 2 2 (3),
    tm 3 2 3 1 1 (-1),
    tm 3 2 3 2 0 (3),
    tm 2 2 3 2 1 (3),
    tm 1 2 3 2 2 (-1),
    tm 2 2 3 3 0 (3),
    tm 1 2 3 3 1 (6),
    tm 0 2 3 3 2 (3)]

/-- Chart core 253 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore253 : Poly :=
  [tm 10 0 0 0 0 (3),
    tm 9 0 1 0 0 (3),
    tm 8 0 1 1 0 (3),
    tm 7 0 1 1 1 (3),
    tm 9 1 0 0 0 (3),
    tm 7 1 0 1 1 (-2),
    tm 8 1 1 0 0 (6),
    tm 7 1 1 1 0 (3),
    tm 6 1 1 1 1 (6),
    tm 5 1 1 2 1 (-2),
    tm 4 1 1 2 2 (-2),
    tm 7 1 2 0 0 (6),
    tm 6 1 2 1 0 (6),
    tm 5 1 2 1 1 (9),
    tm 4 1 2 2 1 (3),
    tm 3 1 2 2 2 (3),
    tm 7 2 1 0 0 (3),
    tm 5 2 1 1 1 (3),
    tm 6 2 2 0 0 (3),
    tm 5 2 2 1 0 (3),
    tm 4 2 2 1 1 (6),
    tm 3 2 2 2 1 (2),
    tm 2 2 2 2 2 (3),
    tm 5 2 3 0 0 (3),
    tm 4 2 3 1 0 (3),
    tm 3 2 3 1 1 (6),
    tm 2 2 3 2 1 (3),
    tm 1 2 3 2 2 (3),
    tm 1 2 3 3 1 (-1),
    tm 0 2 3 3 2 (-1)]

/-- Chart core 254 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore254 : Poly :=
  [tm 8 0 1 1 1 (2),
    tm 10 1 0 0 0 (-3),
    tm 9 1 1 0 0 (-3),
    tm 8 1 1 1 0 (-6),
    tm 7 1 1 1 1 (-3),
    tm 7 1 2 1 0 (-3),
    tm 6 1 2 1 1 (-1),
    tm 6 1 2 2 0 (-3),
    tm 5 1 2 2 1 (-3),
    tm 4 1 2 2 2 (2),
    tm 4 1 3 2 1 (1),
    tm 9 2 0 0 0 (-3),
    tm 8 2 1 0 0 (-3),
    tm 7 2 1 1 0 (-6),
    tm 6 2 1 1 1 (-6),
    tm 7 2 2 0 0 (-3),
    tm 6 2 2 1 0 (-6),
    tm 5 2 2 1 1 (-6),
    tm 5 2 2 2 0 (-3),
    tm 4 2 2 2 1 (-9),
    tm 3 2 2 2 2 (-3),
    tm 5 2 3 1 0 (-3),
    tm 4 2 3 1 1 (-3),
    tm 4 2 3 2 0 (-3),
    tm 3 2 3 2 1 (-6),
    tm 2 2 3 2 2 (-3),
    tm 2 2 3 3 1 (-3),
    tm 1 2 3 3 2 (-3),
    tm 2 2 4 2 1 (1),
    tm 0 2 4 3 2 (1)]

/-- Chart core 255 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore255 : Poly :=
  [tm 13 0 0 0 0 (3),
    tm 12 1 0 0 0 (3),
    tm 11 1 1 0 0 (6),
    tm 10 1 1 1 0 (3),
    tm 9 1 1 1 1 (6),
    tm 10 2 1 0 0 (6),
    tm 9 2 1 1 0 (3),
    tm 8 2 1 1 1 (3),
    tm 9 2 2 0 0 (3),
    tm 8 2 2 1 0 (6),
    tm 7 2 2 1 1 (9),
    tm 7 2 2 2 0 (3),
    tm 6 2 2 2 1 (6),
    tm 5 2 2 2 2 (3),
    tm 7 3 1 1 1 (-2),
    tm 8 3 2 0 0 (3),
    tm 7 3 2 1 0 (3),
    tm 6 3 2 1 1 (3),
    tm 5 3 2 2 1 (1),
    tm 4 3 2 2 2 (-2),
    tm 6 3 3 1 0 (3),
    tm 5 3 3 1 1 (3),
    tm 5 3 3 2 0 (3),
    tm 4 3 3 2 1 (6),
    tm 3 3 3 2 2 (3),
    tm 3 3 3 3 1 (3),
    tm 2 3 3 3 2 (3),
    tm 3 4 3 2 1 (-1),
    tm 1 4 4 3 1 (-1),
    tm 0 4 4 3 2 (-1)]

/-- Chart core 256 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore256 : Poly :=
  [tm 4 0 0 0 0 (2),
    tm 2 0 1 1 0 (-3),
    tm 0 1 2 1 0 (1)]

/-- Chart core 257 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore257 : Poly :=
  [tm 4 0 0 0 0 (2),
    tm 2 1 1 0 0 (-3),
    tm 0 1 2 1 0 (1)]

/-- Chart core 258 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore258 : Poly :=
  [tm 5 0 0 0 0 (3),
    tm 3 0 1 1 0 (3),
    tm 2 0 1 1 1 (2),
    tm 0 1 2 1 1 (-1)]

/-- Chart core 259 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore259 : Poly :=
  [tm 6 0 0 0 0 (3),
    tm 4 1 1 0 0 (3),
    tm 2 1 1 1 1 (2),
    tm 0 1 2 2 1 (-1)]

/-- Chart core 260 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore260 : Poly :=
  [tm 2 0 0 1 1 (2),
    tm 3 1 0 0 0 (-3),
    tm 1 1 1 1 0 (-3),
    tm 0 1 1 1 1 (-1)]

/-- Chart core 261 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore261 : Poly :=
  [tm 4 0 0 0 0 (3),
    tm 2 1 0 0 1 (-2),
    tm 2 1 1 0 0 (3),
    tm 0 1 1 1 1 (1)]

/-- Chart core 262 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore262 : Poly :=
  [tm 10 0 0 0 0 (3),
    tm 9 0 0 0 1 (-1),
    tm 8 0 1 1 0 (3),
    tm 7 0 1 1 1 (3),
    tm 9 1 0 0 0 (3),
    tm 8 1 1 0 0 (3),
    tm 7 1 1 0 1 (-1),
    tm 7 1 1 1 0 (6),
    tm 6 1 1 1 1 (6),
    tm 5 1 1 1 2 (-1),
    tm 6 1 2 1 0 (3),
    tm 5 1 2 1 1 (1),
    tm 5 1 2 2 0 (3),
    tm 4 1 2 2 1 (6),
    tm 3 1 2 2 2 (3),
    tm 7 2 1 0 0 (3),
    tm 6 2 1 1 0 (3),
    tm 5 2 1 1 1 (3),
    tm 5 2 2 1 0 (6),
    tm 4 2 2 1 1 (3),
    tm 4 2 2 2 0 (6),
    tm 3 2 2 2 1 (9),
    tm 2 2 2 2 2 (3),
    tm 3 2 3 1 1 (-2),
    tm 3 2 3 2 0 (3),
    tm 2 2 3 2 1 (3),
    tm 1 2 3 2 2 (-2),
    tm 2 2 3 3 0 (3),
    tm 1 2 3 3 1 (6),
    tm 0 2 3 3 2 (3)]

/-- Chart core 263 of the barycentric order chart 43210,
homogenized to degree 10. -/
def chartCore263 : Poly :=
  [tm 10 0 0 0 0 (3),
    tm 9 0 1 0 0 (3),
    tm 8 0 1 1 0 (3),
    tm 7 0 1 1 1 (3),
    tm 9 1 0 0 0 (3),
    tm 7 1 0 1 1 (-1),
    tm 8 1 1 0 0 (6),
    tm 7 1 1 1 0 (3),
    tm 6 1 1 1 1 (6),
    tm 5 1 1 2 1 (-1),
    tm 4 1 1 2 2 (-1),
    tm 7 1 2 0 0 (6),
    tm 6 1 2 1 0 (6),
    tm 5 1 2 1 1 (9),
    tm 4 1 2 2 1 (3),
    tm 3 1 2 2 2 (3),
    tm 7 2 1 0 0 (3),
    tm 5 2 1 1 1 (3),
    tm 6 2 2 0 0 (3),
    tm 5 2 2 1 0 (3),
    tm 4 2 2 1 1 (6),
    tm 3 2 2 2 1 (1),
    tm 2 2 2 2 2 (3),
    tm 5 2 3 0 0 (3),
    tm 4 2 3 1 0 (3),
    tm 3 2 3 1 1 (6),
    tm 2 2 3 2 1 (3),
    tm 1 2 3 2 2 (3),
    tm 1 2 3 3 1 (-2),
    tm 0 2 3 3 2 (-2)]

/-- Chart core 264 of the barycentric order chart 43210,
homogenized to degree 11. -/
def chartCore264 : Poly :=
  [tm 8 0 1 1 1 (1),
    tm 10 1 0 0 0 (-3),
    tm 9 1 1 0 0 (-3),
    tm 8 1 1 1 0 (-6),
    tm 7 1 1 1 1 (-3),
    tm 7 1 2 1 0 (-3),
    tm 6 1 2 1 1 (-2),
    tm 6 1 2 2 0 (-3),
    tm 5 1 2 2 1 (-3),
    tm 4 1 2 2 2 (1),
    tm 4 1 3 2 1 (2),
    tm 9 2 0 0 0 (-3),
    tm 8 2 1 0 0 (-3),
    tm 7 2 1 1 0 (-6),
    tm 6 2 1 1 1 (-6),
    tm 7 2 2 0 0 (-3),
    tm 6 2 2 1 0 (-6),
    tm 5 2 2 1 1 (-6),
    tm 5 2 2 2 0 (-3),
    tm 4 2 2 2 1 (-9),
    tm 3 2 2 2 2 (-3),
    tm 5 2 3 1 0 (-3),
    tm 4 2 3 1 1 (-3),
    tm 4 2 3 2 0 (-3),
    tm 3 2 3 2 1 (-6),
    tm 2 2 3 2 2 (-3),
    tm 2 2 3 3 1 (-3),
    tm 1 2 3 3 2 (-3),
    tm 2 2 4 2 1 (2),
    tm 0 2 4 3 2 (2)]

/-- Chart core 265 of the barycentric order chart 43210,
homogenized to degree 13. -/
def chartCore265 : Poly :=
  [tm 13 0 0 0 0 (3),
    tm 12 1 0 0 0 (3),
    tm 11 1 1 0 0 (6),
    tm 10 1 1 1 0 (3),
    tm 9 1 1 1 1 (6),
    tm 10 2 1 0 0 (6),
    tm 9 2 1 1 0 (3),
    tm 8 2 1 1 1 (3),
    tm 9 2 2 0 0 (3),
    tm 8 2 2 1 0 (6),
    tm 7 2 2 1 1 (9),
    tm 7 2 2 2 0 (3),
    tm 6 2 2 2 1 (6),
    tm 5 2 2 2 2 (3),
    tm 7 3 1 1 1 (-1),
    tm 8 3 2 0 0 (3),
    tm 7 3 2 1 0 (3),
    tm 6 3 2 1 1 (3),
    tm 5 3 2 2 1 (2),
    tm 4 3 2 2 2 (-1),
    tm 6 3 3 1 0 (3),
    tm 5 3 3 1 1 (3),
    tm 5 3 3 2 0 (3),
    tm 4 3 3 2 1 (6),
    tm 3 3 3 2 2 (3),
    tm 3 3 3 3 1 (3),
    tm 2 3 3 3 2 (3),
    tm 3 4 3 2 1 (-2),
    tm 1 4 4 3 1 (-2),
    tm 0 4 4 3 2 (-2)]

/-- Chart core 266 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore266 : Poly :=
  [tm 4 0 0 0 0 (1),
    tm 2 0 1 1 0 (-3),
    tm 0 1 2 1 0 (2)]

/-- Chart core 267 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore267 : Poly :=
  [tm 4 0 0 0 0 (1),
    tm 2 1 1 0 0 (-3),
    tm 0 1 2 1 0 (2)]

/-- Chart core 268 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore268 : Poly :=
  [tm 5 0 0 0 0 (3),
    tm 3 0 1 1 0 (3),
    tm 2 0 1 1 1 (1),
    tm 0 1 2 1 1 (-2)]

/-- Chart core 269 of the barycentric order chart 43210,
homogenized to degree 6. -/
def chartCore269 : Poly :=
  [tm 6 0 0 0 0 (3),
    tm 4 1 1 0 0 (3),
    tm 2 1 1 1 1 (1),
    tm 0 1 2 2 1 (-2)]

/-- Chart core 270 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore270 : Poly :=
  [tm 2 0 0 1 1 (1),
    tm 3 1 0 0 0 (-3),
    tm 1 1 1 1 0 (-3),
    tm 0 1 1 1 1 (-2)]

/-- Chart core 271 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore271 : Poly :=
  [tm 4 0 0 0 0 (3),
    tm 2 1 0 0 1 (-1),
    tm 2 1 1 0 0 (3),
    tm 0 1 1 1 1 (2)]

/-- Chart core 272 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore272 : Poly :=
  [tm 4 0 0 1 0 (1),
    tm 2 0 1 2 0 (1),
    tm 4 1 0 0 0 (2),
    tm 3 1 0 1 0 (-3),
    tm 2 1 1 1 0 (2),
    tm 1 1 1 2 0 (-3),
    tm 0 1 1 2 1 (-3)]

/-- Chart core 273 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore273 : Poly :=
  [tm 4 0 0 0 0 (3),
    tm 3 0 0 1 0 (-1),
    tm 3 1 0 0 0 (-2),
    tm 2 1 1 0 0 (3),
    tm 1 1 1 1 0 (-1),
    tm 0 1 1 1 1 (3),
    tm 1 2 1 0 0 (-2)]

/-- Chart core 274 of the barycentric order chart 43210,
homogenized to degree 5. -/
def chartCore274 : Poly :=
  [tm 4 0 0 1 0 (2),
    tm 2 0 1 2 0 (2),
    tm 4 1 0 0 0 (1),
    tm 3 1 0 1 0 (-3),
    tm 2 1 1 1 0 (1),
    tm 1 1 1 2 0 (-3),
    tm 0 1 1 2 1 (-3)]

/-- Chart core 275 of the barycentric order chart 43210,
homogenized to degree 4. -/
def chartCore275 : Poly :=
  [tm 4 0 0 0 0 (3),
    tm 3 0 0 1 0 (-2),
    tm 3 1 0 0 0 (-1),
    tm 2 1 1 0 0 (3),
    tm 1 1 1 1 0 (-2),
    tm 0 1 1 1 1 (3),
    tm 1 2 1 0 0 (-1)]

/-- Flat dictionary core 0 (degree 3), denominators cleared. -/
def flatCore0 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 2 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1)]

/-- The certificate-side product for flat core 0: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct0 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    ([tm 10 0 0 0 0 (1),
      tm 8 0 1 1 0 (2),
      tm 9 1 0 0 0 (1),
      tm 8 1 1 0 0 (1),
      tm 7 1 1 1 0 (3),
      tm 6 1 1 1 1 (2),
      tm 6 1 2 1 0 (2),
      tm 5 1 2 2 0 (2),
      tm 4 1 2 2 1 (2),
      tm 7 2 1 0 0 (1),
      tm 6 2 1 1 0 (1),
      tm 5 2 1 1 1 (1),
      tm 5 2 2 1 0 (2),
      tm 4 2 2 1 1 (1),
      tm 4 2 2 2 0 (2),
      tm 3 2 2 2 1 (3),
      tm 2 2 2 2 2 (1),
      tm 3 2 3 2 0 (1),
      tm 2 2 3 2 1 (1),
      tm 2 2 3 3 0 (1),
      tm 1 2 3 3 1 (2),
      tm 0 2 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 0: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore0 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore0)) den one two three four
      = polyEval chartProduct0 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 1 (degree 5), denominators cleared. -/
def flatCore1 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 2 0 (-2),
    ftm 0 1 3 0 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (2),
    ftm 0 2 3 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-2),
    ftm 1 0 1 1 (3),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 0 (2),
    ftm 1 0 2 1 (-2),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 1 (-4),
    ftm 1 1 2 0 (-1),
    ftm 1 1 2 1 (2),
    ftm 1 2 1 0 (1),
    ftm 1 2 2 0 (-1),
    ftm 2 0 0 0 (-2),
    ftm 2 0 0 1 (2),
    ftm 2 0 1 0 (2),
    ftm 2 0 1 1 (-1),
    ftm 2 0 1 2 (-1),
    ftm 2 1 0 0 (2),
    ftm 2 1 0 1 (-2),
    ftm 2 1 1 0 (-2),
    ftm 2 1 1 1 (2),
    ftm 3 0 0 1 (1),
    ftm 3 0 0 2 (-1)]

/-- The certificate-side product for flat core 1: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct1 : Poly :=
  polyMul ([tm 2 2 1 0 0 (1)])
    (chartCore0)

/-- KERNEL-CHECKED chart soundness for flat core 1: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore1 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore1)) den one two three four
      = polyEval chartProduct1 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 2 (degree 3), denominators cleared. -/
def flatCore2 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1)]

/-- The certificate-side product for flat core 2: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct2 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    ([tm 9 0 0 0 0 (1),
      tm 8 0 1 0 0 (1),
      tm 7 0 1 1 0 (1),
      tm 6 0 1 1 1 (1),
      tm 8 1 0 0 0 (1),
      tm 7 1 1 0 0 (3),
      tm 6 1 1 1 0 (1),
      tm 5 1 1 1 1 (2),
      tm 6 1 2 0 0 (2),
      tm 5 1 2 1 0 (2),
      tm 4 1 2 1 1 (3),
      tm 3 1 2 2 1 (1),
      tm 2 1 2 2 2 (1),
      tm 6 2 1 0 0 (2),
      tm 5 2 2 0 0 (2),
      tm 4 2 2 1 0 (2),
      tm 3 2 2 1 1 (2),
      tm 4 2 3 0 0 (1),
      tm 3 2 3 1 0 (1),
      tm 2 2 3 1 1 (2),
      tm 1 2 3 2 1 (1),
      tm 0 2 3 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 2: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore2 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore2)) den one two three four
      = polyEval chartProduct2 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 3 (degree 5), denominators cleared. -/
def flatCore3 : FlatPoly :=
  [ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-2),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-3),
    ftm 0 1 1 2 (2),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 0 (2),
    ftm 0 2 0 1 (-2),
    ftm 0 2 1 0 (-2),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 1 (1),
    ftm 0 3 1 0 (-1),
    ftm 0 3 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (2),
    ftm 1 0 0 3 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (4),
    ftm 1 1 1 2 (-2),
    ftm 1 2 0 0 (-2),
    ftm 1 2 0 1 (2),
    ftm 1 2 1 0 (2),
    ftm 1 2 1 1 (-2),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-2),
    ftm 2 0 0 3 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 0 2 (1)]

/-- The certificate-side product for flat core 3: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct3 : Poly :=
  polyMul ([tm 4 2 1 0 0 (1)])
    (chartCore1)

/-- KERNEL-CHECKED chart soundness for flat core 3: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore3 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore3)) den one two three four
      = polyEval chartProduct3 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 4 (degree 3), denominators cleared. -/
def flatCore4 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 2 0 (1),
    ftm 0 1 0 1 (1),
    ftm 0 1 2 0 (-1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-1)]

/-- The certificate-side product for flat core 4: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct4 : Poly :=
  polyMul ([tm 4 0 0 0 0 (1)])
    ([tm 8 0 0 0 0 (1),
      tm 7 1 0 0 0 (1),
      tm 6 1 1 0 0 (2),
      tm 4 1 1 1 1 (1),
      tm 6 2 0 0 0 (1),
      tm 5 2 1 0 0 (1),
      tm 4 2 1 1 0 (1),
      tm 4 2 2 0 0 (1),
      tm 2 2 2 1 1 (1),
      tm 5 3 0 0 0 (1),
      tm 3 3 1 1 0 (2),
      tm 2 3 1 1 1 (1),
      tm 1 3 2 2 0 (1),
      tm 0 3 2 2 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 4: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore4 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore4)) den one two three four
      = polyEval chartProduct4 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 5 (degree 5), denominators cleared. -/
def flatCore5 : FlatPoly :=
  [ftm 0 0 2 0 (2),
    ftm 0 0 2 1 (-2),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (2),
    ftm 0 1 3 0 (-1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 3 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (2),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 0 (-2),
    ftm 1 0 2 1 (2),
    ftm 1 1 1 0 (-3),
    ftm 1 1 1 1 (4),
    ftm 1 1 2 0 (1),
    ftm 1 1 2 1 (-2),
    ftm 1 2 1 0 (1),
    ftm 1 2 2 0 (1),
    ftm 2 0 0 1 (2),
    ftm 2 0 0 2 (-2),
    ftm 2 0 1 0 (-2),
    ftm 2 0 1 1 (1),
    ftm 2 0 1 2 (1),
    ftm 2 1 1 0 (2),
    ftm 2 1 1 1 (-2),
    ftm 3 0 0 1 (-1),
    ftm 3 0 0 2 (1)]

/-- The certificate-side product for flat core 5: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct5 : Poly :=
  polyMul ([tm 4 2 0 0 0 (-1)])
    (chartCore2)

/-- KERNEL-CHECKED chart soundness for flat core 5: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore5 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore5)) den one two three four
      = polyEval chartProduct5 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 6 (degree 5), denominators cleared. -/
def flatCore6 : FlatPoly :=
  [ftm 0 0 0 2 (2),
    ftm 0 0 1 2 (-2),
    ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-2),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 1 2 (2),
    ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-1),
    ftm 0 2 0 1 (-2),
    ftm 0 2 1 0 (2),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 0 (-2),
    ftm 0 2 2 1 (1),
    ftm 0 3 1 0 (-1),
    ftm 0 3 2 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 0 3 (-1),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (2),
    ftm 1 1 0 1 (-3),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 1 (4),
    ftm 1 1 1 2 (-2),
    ftm 1 2 0 1 (2),
    ftm 1 2 1 1 (-2),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 3 (1),
    ftm 2 1 0 1 (1),
    ftm 2 1 0 2 (1)]

/-- The certificate-side product for flat core 6: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct6 : Poly :=
  polyMul ([tm 5 0 0 0 0 (1)])
    (chartCore3)

/-- KERNEL-CHECKED chart soundness for flat core 6: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore6 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore6)) den one two three four
      = polyEval chartProduct6 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 7 (degree 3), denominators cleared. -/
def flatCore7 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 2 0 (1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1)]

/-- The certificate-side product for flat core 7: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct7 : Poly :=
  polyMul ([tm 3 1 0 0 0 (1)])
    ([tm 8 0 0 0 0 (1),
      tm 6 0 1 1 0 (1),
      tm 7 1 0 0 0 (1),
      tm 6 1 1 0 0 (1),
      tm 5 1 1 1 0 (1),
      tm 4 1 1 1 1 (2),
      tm 4 1 2 1 0 (1),
      tm 5 2 1 0 0 (1),
      tm 3 2 1 1 1 (1),
      tm 3 2 2 1 0 (1),
      tm 2 2 2 1 1 (1),
      tm 1 2 2 2 1 (1),
      tm 0 2 2 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 7: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore7 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore7)) den one two three four
      = polyEval chartProduct7 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 8 (degree 5), denominators cleared. -/
def flatCore8 : FlatPoly :=
  [ftm 0 1 2 0 (1),
    ftm 0 1 3 0 (-1),
    ftm 0 2 2 0 (-1),
    ftm 0 2 3 0 (1),
    ftm 1 0 1 0 (2),
    ftm 1 0 1 1 (-3),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-2),
    ftm 1 0 2 1 (2),
    ftm 1 1 1 0 (-3),
    ftm 1 1 1 1 (4),
    ftm 1 1 2 0 (1),
    ftm 1 1 2 1 (-2),
    ftm 1 2 1 0 (1),
    ftm 1 2 2 0 (1),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 0 (-2),
    ftm 2 0 1 1 (1),
    ftm 2 0 1 2 (1),
    ftm 2 1 1 0 (2),
    ftm 2 1 1 1 (-2),
    ftm 3 0 0 1 (-1),
    ftm 3 0 0 2 (1)]

/-- The certificate-side product for flat core 8: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct8 : Poly :=
  polyMul ([tm 4 3 1 0 0 (1)])
    ([tm 12 0 0 0 0 (1),
      tm 11 0 0 1 0 (1),
      tm 10 0 1 1 0 (2),
      tm 9 0 1 2 0 (2),
      tm 8 0 1 2 1 (1),
      tm 8 0 2 2 0 (1),
      tm 7 0 2 3 0 (1),
      tm 6 0 2 3 1 (1),
      tm 11 1 0 0 0 (1),
      tm 10 1 0 1 0 (1),
      tm 10 1 1 0 0 (1),
      tm 9 1 1 1 0 (3),
      tm 8 1 1 1 1 (2),
      tm 8 1 1 2 0 (2),
      tm 7 1 1 2 1 (4),
      tm 8 1 2 1 0 (2),
      tm 7 1 2 2 0 (3),
      tm 6 1 2 2 1 (4),
      tm 6 1 2 3 0 (1),
      tm 5 1 2 3 1 (5),
      tm 4 1 2 3 2 (3),
      tm 6 1 3 2 0 (1),
      tm 5 1 3 3 0 (1),
      tm 4 1 3 3 1 (2),
      tm 3 1 3 4 1 (1),
      tm 2 1 3 4 2 (1),
      tm 9 2 1 0 0 (1),
      tm 8 2 1 1 0 (1),
      tm 7 2 1 1 1 (1),
      tm 6 2 1 2 1 (2),
      tm 7 2 2 1 0 (2),
      tm 6 2 2 1 1 (1),
      tm 6 2 2 2 0 (2),
      tm 5 2 2 2 1 (5),
      tm 4 2 2 2 2 (1),
      tm 4 2 2 3 1 (4),
      tm 3 2 2 3 2 (4),
      tm 5 2 3 2 0 (1),
      tm 4 2 3 2 1 (1),
      tm 4 2 3 3 0 (1),
      tm 3 2 3 3 1 (4),
      tm 2 2 3 3 2 (3),
      tm 2 2 3 4 1 (2),
      tm 1 2 3 4 2 (4),
      tm 0 2 3 4 3 (2)])

/-- KERNEL-CHECKED chart soundness for flat core 8: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore8 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore8)) den one two three four
      = polyEval chartProduct8 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 9 (degree 3), denominators cleared. -/
def flatCore9 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1)]

/-- The certificate-side product for flat core 9: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct9 : Poly :=
  polyMul ([tm 4 1 0 0 0 (1)])
    ([tm 7 0 0 0 0 (1),
      tm 5 0 1 1 0 (1),
      tm 4 0 1 1 1 (1),
      tm 6 1 0 0 0 (1),
      tm 5 1 1 0 0 (1),
      tm 4 1 1 1 0 (1),
      tm 3 1 1 1 1 (2),
      tm 3 1 2 1 0 (1),
      tm 2 1 2 1 1 (1),
      tm 1 1 2 2 1 (1),
      tm 0 1 2 2 2 (1),
      tm 4 2 1 0 0 (1),
      tm 2 2 2 1 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 9: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore9 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore9)) den one two three four
      = polyEval chartProduct9 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 10 (degree 5), denominators cleared. -/
def flatCore10 : FlatPoly :=
  [ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-2),
    ftm 0 1 1 1 (-3),
    ftm 0 1 1 2 (2),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 1 (-2),
    ftm 0 2 1 0 (1),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 0 (-1),
    ftm 0 2 2 1 (1),
    ftm 0 3 1 0 (-1),
    ftm 0 3 2 0 (1),
    ftm 1 0 0 2 (1),
    ftm 1 0 0 3 (-1),
    ftm 1 1 0 1 (-3),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 1 (4),
    ftm 1 1 1 2 (-2),
    ftm 1 2 0 1 (2),
    ftm 1 2 1 1 (-2),
    ftm 2 0 0 2 (-1),
    ftm 2 0 0 3 (1),
    ftm 2 1 0 1 (1),
    ftm 2 1 0 2 (1)]

/-- The certificate-side product for flat core 10: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct10 : Poly :=
  polyMul ([tm 6 2 1 0 0 (1)])
    ([tm 11 0 0 0 0 (1),
      tm 10 0 0 1 0 (1),
      tm 9 0 1 1 0 (1),
      tm 8 0 1 1 1 (2),
      tm 8 0 1 2 0 (1),
      tm 7 0 1 2 1 (1),
      tm 10 1 0 0 0 (1),
      tm 9 1 0 1 0 (1),
      tm 9 1 1 0 0 (2),
      tm 8 1 1 1 0 (3),
      tm 7 1 1 1 1 (4),
      tm 7 1 1 2 0 (1),
      tm 6 1 1 2 1 (2),
      tm 7 1 2 1 0 (2),
      tm 6 1 2 1 1 (4),
      tm 6 1 2 2 0 (2),
      tm 5 1 2 2 1 (5),
      tm 4 1 2 2 2 (4),
      tm 4 1 2 3 1 (1),
      tm 3 1 2 3 2 (1),
      tm 8 2 1 0 0 (2),
      tm 7 2 1 1 0 (2),
      tm 6 2 1 1 1 (1),
      tm 7 2 2 0 0 (1),
      tm 6 2 2 1 0 (3),
      tm 5 2 2 1 1 (5),
      tm 5 2 2 2 0 (2),
      tm 4 2 2 2 1 (4),
      tm 3 2 2 2 2 (3),
      tm 5 2 3 1 0 (1),
      tm 4 2 3 1 1 (2),
      tm 4 2 3 2 0 (1),
      tm 3 2 3 2 1 (4),
      tm 2 2 3 2 2 (4),
      tm 2 2 3 3 1 (1),
      tm 1 2 3 3 2 (3),
      tm 0 2 3 3 3 (2),
      tm 6 3 2 0 0 (1),
      tm 5 3 2 1 0 (1),
      tm 4 3 2 1 1 (1),
      tm 4 3 3 1 0 (1),
      tm 3 3 3 1 1 (1),
      tm 3 3 3 2 0 (1),
      tm 2 3 3 2 1 (2),
      tm 1 3 3 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 10: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore10 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore10)) den one two three four
      = polyEval chartProduct10 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 11 (degree 4), denominators cleared. -/
def flatCore11 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 1 (-2),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (1)]

/-- The certificate-side product for flat core 11: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct11 : Poly :=
  polyMul ([tm 5 2 1 0 0 (1)])
    (chartCore4)

/-- KERNEL-CHECKED chart soundness for flat core 11: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore11 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore11)) den one two three four
      = polyEval chartProduct11 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 12 (degree 4), denominators cleared. -/
def flatCore12 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (2),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-1)]

/-- The certificate-side product for flat core 12: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct12 : Poly :=
  polyMul ([tm 5 2 1 0 0 (-1)])
    (chartCore5)

/-- KERNEL-CHECKED chart soundness for flat core 12: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore12 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore12)) den one two three four
      = polyEval chartProduct12 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 13 (degree 3), denominators cleared. -/
def flatCore13 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-2),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1)]

/-- The certificate-side product for flat core 13: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct13 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    ([tm 10 0 0 0 0 (1),
      tm 9 0 1 0 0 (1),
      tm 8 0 1 1 0 (1),
      tm 7 0 1 1 1 (1),
      tm 9 1 0 0 0 (1),
      tm 8 1 1 0 0 (2),
      tm 7 1 1 1 0 (2),
      tm 6 1 1 1 1 (2),
      tm 7 1 2 0 0 (2),
      tm 6 1 2 1 0 (2),
      tm 5 1 2 1 1 (3),
      tm 5 1 2 2 0 (1),
      tm 4 1 2 2 1 (2),
      tm 3 1 2 2 2 (1),
      tm 7 2 1 0 0 (1),
      tm 6 2 1 1 0 (1),
      tm 5 2 1 1 1 (1),
      tm 6 2 2 0 0 (1),
      tm 5 2 2 1 0 (2),
      tm 4 2 2 1 1 (2),
      tm 4 2 2 2 0 (2),
      tm 3 2 2 2 1 (3),
      tm 2 2 2 2 2 (1),
      tm 5 2 3 0 0 (1),
      tm 4 2 3 1 0 (1),
      tm 3 2 3 1 1 (2),
      tm 3 2 3 2 0 (1),
      tm 2 2 3 2 1 (2),
      tm 1 2 3 2 2 (1),
      tm 2 2 3 3 0 (1),
      tm 1 2 3 3 1 (2),
      tm 0 2 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 13: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore13 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore13)) den one two three four
      = polyEval chartProduct13 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 14 (degree 4), denominators cleared. -/
def flatCore14 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 0 0 (1),
    ftm 1 1 1 0 (-3),
    ftm 1 1 1 1 (1),
    ftm 1 1 2 0 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 0 (-1),
    ftm 2 1 1 0 (1)]

/-- The certificate-side product for flat core 14: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct14 : Poly :=
  polyMul ([tm 3 2 0 0 0 (1)])
    ([tm 8 0 2 1 0 (1),
      tm 10 1 0 0 0 (1),
      tm 9 1 1 0 0 (1),
      tm 8 1 1 1 0 (2),
      tm 7 1 1 1 1 (1),
      tm 7 1 2 1 0 (2),
      tm 6 1 2 1 1 (1),
      tm 6 1 2 2 0 (1),
      tm 5 1 2 2 1 (1),
      tm 6 1 3 1 0 (2),
      tm 5 1 3 2 0 (1),
      tm 4 1 3 2 1 (2),
      tm 9 2 0 0 0 (1),
      tm 8 2 1 0 0 (1),
      tm 7 2 1 1 0 (2),
      tm 6 2 1 1 1 (2),
      tm 7 2 2 0 0 (1),
      tm 6 2 2 1 0 (2),
      tm 5 2 2 1 1 (2),
      tm 5 2 2 2 0 (1),
      tm 4 2 2 2 1 (3),
      tm 3 2 2 2 2 (1),
      tm 5 2 3 1 0 (2),
      tm 4 2 3 1 1 (1),
      tm 4 2 3 2 0 (1),
      tm 3 2 3 2 1 (3),
      tm 2 2 3 2 2 (1),
      tm 2 2 3 3 1 (1),
      tm 1 2 3 3 2 (1),
      tm 4 2 4 1 0 (1),
      tm 3 2 4 2 0 (1),
      tm 2 2 4 2 1 (2),
      tm 1 2 4 3 1 (1),
      tm 0 2 4 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 14: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore14 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore14)) den one two three four
      = polyEval chartProduct14 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 15 (degree 4), denominators cleared. -/
def flatCore15 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 1 2 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 1 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (-3),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 1 (1),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 15: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct15 : Poly :=
  polyMul ([tm 3 0 0 0 0 (1)])
    ([tm 13 0 0 0 0 (1),
      tm 12 1 0 0 0 (1),
      tm 11 1 1 0 0 (2),
      tm 10 1 1 1 0 (1),
      tm 9 1 1 1 1 (2),
      tm 10 2 1 0 0 (2),
      tm 9 2 1 1 0 (1),
      tm 8 2 1 1 1 (1),
      tm 9 2 2 0 0 (1),
      tm 8 2 2 1 0 (2),
      tm 7 2 2 1 1 (3),
      tm 7 2 2 2 0 (1),
      tm 6 2 2 2 1 (2),
      tm 5 2 2 2 2 (1),
      tm 8 3 2 0 0 (1),
      tm 7 3 2 1 0 (2),
      tm 6 3 2 1 1 (1),
      tm 5 3 2 2 1 (1),
      tm 6 3 3 1 0 (1),
      tm 5 3 3 1 1 (1),
      tm 5 3 3 2 0 (2),
      tm 4 3 3 2 1 (3),
      tm 3 3 3 2 2 (1),
      tm 3 3 3 3 1 (1),
      tm 2 3 3 3 2 (1),
      tm 6 4 2 1 0 (1),
      tm 5 4 3 1 0 (1),
      tm 4 4 3 2 0 (2),
      tm 3 4 3 2 1 (2),
      tm 3 4 4 2 0 (1),
      tm 2 4 4 2 1 (1),
      tm 2 4 4 3 0 (1),
      tm 1 4 4 3 1 (2),
      tm 0 4 4 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 15: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore15 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore15)) den one two three four
      = polyEval chartProduct15 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 16 (degree 3), denominators cleared. -/
def flatCore16 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 1 0 (-3),
    ftm 0 1 1 1 (2),
    ftm 0 1 2 0 (1),
    ftm 0 2 1 0 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 1 0 (1)]

/-- The certificate-side product for flat core 16: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct16 : Poly :=
  polyMul ([tm 3 2 1 0 0 (-1)])
    (chartCore6)

/-- KERNEL-CHECKED chart soundness for flat core 16: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore16 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore16)) den one two three four
      = polyEval chartProduct16 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 17 (degree 3), denominators cleared. -/
def flatCore17 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 1 (1),
    ftm 1 0 0 1 (-3),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 17: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct17 : Poly :=
  polyMul ([tm 3 1 1 1 0 (-1)])
    (chartCore7)

/-- KERNEL-CHECKED chart soundness for flat core 17: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore17 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore17)) den one two three four
      = polyEval chartProduct17 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 18 (degree 2), denominators cleared. -/
def flatCore18 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 1 0 0 1 (-1)]

/-- The certificate-side product for flat core 18: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct18 : Poly :=
  polyMul ([tm 2 1 1 0 0 (1)])
    ([tm 4 0 0 0 0 (1),
      tm 2 0 0 1 1 (1),
      tm 3 1 0 0 0 (1),
      tm 2 1 1 0 0 (1),
      tm 1 1 1 1 0 (1),
      tm 0 1 1 1 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 18: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore18 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore18)) den one two three four
      = polyEval chartProduct18 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 19 (degree 2), denominators cleared. -/
def flatCore19 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 0 2 0 (-1),
    ftm 0 1 1 0 (-1),
    ftm 1 0 0 0 (1),
    ftm 1 0 1 0 (-1)]

/-- The certificate-side product for flat core 19: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct19 : Poly :=
  polyMul ([tm 1 1 1 1 0 (1)])
    ([tm 4 0 0 0 0 (1),
      tm 3 1 0 0 0 (1),
      tm 2 1 0 0 1 (1),
      tm 2 1 1 0 0 (1),
      tm 1 1 1 1 0 (1),
      tm 0 1 1 1 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 19: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore19 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore19)) den one two three four
      = polyEval chartProduct19 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 20 (degree 3), denominators cleared. -/
def flatCore20 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 1 (-1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-1)]

/-- The certificate-side product for flat core 20: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct20 : Poly :=
  polyMul ([tm 3 1 1 0 0 (-1)])
    (chartCore8)

/-- KERNEL-CHECKED chart soundness for flat core 20: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore20 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore20)) den one two three four
      = polyEval chartProduct20 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 21 (degree 4), denominators cleared. -/
def flatCore21 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 1 2 1 (-1),
    ftm 0 2 1 0 (1),
    ftm 0 2 2 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (2),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 0 (1),
    ftm 1 0 2 1 (-1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (2),
    ftm 1 1 1 1 (-3),
    ftm 1 1 2 0 (-1),
    ftm 1 2 0 0 (1),
    ftm 1 2 1 0 (-2),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (2),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 0 (1),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 0 (2),
    ftm 2 1 0 1 (-2),
    ftm 2 1 1 0 (-1),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 21: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct21 : Poly :=
  polyMul ([tm 2 2 1 0 0 (1)])
    (chartCore9)

/-- KERNEL-CHECKED chart soundness for flat core 21: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore21 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore21)) den one two three four
      = polyEval chartProduct21 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 22 (degree 3), denominators cleared. -/
def flatCore22 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-3),
    ftm 0 0 1 2 (2),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-3),
    ftm 0 1 1 1 (3),
    ftm 0 1 2 0 (1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-3),
    ftm 1 0 0 2 (2),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-3),
    ftm 1 1 0 1 (3),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (1)]

/-- The certificate-side product for flat core 22: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct22 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    ([tm 10 0 0 0 0 (1),
      tm 9 0 1 0 0 (1),
      tm 8 0 1 1 0 (1),
      tm 7 0 1 1 1 (1),
      tm 8 1 1 0 0 (2),
      tm 6 1 1 1 1 (1),
      tm 7 1 2 0 0 (2),
      tm 6 1 2 1 0 (2),
      tm 5 1 2 1 1 (3),
      tm 4 1 2 2 1 (1),
      tm 3 1 2 2 2 (1),
      tm 6 2 1 1 0 (1),
      tm 5 2 1 1 1 (1),
      tm 6 2 2 0 0 (1),
      tm 4 2 2 1 1 (1),
      tm 4 2 2 2 0 (2),
      tm 3 2 2 2 1 (3),
      tm 2 2 2 2 2 (1),
      tm 5 2 3 0 0 (1),
      tm 4 2 3 1 0 (1),
      tm 3 2 3 1 1 (2),
      tm 2 2 3 2 1 (1),
      tm 1 2 3 2 2 (1),
      tm 2 2 3 3 0 (1),
      tm 1 2 3 3 1 (2),
      tm 0 2 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 22: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore22 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore22)) den one two three four
      = polyEval chartProduct22 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 23 (degree 4), denominators cleared. -/
def flatCore23 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (2),
    ftm 0 2 1 0 (-2),
    ftm 0 2 2 0 (2),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-3),
    ftm 1 1 1 1 (3),
    ftm 1 1 2 0 (1),
    ftm 1 2 0 0 (-1),
    ftm 1 2 1 0 (3),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (1),
    ftm 2 2 0 0 (1)]

/-- The certificate-side product for flat core 23: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct23 : Poly :=
  polyMul ([tm 3 2 0 0 0 (-1)])
    (chartCore10)

/-- KERNEL-CHECKED chart soundness for flat core 23: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore23 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore23)) den one two three four
      = polyEval chartProduct23 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 24 (degree 4), denominators cleared. -/
def flatCore24 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (2),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 1 1 (3),
    ftm 0 3 1 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (-4),
    ftm 1 1 0 2 (2),
    ftm 1 1 1 1 (1),
    ftm 1 2 0 0 (-2),
    ftm 1 2 0 1 (3),
    ftm 1 3 0 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 24: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct24 : Poly :=
  polyMul ([tm 3 0 0 0 0 (1)])
    (chartCore11)

/-- KERNEL-CHECKED chart soundness for flat core 24: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore24 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore24)) den one two three four
      = polyEval chartProduct24 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 25 (degree 4), denominators cleared. -/
def flatCore25 : FlatPoly :=
  [ftm 0 1 2 1 (1),
    ftm 0 2 2 0 (1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 1 0 (-3),
    ftm 1 1 1 1 (4),
    ftm 1 1 2 0 (1),
    ftm 1 2 1 0 (3),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (1),
    ftm 2 2 0 0 (1)]

/-- The certificate-side product for flat core 25: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct25 : Poly :=
  polyMul ([tm 4 3 1 0 0 (1)])
    (chartCore12)

/-- KERNEL-CHECKED chart soundness for flat core 25: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore25 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore25)) den one two three four
      = polyEval chartProduct25 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 26 (degree 3), denominators cleared. -/
def flatCore26 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (2),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 1 (3),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 1 (-3),
    ftm 1 0 0 2 (2),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (3),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 26: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct26 : Poly :=
  polyMul ([tm 3 1 0 0 0 (1)])
    (chartCore13)

/-- KERNEL-CHECKED chart soundness for flat core 26: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore26 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore26)) den one two three four
      = polyEval chartProduct26 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 27 (degree 3), denominators cleared. -/
def flatCore27 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (2),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 27: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct27 : Poly :=
  polyMul ([tm 3 2 1 0 0 (1)])
    (chartCore14)

/-- KERNEL-CHECKED chart soundness for flat core 27: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore27 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore27)) den one two three four
      = polyEval chartProduct27 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 28 (degree 2), denominators cleared. -/
def flatCore28 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 2 0 (-1),
    ftm 0 1 1 0 (-2),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 1 0 (-1),
    ftm 1 1 0 0 (-1)]

/-- The certificate-side product for flat core 28: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct28 : Poly :=
  polyMul ([tm 1 1 0 0 0 (-1)])
    (chartCore15)

/-- KERNEL-CHECKED chart soundness for flat core 28: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore28 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore28)) den one two three four
      = polyEval chartProduct28 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 29 (degree 3), denominators cleared. -/
def flatCore29 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 2 0 0 (1)]

/-- The certificate-side product for flat core 29: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct29 : Poly :=
  polyMul ([tm 3 1 0 0 0 (1)])
    (chartCore16)

/-- KERNEL-CHECKED chart soundness for flat core 29: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore29 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore29)) den one two three four
      = polyEval chartProduct29 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 30 (degree 2), denominators cleared. -/
def flatCore30 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 1 1 0 (1),
    ftm 1 0 0 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 1 0 (1),
    ftm 1 1 0 0 (1),
    ftm 2 0 0 0 (1)]

/-- The certificate-side product for flat core 30: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct30 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    (chartCore17)

/-- KERNEL-CHECKED chart soundness for flat core 30: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore30 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore30)) den one two three four
      = polyEval chartProduct30 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 31 (degree 3), denominators cleared. -/
def flatCore31 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-3),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (2),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-3),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (2),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-3),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (3),
    ftm 1 1 0 0 (-3),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (3),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 31: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct31 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    ([tm 9 0 1 0 0 (1),
      tm 7 0 1 1 1 (1),
      tm 9 1 0 0 0 (1),
      tm 7 1 1 1 0 (2),
      tm 6 1 1 1 1 (1),
      tm 7 1 2 0 0 (2),
      tm 5 1 2 1 1 (3),
      tm 5 1 2 2 0 (1),
      tm 4 1 2 2 1 (1),
      tm 3 1 2 2 2 (1),
      tm 7 2 1 0 0 (1),
      tm 6 2 1 1 0 (1),
      tm 5 2 1 1 1 (1),
      tm 5 2 2 1 0 (2),
      tm 4 2 2 1 1 (1),
      tm 4 2 2 2 0 (2),
      tm 3 2 2 2 1 (3),
      tm 2 2 2 2 2 (1),
      tm 5 2 3 0 0 (1),
      tm 3 2 3 1 1 (2),
      tm 3 2 3 2 0 (1),
      tm 2 2 3 2 1 (1),
      tm 1 2 3 2 2 (1),
      tm 2 2 3 3 0 (1),
      tm 1 2 3 3 1 (2),
      tm 0 2 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 31: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore31 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore31)) den one two three four
      = polyEval chartProduct31 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 32 (degree 4), denominators cleared. -/
def flatCore32 : FlatPoly :=
  [ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (-2),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (3),
    ftm 1 2 0 0 (-2),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (2),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (2),
    ftm 2 2 0 0 (1)]

/-- The certificate-side product for flat core 32: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct32 : Poly :=
  polyMul ([tm 3 2 1 0 0 (1)])
    (chartCore18)

/-- KERNEL-CHECKED chart soundness for flat core 32: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore32 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore32)) den one two three four
      = polyEval chartProduct32 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 33 (degree 4), denominators cleared. -/
def flatCore33 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-2),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (2),
    ftm 1 1 0 0 (1),
    ftm 1 1 1 0 (-4),
    ftm 1 1 1 1 (1),
    ftm 1 1 2 0 (2),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (3),
    ftm 2 1 0 0 (-2),
    ftm 2 1 1 0 (3),
    ftm 3 0 0 1 (1),
    ftm 3 1 0 0 (1)]

/-- The certificate-side product for flat core 33: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct33 : Poly :=
  polyMul ([tm 3 2 0 0 0 (-1)])
    (chartCore19)

/-- KERNEL-CHECKED chart soundness for flat core 33: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore33 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore33)) den one two three four
      = polyEval chartProduct33 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 34 (degree 4), denominators cleared. -/
def flatCore34 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 1 2 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 1 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (2),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (-3),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (3),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (2),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (3),
    ftm 2 2 0 0 (1)]

/-- The certificate-side product for flat core 34: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct34 : Poly :=
  polyMul ([tm 3 0 0 0 0 (1)])
    (chartCore20)

/-- KERNEL-CHECKED chart soundness for flat core 34: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore34 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore34)) den one two three four
      = polyEval chartProduct34 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 35 (degree 3), denominators cleared. -/
def flatCore35 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (2),
    ftm 0 1 1 0 (-3),
    ftm 0 1 1 1 (2),
    ftm 0 1 2 0 (2),
    ftm 0 2 1 0 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (3),
    ftm 1 1 0 0 (-1),
    ftm 1 1 1 0 (3),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 35: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct35 : Poly :=
  polyMul ([tm 3 2 0 0 0 (1)])
    (chartCore21)

/-- KERNEL-CHECKED chart soundness for flat core 35: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore35 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore35)) den one two three four
      = polyEval chartProduct35 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 36 (degree 4), denominators cleared. -/
def flatCore36 : FlatPoly :=
  [ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 1 (1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (-3),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 1 (4),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (3),
    ftm 2 2 0 0 (1)]

/-- The certificate-side product for flat core 36: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct36 : Poly :=
  polyMul ([tm 5 2 1 1 0 (1)])
    (chartCore22)

/-- KERNEL-CHECKED chart soundness for flat core 36: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore36 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore36)) den one two three four
      = polyEval chartProduct36 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 37 (degree 2), denominators cleared. -/
def flatCore37 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-2),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-1),
    ftm 1 0 0 1 (-2),
    ftm 1 1 0 0 (-1)]

/-- The certificate-side product for flat core 37: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct37 : Poly :=
  polyMul ([tm 2 1 0 0 0 (-1)])
    (chartCore23)

/-- KERNEL-CHECKED chart soundness for flat core 37: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore37 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore37)) den one two three four
      = polyEval chartProduct37 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 38 (degree 3), denominators cleared. -/
def flatCore38 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 1 1 (-1),
    ftm 1 1 0 0 (1),
    ftm 1 1 1 0 (-2),
    ftm 2 0 0 1 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 38: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct38 : Poly :=
  polyMul ([tm 3 2 1 1 0 (-1)])
    (chartCore24)

/-- KERNEL-CHECKED chart soundness for flat core 38: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore38 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore38)) den one two three four
      = polyEval chartProduct38 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 39 (degree 3), denominators cleared. -/
def flatCore39 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 1 1 (-1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 39: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct39 : Poly :=
  polyMul ([tm 3 1 0 0 0 (-1)])
    (chartCore25)

/-- KERNEL-CHECKED chart soundness for flat core 39: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore39 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore39)) den one two three four
      = polyEval chartProduct39 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 40 (degree 2), denominators cleared. -/
def flatCore40 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 1 0 0 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 1 0 (1),
    ftm 0 2 0 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 1 0 0 (1)]

/-- The certificate-side product for flat core 40: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct40 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore26)

/-- KERNEL-CHECKED chart soundness for flat core 40: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore40 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore40)) den one two three four
      = polyEval chartProduct40 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 41 (degree 4), denominators cleared. -/
def flatCore41 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 1 2 1 (-1),
    ftm 0 2 1 0 (1),
    ftm 0 2 2 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (3),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 0 (1),
    ftm 1 0 2 1 (-2),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (3),
    ftm 1 1 1 1 (-3),
    ftm 1 1 2 0 (-2),
    ftm 1 2 0 0 (1),
    ftm 1 2 1 0 (-2),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (3),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 0 (1),
    ftm 2 0 1 1 (-3),
    ftm 2 1 0 0 (3),
    ftm 2 1 0 1 (-2),
    ftm 2 1 1 0 (-3),
    ftm 2 2 0 0 (-1),
    ftm 3 0 0 1 (-1),
    ftm 3 1 0 0 (-1)]

/-- The certificate-side product for flat core 41: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct41 : Poly :=
  polyMul ([tm 2 2 1 0 0 (1)])
    (chartCore27)

/-- KERNEL-CHECKED chart soundness for flat core 41: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore41 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore41)) den one two three four
      = polyEval chartProduct41 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 42 (degree 4), denominators cleared. -/
def flatCore42 : FlatPoly :=
  [ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-3),
    ftm 0 1 1 2 (2),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-3),
    ftm 0 2 1 1 (3),
    ftm 0 2 2 0 (1),
    ftm 0 3 1 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (-3),
    ftm 1 1 0 2 (2),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (3),
    ftm 1 2 0 0 (-3),
    ftm 1 2 0 1 (3),
    ftm 1 2 1 0 (2),
    ftm 1 3 0 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (2),
    ftm 2 2 0 0 (1)]

/-- The certificate-side product for flat core 42: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct42 : Poly :=
  polyMul ([tm 3 2 1 0 0 (1)])
    (chartCore28)

/-- KERNEL-CHECKED chart soundness for flat core 42: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore42 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore42)) den one two three four
      = polyEval chartProduct42 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 43 (degree 4), denominators cleared. -/
def flatCore43 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (2),
    ftm 0 2 1 0 (-2),
    ftm 0 2 2 0 (2),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-2),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (2),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-4),
    ftm 1 1 1 1 (3),
    ftm 1 1 2 0 (2),
    ftm 1 2 0 0 (-1),
    ftm 1 2 1 0 (3),
    ftm 2 0 0 1 (-1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (3),
    ftm 2 1 0 0 (-2),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (3),
    ftm 2 2 0 0 (1),
    ftm 3 0 0 1 (1),
    ftm 3 1 0 0 (1)]

/-- The certificate-side product for flat core 43: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct43 : Poly :=
  polyMul ([tm 3 2 0 0 0 (-1)])
    (chartCore29)

/-- KERNEL-CHECKED chart soundness for flat core 43: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore43 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore43)) den one two three four
      = polyEval chartProduct43 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 44 (degree 4), denominators cleared. -/
def flatCore44 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (2),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 1 1 (3),
    ftm 0 3 1 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (2),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (-4),
    ftm 1 1 0 2 (2),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (3),
    ftm 1 2 0 0 (-2),
    ftm 1 2 0 1 (3),
    ftm 1 2 1 0 (1),
    ftm 1 3 0 0 (1),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (2),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (3),
    ftm 2 2 0 0 (1)]

/-- The certificate-side product for flat core 44: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct44 : Poly :=
  polyMul ([tm 3 0 0 0 0 (1)])
    (chartCore30)

/-- KERNEL-CHECKED chart soundness for flat core 44: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore44 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore44)) den one two three four
      = polyEval chartProduct44 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 45 (degree 4), denominators cleared. -/
def flatCore45 : FlatPoly :=
  [ftm 0 1 2 1 (1),
    ftm 0 2 2 0 (1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (2),
    ftm 1 1 1 0 (-3),
    ftm 1 1 1 1 (4),
    ftm 1 1 2 0 (2),
    ftm 1 2 1 0 (3),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (3),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (3),
    ftm 2 2 0 0 (1),
    ftm 3 0 0 1 (1),
    ftm 3 1 0 0 (1)]

/-- The certificate-side product for flat core 45: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct45 : Poly :=
  polyMul ([tm 4 3 1 0 0 (1)])
    (chartCore31)

/-- KERNEL-CHECKED chart soundness for flat core 45: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore45 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore45)) den one two three four
      = polyEval chartProduct45 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 46 (degree 4), denominators cleared. -/
def flatCore46 : FlatPoly :=
  [ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (2),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 1 (3),
    ftm 0 3 1 0 (1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (-3),
    ftm 1 1 0 2 (2),
    ftm 1 1 1 1 (4),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (3),
    ftm 1 2 1 0 (1),
    ftm 1 3 0 0 (1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (3),
    ftm 2 2 0 0 (1)]

/-- The certificate-side product for flat core 46: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct46 : Poly :=
  polyMul ([tm 5 2 1 0 0 (1)])
    (chartCore32)

/-- KERNEL-CHECKED chart soundness for flat core 46: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore46 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore46)) den one two three four
      = polyEval chartProduct46 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 47 (degree 3), denominators cleared. -/
def flatCore47 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 1 (2),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 47: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct47 : Poly :=
  polyMul ([tm 3 2 1 0 0 (1)])
    (chartCore33)

/-- KERNEL-CHECKED chart soundness for flat core 47: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore47 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore47)) den one two three four
      = polyEval chartProduct47 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 48 (degree 3), denominators cleared. -/
def flatCore48 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-1),
    ftm 0 2 1 0 (-2),
    ftm 1 0 1 1 (-1),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-2),
    ftm 1 2 0 0 (-1),
    ftm 2 0 0 1 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 48: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct48 : Poly :=
  polyMul ([tm 3 2 1 0 0 (-1)])
    (chartCore34)

/-- KERNEL-CHECKED chart soundness for flat core 48: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore48 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore48)) den one two three four
      = polyEval chartProduct48 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 49 (degree 3), denominators cleared. -/
def flatCore49 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 1 1 1 (1),
    ftm 0 2 1 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 49: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct49 : Poly :=
  polyMul ([tm 3 1 0 0 0 (1)])
    (chartCore35)

/-- KERNEL-CHECKED chart soundness for flat core 49: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore49 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore49)) den one two three four
      = polyEval chartProduct49 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 50 (degree 3), denominators cleared. -/
def flatCore50 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 0 (-1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 0 (1),
    ftm 0 1 0 1 (1),
    ftm 0 1 1 1 (-1),
    ftm 1 0 0 0 (-1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 50: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct50 : Poly :=
  polyMul ([tm 1 0 0 0 0 (1)])
    (chartCore36)

/-- KERNEL-CHECKED chart soundness for flat core 50: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore50 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore50)) den one two three four
      = polyEval chartProduct50 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 51 (degree 4), denominators cleared. -/
def flatCore51 : FlatPoly :=
  [ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 1 (-1),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (1),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-1),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (-2),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 51: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct51 : Poly :=
  polyMul ([tm 4 2 1 0 0 (1)])
    (chartCore37)

/-- KERNEL-CHECKED chart soundness for flat core 51: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore51 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore51)) den one two three four
      = polyEval chartProduct51 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 52 (degree 4), denominators cleared. -/
def flatCore52 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 0 2 0 (-1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (2),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 0 (1),
    ftm 2 1 1 0 (-1),
    ftm 3 0 0 1 (-1),
    ftm 3 1 0 0 (-1)]

/-- The certificate-side product for flat core 52: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct52 : Poly :=
  polyMul ([tm 4 1 0 0 0 (-1)])
    (chartCore38)

/-- KERNEL-CHECKED chart soundness for flat core 52: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore52 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore52)) den one two three four
      = polyEval chartProduct52 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 53 (degree 4), denominators cleared. -/
def flatCore53 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 1 2 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 1 (-1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (-1),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 53: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct53 : Poly :=
  polyMul ([tm 4 0 0 0 0 (1)])
    ([tm 12 0 0 0 0 (1),
      tm 11 1 0 0 0 (1),
      tm 10 1 1 0 0 (2),
      tm 9 1 1 1 0 (1),
      tm 8 1 1 1 1 (2),
      tm 9 2 1 0 0 (2),
      tm 7 2 1 1 1 (1),
      tm 8 2 2 0 0 (1),
      tm 7 2 2 1 0 (2),
      tm 6 2 2 1 1 (3),
      tm 5 2 2 2 1 (1),
      tm 4 2 2 2 2 (1),
      tm 7 3 2 0 0 (1),
      tm 5 3 2 1 1 (1),
      tm 5 3 3 1 0 (1),
      tm 4 3 3 1 1 (1),
      tm 3 3 3 2 1 (1),
      tm 2 3 3 2 2 (1),
      tm 5 4 2 1 0 (1),
      tm 3 4 3 2 0 (2),
      tm 2 4 3 2 1 (1),
      tm 1 4 4 3 0 (1),
      tm 0 4 4 3 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 53: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore53 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore53)) den one two three four
      = polyEval chartProduct53 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 54 (degree 3), denominators cleared. -/
def flatCore54 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (2),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (-1),
    ftm 1 1 1 0 (-1),
    ftm 2 0 0 1 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 54: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct54 : Poly :=
  polyMul ([tm 3 1 0 0 0 (1)])
    (chartCore39)

/-- KERNEL-CHECKED chart soundness for flat core 54: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore54 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore54)) den one two three four
      = polyEval chartProduct54 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 55 (degree 4), denominators cleared. -/
def flatCore55 : FlatPoly :=
  [ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 1 (1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 0 2 (1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (-1),
    ftm 2 0 0 2 (-1),
    ftm 2 1 0 1 (-1),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 55: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct55 : Poly :=
  polyMul ([tm 6 1 1 1 0 (1)])
    (chartCore40)

/-- KERNEL-CHECKED chart soundness for flat core 55: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore55 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore55)) den one two three four
      = polyEval chartProduct55 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 56 (degree 2), denominators cleared. -/
def flatCore56 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 1 0 1 (1),
    ftm 0 1 1 0 (-1),
    ftm 1 1 0 0 (-1)]

/-- The certificate-side product for flat core 56: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct56 : Poly :=
  polyMul ([tm 3 0 0 0 0 (1)])
    (chartCore41)

/-- KERNEL-CHECKED chart soundness for flat core 56: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore56 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore56)) den one two three four
      = polyEval chartProduct56 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 57 (degree 3), denominators cleared. -/
def flatCore57 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 1 1 (1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 57: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct57 : Poly :=
  polyMul ([tm 4 1 1 1 0 (-1)])
    (chartCore42)

/-- KERNEL-CHECKED chart soundness for flat core 57: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore57 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore57)) den one two three four
      = polyEval chartProduct57 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 58 (degree 2), denominators cleared. -/
def flatCore58 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 1 0 0 (-1)]

/-- The certificate-side product for flat core 58: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct58 : Poly :=
  polyMul ([tm 3 1 1 0 0 (1)])
    (chartCore43)

/-- KERNEL-CHECKED chart soundness for flat core 58: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore58 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore58)) den one two three four
      = polyEval chartProduct58 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 59 (degree 3), denominators cleared. -/
def flatCore59 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 59: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct59 : Poly :=
  polyMul ([tm 4 1 1 0 0 (-1)])
    (chartCore44)

/-- KERNEL-CHECKED chart soundness for flat core 59: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore59 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore59)) den one two three four
      = polyEval chartProduct59 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 60 (degree 4), denominators cleared. -/
def flatCore60 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 1 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 0 (-1),
    ftm 1 1 1 1 (-1),
    ftm 2 0 0 0 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (-1),
    ftm 2 1 1 0 (-1),
    ftm 3 0 0 1 (-1),
    ftm 3 1 0 0 (-1)]

/-- The certificate-side product for flat core 60: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct60 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    ([tm 13 0 0 0 0 (1),
      tm 11 1 1 0 0 (2),
      tm 10 1 1 1 0 (1),
      tm 9 1 1 1 1 (1),
      tm 8 1 2 2 0 (1),
      tm 9 2 1 1 0 (1),
      tm 9 2 2 0 0 (1),
      tm 8 2 2 1 0 (2),
      tm 7 2 2 1 1 (1),
      tm 7 2 2 2 0 (2),
      tm 6 2 2 2 1 (2),
      tm 6 2 3 2 0 (2),
      tm 5 2 3 3 0 (1),
      tm 4 2 3 3 1 (2),
      tm 7 3 2 1 0 (1),
      tm 6 3 2 2 0 (1),
      tm 5 3 2 2 1 (1),
      tm 6 3 3 1 0 (1),
      tm 5 3 3 2 0 (2),
      tm 4 3 3 2 1 (2),
      tm 4 3 3 3 0 (2),
      tm 3 3 3 3 1 (3),
      tm 2 3 3 3 2 (1),
      tm 4 3 4 2 0 (1),
      tm 3 3 4 3 0 (1),
      tm 2 3 4 3 1 (2),
      tm 2 3 4 4 0 (1),
      tm 1 3 4 4 1 (2),
      tm 0 3 4 4 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 60: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore60 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore60)) den one two three four
      = polyEval chartProduct60 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 61 (degree 4), denominators cleared. -/
def flatCore61 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 1 3 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (2),
    ftm 1 0 0 3 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 1 (-1),
    ftm 1 2 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-1),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (-2),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 61: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct61 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    (chartCore45)

/-- KERNEL-CHECKED chart soundness for flat core 61: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore61 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore61)) den one two three four
      = polyEval chartProduct61 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 62 (degree 4), denominators cleared. -/
def flatCore62 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 2 0 (-2),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-2),
    ftm 1 0 2 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (-1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (2),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (-1),
    ftm 3 0 0 1 (-1),
    ftm 3 1 0 0 (-1)]

/-- The certificate-side product for flat core 62: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct62 : Poly :=
  polyMul ([tm 4 1 0 0 0 (1)])
    (chartCore46)

/-- KERNEL-CHECKED chart soundness for flat core 62: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore62 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore62)) den one two three four
      = polyEval chartProduct62 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 63 (degree 4), denominators cleared. -/
def flatCore63 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 3 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 2 (-1),
    ftm 0 2 0 1 (-1),
    ftm 1 0 0 3 (-1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 1 (-1),
    ftm 1 2 1 0 (-1),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 63: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct63 : Poly :=
  polyMul ([tm 4 0 0 0 0 (1)])
    ([tm 12 0 0 0 0 (1),
      tm 11 1 0 0 0 (1),
      tm 10 1 1 0 0 (2),
      tm 9 1 1 1 0 (1),
      tm 8 1 1 1 1 (2),
      tm 10 2 0 0 0 (1),
      tm 9 2 1 0 0 (2),
      tm 8 2 1 1 0 (2),
      tm 7 2 1 1 1 (2),
      tm 8 2 2 0 0 (1),
      tm 7 2 2 1 0 (2),
      tm 6 2 2 1 1 (3),
      tm 6 2 2 2 0 (1),
      tm 5 2 2 2 1 (2),
      tm 4 2 2 2 2 (1),
      tm 8 3 1 0 0 (1),
      tm 7 3 2 0 0 (1),
      tm 6 3 2 1 0 (2),
      tm 5 3 2 1 1 (2),
      tm 5 3 3 1 0 (1),
      tm 4 3 3 1 1 (1),
      tm 4 3 3 2 0 (1),
      tm 3 3 3 2 1 (2),
      tm 2 3 3 2 2 (1),
      tm 5 4 2 1 0 (1),
      tm 3 4 3 2 0 (2),
      tm 2 4 3 2 1 (1),
      tm 1 4 4 3 0 (1),
      tm 0 4 4 3 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 63: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore63 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore63)) den one two three four
      = polyEval chartProduct63 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 64 (degree 4), denominators cleared. -/
def flatCore64 : FlatPoly :=
  [ftm 0 0 2 2 (1),
    ftm 0 1 2 1 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (1),
    ftm 1 1 1 0 (2),
    ftm 1 2 1 0 (-1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (1),
    ftm 3 0 0 1 (1),
    ftm 3 1 0 0 (1)]

/-- The certificate-side product for flat core 64: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct64 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    (chartCore47)

/-- KERNEL-CHECKED chart soundness for flat core 64: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore64 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore64)) den one two three four
      = polyEval chartProduct64 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 65 (degree 4), denominators cleared. -/
def flatCore65 : FlatPoly :=
  [ftm 0 0 1 3 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 0 2 (1),
    ftm 0 1 1 1 (2),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 1 (-1),
    ftm 0 2 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 0 3 (1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1),
    ftm 2 2 0 0 (1)]

/-- The certificate-side product for flat core 65: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct65 : Poly :=
  polyMul ([tm 6 1 0 0 0 (1)])
    (chartCore48)

/-- KERNEL-CHECKED chart soundness for flat core 65: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore65 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore65)) den one two three four
      = polyEval chartProduct65 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 66 (degree 3), denominators cleared. -/
def flatCore66 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 1 1 1 (1),
    ftm 1 1 1 0 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 66: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct66 : Poly :=
  polyMul ([tm 4 1 0 0 0 (1)])
    ([tm 7 0 0 0 0 (1),
      tm 5 1 1 0 0 (1),
      tm 2 2 2 1 0 (1),
      tm 0 2 3 2 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 66: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore66 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore66)) den one two three four
      = polyEval chartProduct66 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 67 (degree 3), denominators cleared. -/
def flatCore67 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 1 1 0 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 1 (1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 67: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct67 : Poly :=
  polyMul ([tm 4 1 0 0 0 (1)])
    (chartCore49)

/-- KERNEL-CHECKED chart soundness for flat core 67: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore67 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore67)) den one two three four
      = polyEval chartProduct67 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 68 (degree 3), denominators cleared. -/
def flatCore68 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 68: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct68 : Poly :=
  polyMul ([tm 4 1 0 0 0 (1)])
    (chartCore50)

/-- KERNEL-CHECKED chart soundness for flat core 68: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore68 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore68)) den one two three four
      = polyEval chartProduct68 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 69 (degree 3), denominators cleared. -/
def flatCore69 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 0 (-1),
    ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-1),
    ftm 1 0 0 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-1)]

/-- The certificate-side product for flat core 69: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct69 : Poly :=
  polyMul ([tm 1 0 0 0 0 (1)])
    (chartCore51)

/-- KERNEL-CHECKED chart soundness for flat core 69: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore69 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore69)) den one two three four
      = polyEval chartProduct69 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 70 (degree 4), denominators cleared. -/
def flatCore70 : FlatPoly :=
  [ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (1),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (1)]

/-- The certificate-side product for flat core 70: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct70 : Poly :=
  polyMul ([tm 4 2 1 0 0 (1)])
    (chartCore52)

/-- KERNEL-CHECKED chart soundness for flat core 70: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore70 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore70)) den one two three four
      = polyEval chartProduct70 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 71 (degree 4), denominators cleared. -/
def flatCore71 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (1),
    ftm 1 1 2 0 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 1 0 (1)]

/-- The certificate-side product for flat core 71: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct71 : Poly :=
  polyMul ([tm 4 1 0 0 0 (-1)])
    (chartCore53)

/-- KERNEL-CHECKED chart soundness for flat core 71: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore71 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore71)) den one two three four
      = polyEval chartProduct71 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 72 (degree 3), denominators cleared. -/
def flatCore72 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 72: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct72 : Poly :=
  polyMul ([tm 2 0 0 0 0 (1)])
    (chartCore54)

/-- KERNEL-CHECKED chart soundness for flat core 72: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore72 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore72)) den one two three four
      = polyEval chartProduct72 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 73 (degree 3), denominators cleared. -/
def flatCore73 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (2),
    ftm 0 1 2 0 (1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 1 0 (1)]

/-- The certificate-side product for flat core 73: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct73 : Poly :=
  polyMul ([tm 3 1 0 0 0 (1)])
    ([tm 8 0 0 0 0 (1),
      tm 6 0 1 1 0 (1),
      tm 7 1 0 0 0 (1),
      tm 6 1 1 0 0 (1),
      tm 5 1 1 1 0 (2),
      tm 4 1 1 1 1 (1),
      tm 4 1 2 1 0 (1),
      tm 3 1 2 2 0 (1),
      tm 2 1 2 2 1 (1),
      tm 3 2 1 1 1 (1),
      tm 1 2 2 2 1 (1),
      tm 0 2 2 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 73: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore73 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore73)) den one two three four
      = polyEval chartProduct73 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 74 (degree 3), denominators cleared. -/
def flatCore74 : FlatPoly :=
  [ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (2),
    ftm 1 2 0 0 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 74: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct74 : Poly :=
  polyMul ([tm 2 1 1 1 0 (1)])
    ([tm 7 0 0 0 0 (1),
      tm 6 1 0 0 0 (1),
      tm 5 1 1 0 0 (2),
      tm 4 1 1 0 1 (1),
      tm 4 1 1 1 0 (1),
      tm 3 1 1 1 1 (1),
      tm 4 2 1 0 0 (1),
      tm 3 2 2 0 0 (1),
      tm 2 2 2 0 1 (1),
      tm 2 2 2 1 0 (1),
      tm 1 2 2 1 1 (1),
      tm 0 2 2 1 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 74: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore74 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore74)) den one two three four
      = polyEval chartProduct74 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 75 (degree 1), denominators cleared. -/
def flatCore75 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 1 0 (1),
    ftm 0 1 0 0 (1),
    ftm 1 0 0 0 (1)]

/-- The certificate-side product for flat core 75: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct75 : Poly :=
  polyMul ([tm 1 0 0 0 0 (1)])
    ([tm 3 0 0 0 0 (1),
      tm 2 1 0 0 0 (1),
      tm 1 1 1 0 0 (1),
      tm 0 1 1 1 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 75: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore75 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 1 flatCore75)) den one two three four
      = polyEval chartProduct75 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 76 (degree 3), denominators cleared. -/
def flatCore76 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 1 1 0 (-1)]

/-- The certificate-side product for flat core 76: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct76 : Poly :=
  polyMul ([tm 5 1 1 1 0 (-1)])
    (chartCore55)

/-- KERNEL-CHECKED chart soundness for flat core 76: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore76 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore76)) den one two three four
      = polyEval chartProduct76 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 77 (degree 3), denominators cleared. -/
def flatCore77 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (1)]

/-- The certificate-side product for flat core 77: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct77 : Poly :=
  polyMul ([tm 5 1 0 0 0 (1)])
    (chartCore56)

/-- KERNEL-CHECKED chart soundness for flat core 77: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore77 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore77)) den one two three four
      = polyEval chartProduct77 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 78 (degree 4), denominators cleared. -/
def flatCore78 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 1 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (-1),
    ftm 1 1 2 0 (1),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 0 (-1),
    ftm 2 1 1 0 (1)]

/-- The certificate-side product for flat core 78: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct78 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    ([tm 13 0 0 0 0 (1),
      tm 11 1 1 0 0 (2),
      tm 9 1 1 1 1 (1),
      tm 9 2 1 1 0 (1),
      tm 9 2 2 0 0 (1),
      tm 7 2 2 1 1 (1),
      tm 7 2 2 2 0 (2),
      tm 6 2 2 2 1 (1),
      tm 5 2 3 3 0 (1),
      tm 4 2 3 3 1 (1),
      tm 7 3 2 1 0 (1),
      tm 6 3 2 2 0 (1),
      tm 5 3 2 2 1 (1),
      tm 5 3 3 2 0 (2),
      tm 4 3 3 2 1 (1),
      tm 4 3 3 3 0 (2),
      tm 3 3 3 3 1 (3),
      tm 2 3 3 3 2 (1),
      tm 3 3 4 3 0 (1),
      tm 2 3 4 3 1 (1),
      tm 2 3 4 4 0 (1),
      tm 1 3 4 4 1 (2),
      tm 0 3 4 4 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 78: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore78 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore78)) den one two three four
      = polyEval chartProduct78 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 79 (degree 4), denominators cleared. -/
def flatCore79 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 1 3 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (2),
    ftm 1 0 0 3 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (1),
    ftm 1 2 0 0 (-1),
    ftm 1 2 1 0 (1)]

/-- The certificate-side product for flat core 79: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct79 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    (chartCore57)

/-- KERNEL-CHECKED chart soundness for flat core 79: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore79 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore79)) den one two three four
      = polyEval chartProduct79 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 80 (degree 4), denominators cleared. -/
def flatCore80 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 2 0 (-2),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 2 (-2),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (-1),
    ftm 1 1 2 0 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (1)]

/-- The certificate-side product for flat core 80: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct80 : Poly :=
  polyMul ([tm 4 1 0 0 0 (1)])
    (chartCore58)

/-- KERNEL-CHECKED chart soundness for flat core 80: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore80 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore80)) den one two three four
      = polyEval chartProduct80 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 81 (degree 3), denominators cleared. -/
def flatCore81 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 1 (-1),
    ftm 0 2 0 0 (-1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (1),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 81: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct81 : Poly :=
  polyMul ([tm 2 0 0 0 0 (1)])
    (chartCore59)

/-- KERNEL-CHECKED chart soundness for flat core 81: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore81 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore81)) den one two three four
      = polyEval chartProduct81 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 82 (degree 4), denominators cleared. -/
def flatCore82 : FlatPoly :=
  [ftm 0 0 2 2 (1),
    ftm 0 1 2 1 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (1),
    ftm 1 0 2 1 (-1),
    ftm 1 1 1 0 (2),
    ftm 1 1 2 0 (-1),
    ftm 1 2 1 0 (-1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (1),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (-1)]

/-- The certificate-side product for flat core 82: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct82 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    (chartCore60)

/-- KERNEL-CHECKED chart soundness for flat core 82: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore82 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore82)) den one two three four
      = polyEval chartProduct82 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 83 (degree 3), denominators cleared. -/
def flatCore83 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 1 0 0 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 1 0 (2),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 0 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (-2),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 83: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct83 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore61)

/-- KERNEL-CHECKED chart soundness for flat core 83: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore83 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore83)) den one two three four
      = polyEval chartProduct83 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 84 (degree 2), denominators cleared. -/
def flatCore84 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 1 1 0 (1),
    ftm 1 0 1 0 (-1),
    ftm 2 0 0 0 (-1)]

/-- The certificate-side product for flat core 84: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct84 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore62)

/-- KERNEL-CHECKED chart soundness for flat core 84: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore84 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore84)) den one two three four
      = polyEval chartProduct84 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 85 (degree 3), denominators cleared. -/
def flatCore85 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 1 1 0 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (-1)]

/-- The certificate-side product for flat core 85: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct85 : Poly :=
  polyMul ([tm 5 1 0 0 0 (1)])
    (chartCore63)

/-- KERNEL-CHECKED chart soundness for flat core 85: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore85 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore85)) den one two three four
      = polyEval chartProduct85 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 86 (degree 3), denominators cleared. -/
def flatCore86 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (-1)]

/-- The certificate-side product for flat core 86: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct86 : Poly :=
  polyMul ([tm 5 1 0 0 0 (1)])
    (chartCore64)

/-- KERNEL-CHECKED chart soundness for flat core 86: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore86 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore86)) den one two three four
      = polyEval chartProduct86 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 87 (degree 3), denominators cleared. -/
def flatCore87 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 1 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 87: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct87 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    ([tm 10 0 0 0 0 (1),
      tm 8 0 1 1 0 (1),
      tm 7 0 1 1 1 (1),
      tm 9 1 0 0 0 (1),
      tm 8 1 1 0 0 (2),
      tm 7 1 1 1 0 (2),
      tm 6 1 1 1 1 (2),
      tm 6 1 2 1 0 (2),
      tm 5 1 2 1 1 (1),
      tm 5 1 2 2 0 (1),
      tm 4 1 2 2 1 (2),
      tm 3 1 2 2 2 (1),
      tm 7 2 1 0 0 (1),
      tm 6 2 1 1 0 (1),
      tm 5 2 1 1 1 (1),
      tm 6 2 2 0 0 (1),
      tm 5 2 2 1 0 (2),
      tm 4 2 2 1 1 (2),
      tm 4 2 2 2 0 (2),
      tm 3 2 2 2 1 (3),
      tm 2 2 2 2 2 (1),
      tm 4 2 3 1 0 (1),
      tm 3 2 3 2 0 (1),
      tm 2 2 3 2 1 (2),
      tm 2 2 3 3 0 (1),
      tm 1 2 3 3 1 (2),
      tm 0 2 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 87: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore87 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore87)) den one two three four
      = polyEval chartProduct87 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 88 (degree 3), denominators cleared. -/
def flatCore88 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 88: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct88 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    ([tm 9 0 0 0 0 (1),
      tm 8 0 1 0 0 (1),
      tm 7 0 1 1 0 (1),
      tm 6 0 1 1 1 (1),
      tm 8 1 0 0 0 (1),
      tm 7 1 1 0 0 (2),
      tm 6 1 1 1 0 (1),
      tm 5 1 1 1 1 (2),
      tm 6 1 2 0 0 (2),
      tm 5 1 2 1 0 (2),
      tm 4 1 2 1 1 (3),
      tm 3 1 2 2 1 (1),
      tm 2 1 2 2 2 (1),
      tm 6 2 1 0 0 (1),
      tm 5 2 1 1 0 (1),
      tm 4 2 1 1 1 (1),
      tm 5 2 2 0 0 (1),
      tm 4 2 2 1 0 (1),
      tm 3 2 2 1 1 (2),
      tm 3 2 2 2 0 (2),
      tm 2 2 2 2 1 (2),
      tm 1 2 2 2 2 (1),
      tm 4 2 3 0 0 (1),
      tm 3 2 3 1 0 (1),
      tm 2 2 3 1 1 (2),
      tm 1 2 3 2 1 (1),
      tm 0 2 3 2 2 (1),
      tm 1 2 3 3 0 (1),
      tm 0 2 3 3 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 88: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore88 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore88)) den one two three four
      = polyEval chartProduct88 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 89 (degree 4), denominators cleared. -/
def flatCore89 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 0 (1),
    ftm 2 1 1 0 (-1),
    ftm 3 1 0 0 (-1)]

/-- The certificate-side product for flat core 89: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct89 : Poly :=
  polyMul ([tm 4 3 0 0 0 (1)])
    ([tm 9 0 0 0 0 (1),
      tm 8 0 1 0 0 (1),
      tm 7 0 1 1 0 (2),
      tm 6 0 1 1 1 (1),
      tm 6 0 2 1 0 (2),
      tm 5 0 2 1 1 (1),
      tm 5 0 2 2 0 (1),
      tm 4 0 2 2 1 (1),
      tm 4 0 3 2 0 (1),
      tm 8 1 0 0 0 (1),
      tm 7 1 1 0 0 (1),
      tm 6 1 1 1 0 (2),
      tm 5 1 1 1 1 (2),
      tm 6 1 2 0 0 (1),
      tm 5 1 2 1 0 (2),
      tm 4 1 2 1 1 (2),
      tm 4 1 2 2 0 (1),
      tm 3 1 2 2 1 (3),
      tm 2 1 2 2 2 (1),
      tm 4 1 3 1 0 (2),
      tm 3 1 3 1 1 (1),
      tm 3 1 3 2 0 (1),
      tm 2 1 3 2 1 (3),
      tm 1 1 3 2 2 (1),
      tm 1 1 3 3 1 (1),
      tm 0 1 3 3 2 (1),
      tm 2 1 4 2 0 (1),
      tm 0 1 4 3 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 89: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore89 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore89)) den one two three four
      = polyEval chartProduct89 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 90 (degree 4), denominators cleared. -/
def flatCore90 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 1 2 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 1 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (-2),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (-1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 0 (1),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 90: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct90 : Poly :=
  polyMul ([tm 4 0 0 0 0 (1)])
    ([tm 12 0 0 0 0 (1),
      tm 11 1 0 0 0 (1),
      tm 10 1 1 0 0 (2),
      tm 9 1 1 1 0 (1),
      tm 8 1 1 1 1 (2),
      tm 9 2 1 0 0 (2),
      tm 8 2 1 1 0 (1),
      tm 7 2 1 1 1 (1),
      tm 8 2 2 0 0 (1),
      tm 7 2 2 1 0 (2),
      tm 6 2 2 1 1 (3),
      tm 6 2 2 2 0 (1),
      tm 5 2 2 2 1 (2),
      tm 4 2 2 2 2 (1),
      tm 7 3 2 0 0 (1),
      tm 6 3 2 1 0 (1),
      tm 5 3 2 1 1 (1),
      tm 4 3 2 2 1 (1),
      tm 5 3 3 1 0 (1),
      tm 4 3 3 1 1 (1),
      tm 4 3 3 2 0 (1),
      tm 3 3 3 2 1 (2),
      tm 2 3 3 2 2 (1),
      tm 2 3 3 3 1 (1),
      tm 1 3 3 3 2 (1),
      tm 5 4 2 1 0 (1),
      tm 3 4 3 2 0 (2),
      tm 2 4 3 2 1 (1),
      tm 1 4 4 3 0 (1),
      tm 0 4 4 3 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 90: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore90 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore90)) den one two three four
      = polyEval chartProduct90 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 91 (degree 3), denominators cleared. -/
def flatCore91 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (2),
    ftm 0 2 1 0 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 1 0 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 91: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct91 : Poly :=
  polyMul ([tm 3 3 1 0 0 (-1)])
    (chartCore65)

/-- KERNEL-CHECKED chart soundness for flat core 91: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore91 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore91)) den one two three four
      = polyEval chartProduct91 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 92 (degree 3), denominators cleared. -/
def flatCore92 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 1 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 92: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct92 : Poly :=
  polyMul ([tm 4 1 1 1 0 (1)])
    (chartCore66)

/-- KERNEL-CHECKED chart soundness for flat core 92: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore92 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore92)) den one two three four
      = polyEval chartProduct92 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 93 (degree 2), denominators cleared. -/
def flatCore93 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 1 0 0 (1)]

/-- The certificate-side product for flat core 93: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct93 : Poly :=
  polyMul ([tm 3 1 1 0 0 (1)])
    ([tm 1 0 0 1 1 (1),
      tm 2 1 0 0 0 (1),
      tm 0 1 1 1 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 93: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore93 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore93)) den one two three four
      = polyEval chartProduct93 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 94 (degree 2), denominators cleared. -/
def flatCore94 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 0 2 0 (-1),
    ftm 0 1 1 0 (-1),
    ftm 2 0 0 0 (1)]

/-- The certificate-side product for flat core 94: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct94 : Poly :=
  polyMul ([tm 2 2 1 1 0 (1)])
    ([tm 2 0 0 0 0 (1),
      tm 1 0 0 0 1 (1),
      tm 0 0 1 1 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 94: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore94 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore94)) den one two three four
      = polyEval chartProduct94 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 95 (degree 3), denominators cleared. -/
def flatCore95 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-3),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (2),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-3),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (3),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 95: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct95 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    ([tm 7 0 1 1 1 (1),
      tm 9 1 0 0 0 (1),
      tm 7 1 1 1 0 (2),
      tm 6 1 1 1 1 (1),
      tm 5 1 2 1 1 (1),
      tm 5 1 2 2 0 (1),
      tm 4 1 2 2 1 (1),
      tm 3 1 2 2 2 (1),
      tm 7 2 1 0 0 (1),
      tm 6 2 1 1 0 (1),
      tm 5 2 1 1 1 (1),
      tm 5 2 2 1 0 (2),
      tm 4 2 2 1 1 (1),
      tm 4 2 2 2 0 (2),
      tm 3 2 2 2 1 (3),
      tm 2 2 2 2 2 (1),
      tm 3 2 3 2 0 (1),
      tm 2 2 3 2 1 (1),
      tm 2 2 3 3 0 (1),
      tm 1 2 3 3 1 (2),
      tm 0 2 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 95: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore95 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore95)) den one two three four
      = polyEval chartProduct95 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 96 (degree 4), denominators cleared. -/
def flatCore96 : FlatPoly :=
  [ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (2),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 96: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct96 : Poly :=
  polyMul ([tm 4 2 1 0 0 (1)])
    (chartCore67)

/-- KERNEL-CHECKED chart soundness for flat core 96: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore96 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore96)) den one two three four
      = polyEval chartProduct96 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 97 (degree 4), denominators cleared. -/
def flatCore97 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-2),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (2),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (1),
    ftm 1 1 2 0 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (3),
    ftm 2 1 1 0 (1),
    ftm 3 0 0 1 (1)]

/-- The certificate-side product for flat core 97: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct97 : Poly :=
  polyMul ([tm 4 2 0 0 0 (-1)])
    (chartCore68)

/-- KERNEL-CHECKED chart soundness for flat core 97: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore97 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore97)) den one two three four
      = polyEval chartProduct97 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 98 (degree 3), denominators cleared. -/
def flatCore98 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 1 0 (-2),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 0 (-2),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (2),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 0 (-2),
    ftm 2 0 0 1 (2),
    ftm 2 1 0 0 (2)]

/-- The certificate-side product for flat core 98: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct98 : Poly :=
  polyMul ([tm 1 0 0 0 0 (1)])
    (chartCore69)

/-- KERNEL-CHECKED chart soundness for flat core 98: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore98 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore98)) den one two three four
      = polyEval chartProduct98 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 99 (degree 3), denominators cleared. -/
def flatCore99 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (2),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (2),
    ftm 0 1 2 0 (1),
    ftm 0 2 1 0 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (3),
    ftm 1 1 1 0 (1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 99: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct99 : Poly :=
  polyMul ([tm 3 2 0 0 0 (1)])
    ([tm 7 0 0 0 0 (1),
      tm 5 0 1 1 0 (2),
      tm 3 0 2 2 0 (1),
      tm 3 1 1 1 1 (1),
      tm 1 1 2 2 1 (1),
      tm 0 1 2 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 99: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore99 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore99)) den one two three four
      = polyEval chartProduct99 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 100 (degree 3), denominators cleared. -/
def flatCore100 : FlatPoly :=
  [ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-2),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (3),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (2)]

/-- The certificate-side product for flat core 100: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct100 : Poly :=
  polyMul ([tm 2 2 1 1 0 (1)])
    ([tm 6 0 0 0 0 (1),
      tm 4 0 1 0 1 (1),
      tm 4 0 1 1 0 (1),
      tm 4 1 1 0 0 (1),
      tm 2 1 2 0 1 (1),
      tm 2 1 2 1 0 (1),
      tm 0 1 2 1 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 100: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore100 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore100)) den one two three four
      = polyEval chartProduct100 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 101 (degree 1), denominators cleared. -/
def flatCore101 : FlatPoly :=
  [ftm 0 0 0 0 (1),
    ftm 0 0 0 1 (-1),
    ftm 0 0 1 0 (-2),
    ftm 0 1 0 0 (-1),
    ftm 1 0 0 0 (-2)]

/-- The certificate-side product for flat core 101: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct101 : Poly :=
  polyMul ([tm 0 1 0 0 0 (-1)])
    (chartCore70)

/-- KERNEL-CHECKED chart soundness for flat core 101: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore101 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 1 flatCore101)) den one two three four
      = polyEval chartProduct101 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 102 (degree 3), denominators cleared. -/
def flatCore102 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 1 1 (-1),
    ftm 1 1 1 0 (-1),
    ftm 2 0 0 1 (-1)]

/-- The certificate-side product for flat core 102: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct102 : Poly :=
  polyMul ([tm 5 2 1 1 0 (-1)])
    (chartCore71)

/-- KERNEL-CHECKED chart soundness for flat core 102: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore102 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore102)) den one two three four
      = polyEval chartProduct102 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 103 (degree 4), denominators cleared. -/
def flatCore103 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (2),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 0 (1),
    ftm 1 0 2 1 (-1),
    ftm 1 1 1 1 (1),
    ftm 1 1 2 0 (-1),
    ftm 1 2 0 0 (-1),
    ftm 1 2 1 0 (2),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (2),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 0 (1),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 0 (1),
    ftm 2 1 1 0 (-1),
    ftm 2 2 0 0 (1)]

/-- The certificate-side product for flat core 103: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct103 : Poly :=
  polyMul ([tm 2 2 1 0 0 (-1)])
    (chartCore72)

/-- KERNEL-CHECKED chart soundness for flat core 103: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore103 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore103)) den one two three four
      = polyEval chartProduct103 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 104 (degree 3), denominators cleared. -/
def flatCore104 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (-1)]

/-- The certificate-side product for flat core 104: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct104 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore73)

/-- KERNEL-CHECKED chart soundness for flat core 104: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore104 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore104)) den one two three four
      = polyEval chartProduct104 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 105 (degree 4), denominators cleared. -/
def flatCore105 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 2 0 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (-1),
    ftm 1 1 2 0 (1),
    ftm 1 2 0 0 (1),
    ftm 1 2 1 0 (-1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (1),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 105: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct105 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    ([tm 7 0 2 1 0 (1),
      tm 9 1 0 0 0 (1),
      tm 7 1 1 1 0 (2),
      tm 6 1 1 1 1 (1),
      tm 5 1 2 2 0 (1),
      tm 4 1 2 2 1 (1),
      tm 5 1 3 1 0 (2),
      tm 3 1 3 2 1 (1),
      tm 8 2 0 0 0 (1),
      tm 7 2 1 0 0 (1),
      tm 6 2 1 1 0 (2),
      tm 5 2 1 1 1 (2),
      tm 5 2 2 1 0 (2),
      tm 4 2 2 1 1 (1),
      tm 4 2 2 2 0 (1),
      tm 3 2 2 2 1 (3),
      tm 2 2 2 2 2 (1),
      tm 3 2 3 2 0 (1),
      tm 2 2 3 2 1 (1),
      tm 1 2 3 3 1 (1),
      tm 0 2 3 3 2 (1),
      tm 3 2 4 1 0 (1),
      tm 1 2 4 2 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 105: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore105 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore105)) den one two three four
      = polyEval chartProduct105 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 106 (degree 4), denominators cleared. -/
def flatCore106 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (2),
    ftm 0 2 1 1 (-1),
    ftm 0 3 1 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 1 (1),
    ftm 1 2 0 0 (1),
    ftm 1 2 0 1 (-1),
    ftm 1 3 0 0 (-1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 106: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct106 : Poly :=
  polyMul ([tm 5 0 0 0 0 (1)])
    (chartCore74)

/-- KERNEL-CHECKED chart soundness for flat core 106: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore106 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore106)) den one two three four
      = polyEval chartProduct106 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 107 (degree 4), denominators cleared. -/
def flatCore107 : FlatPoly :=
  [ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-1),
    ftm 0 2 2 0 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 2 0 (1),
    ftm 1 2 1 0 (-1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (1),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 107: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct107 : Poly :=
  polyMul ([tm 4 3 1 0 0 (-1)])
    (chartCore75)

/-- KERNEL-CHECKED chart soundness for flat core 107: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore107 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore107)) den one two three four
      = polyEval chartProduct107 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 108 (degree 3), denominators cleared. -/
def flatCore108 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 1 (-1),
    ftm 1 2 0 0 (-1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 108: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct108 : Poly :=
  polyMul ([tm 4 1 0 0 0 (-1)])
    (chartCore76)

/-- KERNEL-CHECKED chart soundness for flat core 108: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore108 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore108)) den one two three four
      = polyEval chartProduct108 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 109 (degree 3), denominators cleared. -/
def flatCore109 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (1),
    ftm 1 2 0 0 (-1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 109: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct109 : Poly :=
  polyMul ([tm 5 2 1 0 0 (-1)])
    (chartCore77)

/-- KERNEL-CHECKED chart soundness for flat core 109: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore109 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore109)) den one two three four
      = polyEval chartProduct109 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 110 (degree 2), denominators cleared. -/
def flatCore110 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 1 0 0 (-1)]

/-- The certificate-side product for flat core 110: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct110 : Poly :=
  polyMul ([tm 3 1 0 0 0 (-1)])
    (chartCore78)

/-- KERNEL-CHECKED chart soundness for flat core 110: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore110 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore110)) den one two three four
      = polyEval chartProduct110 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 111 (degree 2), denominators cleared. -/
def flatCore111 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 0 2 0 (-1),
    ftm 0 1 1 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 1 0 (-1),
    ftm 1 1 0 0 (-1)]

/-- The certificate-side product for flat core 111: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct111 : Poly :=
  polyMul ([tm 3 1 1 1 0 (-1)])
    (chartCore79)

/-- KERNEL-CHECKED chart soundness for flat core 111: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore111 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore111)) den one two three four
      = polyEval chartProduct111 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 112 (degree 4), denominators cleared. -/
def flatCore112 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 2 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (2),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 0 (1),
    ftm 1 0 2 1 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 1 (-1),
    ftm 1 1 2 0 (-1),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (2),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 0 (1),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (-1)]

/-- The certificate-side product for flat core 112: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct112 : Poly :=
  polyMul ([tm 2 2 1 0 0 (1)])
    (chartCore80)

/-- KERNEL-CHECKED chart soundness for flat core 112: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore112 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore112)) den one two three four
      = polyEval chartProduct112 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 113 (degree 3), denominators cleared. -/
def flatCore113 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-1),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1)]

/-- The certificate-side product for flat core 113: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct113 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore81)

/-- KERNEL-CHECKED chart soundness for flat core 113: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore113 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore113)) den one two three four
      = polyEval chartProduct113 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 114 (degree 3), denominators cleared. -/
def flatCore114 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 114: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct114 : Poly :=
  polyMul ([tm 1 1 0 0 0 (-1)])
    (chartCore82)

/-- KERNEL-CHECKED chart soundness for flat core 114: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore114 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore114)) den one two three four
      = polyEval chartProduct114 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 115 (degree 4), denominators cleared. -/
def flatCore115 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 2 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (1),
    ftm 0 2 1 1 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (-2),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 1 (1),
    ftm 1 2 0 1 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 115: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct115 : Poly :=
  polyMul ([tm 5 0 0 0 0 (1)])
    (chartCore83)

/-- KERNEL-CHECKED chart soundness for flat core 115: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore115 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore115)) den one two three four
      = polyEval chartProduct115 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 116 (degree 3), denominators cleared. -/
def flatCore116 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 116: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct116 : Poly :=
  polyMul ([tm 1 2 1 0 0 (1)])
    ([tm 8 0 0 0 0 (1),
      tm 6 0 1 1 0 (1),
      tm 7 1 0 0 0 (1),
      tm 6 1 1 0 0 (1),
      tm 5 1 1 1 0 (2),
      tm 4 1 1 1 1 (1),
      tm 3 1 1 2 1 (1),
      tm 4 1 2 1 0 (1),
      tm 3 1 2 2 0 (1),
      tm 2 1 2 2 1 (1),
      tm 1 1 2 3 1 (1),
      tm 0 1 2 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 116: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore116 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore116)) den one two three four
      = polyEval chartProduct116 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 117 (degree 3), denominators cleared. -/
def flatCore117 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-1),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 1 (1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 117: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct117 : Poly :=
  polyMul ([tm 4 1 0 0 0 (1)])
    ([tm 7 0 0 0 0 (1),
      tm 4 0 1 1 1 (1),
      tm 6 1 0 0 0 (1),
      tm 5 1 1 0 0 (2),
      tm 4 1 1 1 0 (1),
      tm 3 1 1 1 1 (1),
      tm 2 1 2 1 1 (1),
      tm 0 1 2 2 2 (1),
      tm 4 2 1 0 0 (1),
      tm 3 2 2 0 0 (1),
      tm 2 2 2 1 0 (1),
      tm 1 2 2 1 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 117: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore117 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore117)) den one two three four
      = polyEval chartProduct117 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 118 (degree 3), denominators cleared. -/
def flatCore118 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 1 (1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 118: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct118 : Poly :=
  polyMul ([tm 5 2 1 0 0 (1)])
    (chartCore84)

/-- KERNEL-CHECKED chart soundness for flat core 118: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore118 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore118)) den one two three four
      = polyEval chartProduct118 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 119 (degree 4), denominators cleared. -/
def flatCore119 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 0 3 1 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (2),
    ftm 0 1 2 1 (-1),
    ftm 0 1 3 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 0 2 2 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 1 (-1),
    ftm 1 1 2 0 (-1),
    ftm 1 2 0 0 (1),
    ftm 1 2 1 0 (-2),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 1 0 0 (-1),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 119: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct119 : Poly :=
  polyMul ([tm 2 2 0 0 0 (1)])
    (chartCore85)

/-- KERNEL-CHECKED chart soundness for flat core 119: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore119 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore119)) den one two three four
      = polyEval chartProduct119 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 120 (degree 4), denominators cleared. -/
def flatCore120 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 2 1 (-1),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 1 (-1),
    ftm 0 3 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 1 1 1 (-1),
    ftm 1 2 0 1 (-1),
    ftm 1 3 0 0 (-1)]

/-- The certificate-side product for flat core 120: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct120 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    ([tm 9 0 1 0 0 (1),
      tm 8 0 2 0 0 (1),
      tm 7 0 2 1 0 (1),
      tm 6 0 2 1 1 (1),
      tm 9 1 0 0 0 (1),
      tm 8 1 1 0 0 (1),
      tm 7 1 1 1 0 (2),
      tm 6 1 1 1 1 (1),
      tm 7 1 2 0 0 (2),
      tm 6 1 2 1 0 (2),
      tm 5 1 2 1 1 (2),
      tm 5 1 2 2 0 (1),
      tm 4 1 2 2 1 (1),
      tm 6 1 3 0 0 (2),
      tm 5 1 3 1 0 (2),
      tm 4 1 3 1 1 (3),
      tm 4 1 3 2 0 (1),
      tm 3 1 3 2 1 (2),
      tm 2 1 3 2 2 (1),
      tm 6 2 2 0 0 (1),
      tm 5 2 3 0 0 (1),
      tm 4 2 3 1 0 (2),
      tm 3 2 3 1 1 (2),
      tm 4 2 4 0 0 (1),
      tm 3 2 4 1 0 (1),
      tm 2 2 4 1 1 (2),
      tm 2 2 4 2 0 (1),
      tm 1 2 4 2 1 (2),
      tm 0 2 4 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 120: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore120 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore120)) den one two three four
      = polyEval chartProduct120 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 121 (degree 4), denominators cleared. -/
def flatCore121 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 0 0 3 1 (-1),
    ftm 0 1 3 0 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 1 (-1),
    ftm 1 1 2 0 (-1),
    ftm 1 2 0 0 (1),
    ftm 1 2 1 0 (-1),
    ftm 2 0 1 0 (-1),
    ftm 2 1 0 1 (-1),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 121: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct121 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    ([tm 10 0 0 0 0 (1),
      tm 8 0 1 1 0 (1),
      tm 7 0 2 1 0 (1),
      tm 9 1 0 0 0 (1),
      tm 8 1 1 0 0 (2),
      tm 7 1 1 1 0 (2),
      tm 6 1 1 1 1 (2),
      tm 6 1 2 1 0 (2),
      tm 5 1 2 2 0 (1),
      tm 4 1 2 2 1 (2),
      tm 5 1 3 1 0 (2),
      tm 3 1 3 2 1 (1),
      tm 8 2 0 0 0 (1),
      tm 7 2 1 0 0 (1),
      tm 6 2 1 1 0 (2),
      tm 5 2 1 1 1 (2),
      tm 6 2 2 0 0 (1),
      tm 5 2 2 1 0 (2),
      tm 4 2 2 1 1 (2),
      tm 4 2 2 2 0 (1),
      tm 3 2 2 2 1 (3),
      tm 2 2 2 2 2 (1),
      tm 4 2 3 1 0 (1),
      tm 3 2 3 2 0 (1),
      tm 2 2 3 2 1 (2),
      tm 1 2 3 3 1 (1),
      tm 0 2 3 3 2 (1),
      tm 3 2 4 1 0 (1),
      tm 1 2 4 2 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 121: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore121 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore121)) den one two three four
      = polyEval chartProduct121 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 122 (degree 4), denominators cleared. -/
def flatCore122 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-2),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (2),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 0 (-1),
    ftm 0 3 1 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 1 (-1),
    ftm 1 2 0 0 (1),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-1),
    ftm 1 3 0 0 (-1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 122: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct122 : Poly :=
  polyMul ([tm 5 0 0 0 0 (1)])
    (chartCore86)

/-- KERNEL-CHECKED chart soundness for flat core 122: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore122 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore122)) den one two three four
      = polyEval chartProduct122 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 123 (degree 4), denominators cleared. -/
def flatCore123 : FlatPoly :=
  [ftm 0 0 3 1 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 1 3 0 (1),
    ftm 0 2 2 0 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (2),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 0 (1),
    ftm 1 0 2 1 (1),
    ftm 1 1 1 0 (1),
    ftm 1 1 2 0 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 1 0 (1),
    ftm 2 1 0 1 (1),
    ftm 2 2 0 0 (1)]

/-- The certificate-side product for flat core 123: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct123 : Poly :=
  polyMul ([tm 4 3 0 0 0 (1)])
    (chartCore87)

/-- KERNEL-CHECKED chart soundness for flat core 123: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore123 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore123)) den one two three four
      = polyEval chartProduct123 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 124 (degree 4), denominators cleared. -/
def flatCore124 : FlatPoly :=
  [ftm 0 0 2 2 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 0 2 (1),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 1 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 0 (1),
    ftm 0 3 1 0 (1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (2),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (1),
    ftm 1 3 0 0 (1),
    ftm 2 1 0 1 (-1)]

/-- The certificate-side product for flat core 124: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct124 : Poly :=
  polyMul ([tm 6 2 0 0 0 (1)])
    (chartCore88)

/-- KERNEL-CHECKED chart soundness for flat core 124: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore124 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore124)) den one two three four
      = polyEval chartProduct124 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 125 (degree 3), denominators cleared. -/
def flatCore125 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 1 (-1)]

/-- The certificate-side product for flat core 125: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct125 : Poly :=
  polyMul ([tm 5 2 0 0 0 (1)])
    (chartCore89)

/-- KERNEL-CHECKED chart soundness for flat core 125: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore125 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore125)) den one two three four
      = polyEval chartProduct125 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 126 (degree 3), denominators cleared. -/
def flatCore126 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 1 (1),
    ftm 1 2 0 0 (1)]

/-- The certificate-side product for flat core 126: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct126 : Poly :=
  polyMul ([tm 5 2 0 0 0 (1)])
    ([tm 5 0 0 0 0 (1),
      tm 3 0 1 1 0 (1),
      tm 2 0 2 1 0 (1),
      tm 0 1 3 1 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 126: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore126 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore126)) den one two three four
      = polyEval chartProduct126 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 127 (degree 4), denominators cleared. -/
def flatCore127 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 0 3 1 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 2 0 (2),
    ftm 0 1 3 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 1 (1),
    ftm 1 1 2 0 (-1),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 127: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct127 : Poly :=
  polyMul ([tm 2 2 0 0 0 (1)])
    (chartCore90)

/-- KERNEL-CHECKED chart soundness for flat core 127: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore127 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore127)) den one two three four
      = polyEval chartProduct127 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 128 (degree 4), denominators cleared. -/
def flatCore128 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 1 (-1),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 1 1 (1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 1 (-1),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (1)]

/-- The certificate-side product for flat core 128: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct128 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    ([tm 9 0 1 0 0 (1),
      tm 8 0 2 0 0 (1),
      tm 7 0 2 1 0 (1),
      tm 6 0 2 1 1 (1),
      tm 9 1 0 0 0 (1),
      tm 7 1 1 1 0 (2),
      tm 6 1 1 1 1 (1),
      tm 7 1 2 0 0 (2),
      tm 5 1 2 1 1 (1),
      tm 5 1 2 2 0 (1),
      tm 4 1 2 2 1 (1),
      tm 6 1 3 0 0 (2),
      tm 5 1 3 1 0 (2),
      tm 4 1 3 1 1 (3),
      tm 3 1 3 2 1 (1),
      tm 2 1 3 2 2 (1),
      tm 5 2 3 0 0 (1),
      tm 3 2 3 1 1 (1),
      tm 4 2 4 0 0 (1),
      tm 3 2 4 1 0 (1),
      tm 2 2 4 1 1 (2),
      tm 1 2 4 2 1 (1),
      tm 0 2 4 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 128: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore128 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore128)) den one two three four
      = polyEval chartProduct128 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 129 (degree 3), denominators cleared. -/
def flatCore129 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 0 (-1)]

/-- The certificate-side product for flat core 129: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct129 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    (chartCore91)

/-- KERNEL-CHECKED chart soundness for flat core 129: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore129 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore129)) den one two three four
      = polyEval chartProduct129 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 130 (degree 4), denominators cleared. -/
def flatCore130 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-2),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (1),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 1 0 1 (-2),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 1 (-1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (-1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 130: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct130 : Poly :=
  polyMul ([tm 5 0 0 0 0 (1)])
    (chartCore92)

/-- KERNEL-CHECKED chart soundness for flat core 130: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore130 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore130)) den one two three four
      = polyEval chartProduct130 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 131 (degree 3), denominators cleared. -/
def flatCore131 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 2 0 (1),
    ftm 1 0 0 0 (-1),
    ftm 1 0 0 1 (2),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (-2),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (-1),
    ftm 2 0 0 0 (1)]

/-- The certificate-side product for flat core 131: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct131 : Poly :=
  polyMul ([tm 1 2 0 0 0 (1)])
    (chartCore93)

/-- KERNEL-CHECKED chart soundness for flat core 131: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore131 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore131)) den one two three four
      = polyEval chartProduct131 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 132 (degree 4), denominators cleared. -/
def flatCore132 : FlatPoly :=
  [ftm 0 0 2 2 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 0 2 (1),
    ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 1 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (2),
    ftm 1 1 0 2 (-1),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (1),
    ftm 2 1 0 1 (-1)]

/-- The certificate-side product for flat core 132: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct132 : Poly :=
  polyMul ([tm 6 2 0 0 0 (1)])
    (chartCore94)

/-- KERNEL-CHECKED chart soundness for flat core 132: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore132 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore132)) den one two three four
      = polyEval chartProduct132 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 133 (degree 3), denominators cleared. -/
def flatCore133 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 2 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (1),
    ftm 2 0 0 1 (-1)]

/-- The certificate-side product for flat core 133: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct133 : Poly :=
  polyMul ([tm 5 2 0 0 0 (1)])
    (chartCore95)

/-- KERNEL-CHECKED chart soundness for flat core 133: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore133 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore133)) den one two three four
      = polyEval chartProduct133 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 134 (degree 2), denominators cleared. -/
def flatCore134 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 2 0 0 (-1),
    ftm 1 0 0 1 (1)]

/-- The certificate-side product for flat core 134: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct134 : Poly :=
  polyMul ([tm 4 1 0 0 0 (1)])
    (chartCore96)

/-- KERNEL-CHECKED chart soundness for flat core 134: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore134 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore134)) den one two three four
      = polyEval chartProduct134 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 135 (degree 3), denominators cleared. -/
def flatCore135 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 2 0 (1),
    ftm 0 2 0 0 (1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (-1)]

/-- The certificate-side product for flat core 135: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct135 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    ([tm 10 0 0 0 0 (1),
      tm 9 0 1 0 0 (1),
      tm 8 0 1 1 0 (1),
      tm 7 0 1 1 1 (1),
      tm 9 1 0 0 0 (1),
      tm 8 1 1 0 0 (1),
      tm 7 1 1 1 0 (2),
      tm 6 1 1 1 1 (2),
      tm 7 1 2 0 0 (2),
      tm 6 1 2 1 0 (1),
      tm 5 1 2 1 1 (2),
      tm 5 1 2 2 0 (1),
      tm 4 1 2 2 1 (2),
      tm 3 1 2 2 2 (1),
      tm 7 2 1 0 0 (1),
      tm 6 2 1 1 0 (1),
      tm 5 2 1 1 1 (1),
      tm 5 2 2 1 0 (2),
      tm 4 2 2 1 1 (1),
      tm 4 2 2 2 0 (2),
      tm 3 2 2 2 1 (3),
      tm 2 2 2 2 2 (1),
      tm 5 2 3 0 0 (1),
      tm 3 2 3 1 1 (1),
      tm 3 2 3 2 0 (1),
      tm 2 2 3 2 1 (1),
      tm 2 2 3 3 0 (1),
      tm 1 2 3 3 1 (2),
      tm 0 2 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 135: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore135 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore135)) den one two three four
      = polyEval chartProduct135 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 136 (degree 3), denominators cleared. -/
def flatCore136 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (-1)]

/-- The certificate-side product for flat core 136: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct136 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    ([tm 9 0 0 0 0 (1),
      tm 8 0 1 0 0 (1),
      tm 7 0 1 1 0 (1),
      tm 6 0 1 1 1 (1),
      tm 8 1 0 0 0 (1),
      tm 7 1 1 0 0 (2),
      tm 6 1 1 1 0 (2),
      tm 5 1 1 1 1 (2),
      tm 6 1 2 0 0 (2),
      tm 5 1 2 1 0 (2),
      tm 4 1 2 1 1 (3),
      tm 4 1 2 2 0 (1),
      tm 3 1 2 2 1 (2),
      tm 2 1 2 2 2 (1),
      tm 6 2 1 0 0 (1),
      tm 4 2 1 1 1 (1),
      tm 5 2 2 0 0 (1),
      tm 4 2 2 1 0 (2),
      tm 3 2 2 1 1 (2),
      tm 2 2 2 2 1 (1),
      tm 1 2 2 2 2 (1),
      tm 4 2 3 0 0 (1),
      tm 3 2 3 1 0 (1),
      tm 2 2 3 1 1 (2),
      tm 2 2 3 2 0 (1),
      tm 1 2 3 2 1 (2),
      tm 0 2 3 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 136: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore136 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore136)) den one two three four
      = polyEval chartProduct136 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 137 (degree 4), denominators cleared. -/
def flatCore137 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (-2),
    ftm 1 1 2 0 (1),
    ftm 1 2 0 0 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (1),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 137: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct137 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    ([tm 7 0 2 1 0 (1),
      tm 9 1 0 0 0 (1),
      tm 8 1 1 0 0 (1),
      tm 7 1 1 1 0 (2),
      tm 6 1 1 1 1 (1),
      tm 6 1 2 1 0 (1),
      tm 5 1 2 1 1 (1),
      tm 5 1 2 2 0 (1),
      tm 4 1 2 2 1 (1),
      tm 5 1 3 1 0 (2),
      tm 3 1 3 2 1 (1),
      tm 8 2 0 0 0 (1),
      tm 7 2 1 0 0 (1),
      tm 6 2 1 1 0 (2),
      tm 5 2 1 1 1 (2),
      tm 6 2 2 0 0 (1),
      tm 5 2 2 1 0 (2),
      tm 4 2 2 1 1 (2),
      tm 4 2 2 2 0 (1),
      tm 3 2 2 2 1 (3),
      tm 2 2 2 2 2 (1),
      tm 4 2 3 1 0 (1),
      tm 3 2 3 1 1 (1),
      tm 3 2 3 2 0 (1),
      tm 2 2 3 2 1 (2),
      tm 1 2 3 2 2 (1),
      tm 1 2 3 3 1 (1),
      tm 0 2 3 3 2 (1),
      tm 3 2 4 1 0 (1),
      tm 1 2 4 2 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 137: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore137 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore137)) den one two three four
      = polyEval chartProduct137 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 138 (degree 4), denominators cleared. -/
def flatCore138 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 1 2 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 1 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 1 (1),
    ftm 1 2 0 0 (1),
    ftm 1 2 0 1 (-1),
    ftm 1 3 0 0 (-1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 138: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct138 : Poly :=
  polyMul ([tm 5 0 0 0 0 (1)])
    ([tm 11 0 0 0 0 (1),
      tm 10 1 0 0 0 (1),
      tm 9 1 1 0 0 (2),
      tm 8 1 1 1 0 (1),
      tm 7 1 1 1 1 (2),
      tm 8 2 1 0 0 (2),
      tm 7 2 1 1 0 (1),
      tm 6 2 1 1 1 (1),
      tm 7 2 2 0 0 (1),
      tm 6 2 2 1 0 (2),
      tm 5 2 2 1 1 (3),
      tm 5 2 2 2 0 (1),
      tm 4 2 2 2 1 (2),
      tm 3 2 2 2 2 (1),
      tm 6 3 2 0 0 (1),
      tm 5 3 2 1 0 (2),
      tm 4 3 2 1 1 (1),
      tm 3 3 2 2 1 (1),
      tm 4 3 3 1 0 (1),
      tm 3 3 3 1 1 (1),
      tm 3 3 3 2 0 (2),
      tm 2 3 3 2 1 (3),
      tm 1 3 3 2 2 (1),
      tm 1 3 3 3 1 (1),
      tm 0 3 3 3 2 (1),
      tm 3 4 3 1 0 (1),
      tm 1 4 4 2 0 (1),
      tm 0 4 4 2 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 138: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore138 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore138)) den one two three four
      = polyEval chartProduct138 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 139 (degree 3), denominators cleared. -/
def flatCore139 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (-1)]

/-- The certificate-side product for flat core 139: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct139 : Poly :=
  polyMul ([tm 3 2 1 0 0 (-1)])
    (chartCore97)

/-- KERNEL-CHECKED chart soundness for flat core 139: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore139 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore139)) den one two three four
      = polyEval chartProduct139 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 140 (degree 3), denominators cleared. -/
def flatCore140 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 1 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 1 (-1),
    ftm 1 2 0 0 (-1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 140: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct140 : Poly :=
  polyMul ([tm 4 1 1 1 0 (-1)])
    (chartCore98)

/-- KERNEL-CHECKED chart soundness for flat core 140: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore140 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore140)) den one two three four
      = polyEval chartProduct140 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 141 (degree 2), denominators cleared. -/
def flatCore141 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-1),
    ftm 0 2 0 0 (1),
    ftm 1 0 0 1 (-1)]

/-- The certificate-side product for flat core 141: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct141 : Poly :=
  polyMul ([tm 4 1 1 0 0 (1)])
    ([tm 2 0 0 0 0 (1),
      tm 0 0 0 1 1 (1),
      tm 0 1 1 0 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 141: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore141 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore141)) den one two three four
      = polyEval chartProduct141 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 142 (degree 2), denominators cleared. -/
def flatCore142 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 0 2 0 (-1),
    ftm 0 1 1 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 1 0 0 (1)]

/-- The certificate-side product for flat core 142: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct142 : Poly :=
  polyMul ([tm 3 1 1 1 0 (1)])
    ([tm 2 0 0 0 0 (1),
      tm 0 1 0 0 1 (1),
      tm 0 1 1 0 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 142: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore142 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore142)) den one two three four
      = polyEval chartProduct142 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 143 (degree 4), denominators cleared. -/
def flatCore143 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 1 2 1 (-1),
    ftm 0 2 1 0 (1),
    ftm 0 2 2 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (2),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 0 (1),
    ftm 1 0 2 1 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 1 (-2),
    ftm 1 1 2 0 (-1),
    ftm 1 2 1 0 (-1),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (2),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 0 (1),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (-1)]

/-- The certificate-side product for flat core 143: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct143 : Poly :=
  polyMul ([tm 2 2 1 0 0 (1)])
    (chartCore99)

/-- KERNEL-CHECKED chart soundness for flat core 143: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore143 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore143)) den one two three four
      = polyEval chartProduct143 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 144 (degree 3), denominators cleared. -/
def flatCore144 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-3),
    ftm 0 0 1 2 (2),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-3),
    ftm 0 1 1 1 (3),
    ftm 0 1 2 0 (1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1)]

/-- The certificate-side product for flat core 144: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct144 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    ([tm 9 0 0 0 0 (1),
      tm 8 0 1 0 0 (1),
      tm 7 0 1 1 0 (1),
      tm 6 0 1 1 1 (1),
      tm 7 1 1 0 0 (2),
      tm 5 1 1 1 1 (1),
      tm 6 1 2 0 0 (2),
      tm 5 1 2 1 0 (2),
      tm 4 1 2 1 1 (3),
      tm 3 1 2 2 1 (1),
      tm 2 1 2 2 2 (1),
      tm 4 2 1 1 1 (1),
      tm 5 2 2 0 0 (1),
      tm 3 2 2 1 1 (1),
      tm 2 2 2 2 1 (1),
      tm 1 2 2 2 2 (1),
      tm 4 2 3 0 0 (1),
      tm 3 2 3 1 0 (1),
      tm 2 2 3 1 1 (2),
      tm 1 2 3 2 1 (1),
      tm 0 2 3 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 144: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore144 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore144)) den one two three four
      = polyEval chartProduct144 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 145 (degree 3), denominators cleared. -/
def flatCore145 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-2),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (2),
    ftm 0 2 0 0 (-2),
    ftm 0 2 1 0 (2),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-2),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (2),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 145: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct145 : Poly :=
  polyMul ([tm 1 1 0 0 0 (-1)])
    (chartCore100)

/-- KERNEL-CHECKED chart soundness for flat core 145: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore145 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore145)) den one two three four
      = polyEval chartProduct145 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 146 (degree 4), denominators cleared. -/
def flatCore146 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (2),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 1 1 (3),
    ftm 0 3 1 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (-2),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 1 (1),
    ftm 1 2 0 1 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 146: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct146 : Poly :=
  polyMul ([tm 5 0 0 0 0 (1)])
    (chartCore101)

/-- KERNEL-CHECKED chart soundness for flat core 146: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore146 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore146)) den one two three four
      = polyEval chartProduct146 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 147 (degree 3), denominators cleared. -/
def flatCore147 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-2),
    ftm 1 1 0 1 (3),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (2),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 147: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct147 : Poly :=
  polyMul ([tm 1 2 1 0 0 (1)])
    ([tm 8 0 0 0 0 (1),
      tm 6 0 1 1 0 (1),
      tm 6 1 1 0 0 (1),
      tm 3 1 1 2 1 (1),
      tm 4 1 2 1 0 (1),
      tm 1 1 2 3 1 (1),
      tm 0 1 2 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 147: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore147 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore147)) den one two three four
      = polyEval chartProduct147 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 148 (degree 3), denominators cleared. -/
def flatCore148 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (2),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 1 (3),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 1 (1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 148: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct148 : Poly :=
  polyMul ([tm 4 1 0 0 0 (1)])
    ([tm 7 0 0 0 0 (1),
      tm 4 0 1 1 1 (1),
      tm 5 1 1 0 0 (2),
      tm 2 1 2 1 1 (1),
      tm 0 1 2 2 2 (1),
      tm 3 2 2 0 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 148: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore148 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore148)) den one two three four
      = polyEval chartProduct148 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 149 (degree 3), denominators cleared. -/
def flatCore149 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 1 (1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 149: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct149 : Poly :=
  polyMul ([tm 5 2 1 0 0 (1)])
    (chartCore102)

/-- KERNEL-CHECKED chart soundness for flat core 149: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore149 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore149)) den one two three four
      = polyEval chartProduct149 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 150 (degree 1), denominators cleared. -/
def flatCore150 : FlatPoly :=
  [ftm 0 0 0 0 (1),
    ftm 0 0 0 1 (-2),
    ftm 0 0 1 0 (-1),
    ftm 0 1 0 0 (-2),
    ftm 1 0 0 0 (-1)]

/-- The certificate-side product for flat core 150: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct150 : Poly :=
  polyMul ([tm 0 0 0 0 0 (-1)])
    (chartCore103)

/-- KERNEL-CHECKED chart soundness for flat core 150: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore150 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 1 flatCore150)) den one two three four
      = polyEval chartProduct150 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 151 (degree 4), denominators cleared. -/
def flatCore151 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 2 (-1),
    ftm 0 0 3 0 (1),
    ftm 0 1 1 0 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-2),
    ftm 1 0 1 1 (2),
    ftm 1 0 1 2 (-2),
    ftm 1 0 2 0 (2),
    ftm 1 2 0 0 (-1),
    ftm 1 2 1 0 (2),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (2),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 0 (1),
    ftm 2 1 0 0 (1),
    ftm 2 2 0 0 (1)]

/-- The certificate-side product for flat core 151: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct151 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore104)

/-- KERNEL-CHECKED chart soundness for flat core 151: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore151 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore151)) den one two three four
      = polyEval chartProduct151 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 152 (degree 5), denominators cleared. -/
def flatCore152 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-2),
    ftm 0 1 2 2 (1),
    ftm 0 1 3 0 (-1),
    ftm 0 1 3 1 (1),
    ftm 0 2 1 0 (1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 0 (-2),
    ftm 0 2 2 1 (1),
    ftm 0 2 3 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 1 (1),
    ftm 1 0 2 2 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 2 (1),
    ftm 1 1 2 0 (-1),
    ftm 1 2 0 0 (1),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-1),
    ftm 1 2 2 0 (1),
    ftm 1 3 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 0 1 2 (-1),
    ftm 2 1 1 1 (-1),
    ftm 2 2 0 1 (-1),
    ftm 2 3 0 0 (-1)]

/-- The certificate-side product for flat core 152: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct152 : Poly :=
  polyMul ([tm 5 3 1 0 0 (1)])
    (chartCore105)

/-- KERNEL-CHECKED chart soundness for flat core 152: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore152 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore152)) den one two three four
      = polyEval chartProduct152 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 153 (degree 5), denominators cleared. -/
def flatCore153 : FlatPoly :=
  [ftm 0 0 3 0 (1),
    ftm 0 0 3 1 (-1),
    ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-1),
    ftm 0 1 3 0 (-2),
    ftm 0 1 3 1 (1),
    ftm 0 2 2 0 (-1),
    ftm 0 2 3 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 2 0 (2),
    ftm 1 0 3 0 (-1),
    ftm 1 1 2 0 (-2),
    ftm 1 1 2 1 (1),
    ftm 1 2 2 0 (1),
    ftm 2 0 1 0 (1),
    ftm 2 0 1 1 (1),
    ftm 2 0 2 0 (-2),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 1 (-1),
    ftm 2 2 0 0 (1),
    ftm 2 2 1 0 (-1),
    ftm 3 0 1 0 (-1),
    ftm 3 1 0 1 (-1),
    ftm 3 2 0 0 (-1)]

/-- The certificate-side product for flat core 153: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct153 : Poly :=
  polyMul ([tm 5 2 0 0 0 (-1)])
    (chartCore106)

/-- KERNEL-CHECKED chart soundness for flat core 153: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore153 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore153)) den one two three four
      = polyEval chartProduct153 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 154 (degree 5), denominators cleared. -/
def flatCore154 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 1 (-1),
    ftm 0 1 2 2 (1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 1 (1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 2 (-2),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 2 (1),
    ftm 1 1 2 0 (1),
    ftm 1 1 2 1 (-1),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (2),
    ftm 1 2 2 0 (-1),
    ftm 1 3 1 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-2),
    ftm 2 0 1 1 (-1),
    ftm 2 0 1 2 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (1),
    ftm 2 2 0 0 (1),
    ftm 2 2 0 1 (-1),
    ftm 2 2 1 0 (-1),
    ftm 2 3 0 0 (-1),
    ftm 3 0 0 1 (-1),
    ftm 3 0 0 2 (1),
    ftm 3 1 0 1 (1)]

/-- The certificate-side product for flat core 154: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct154 : Poly :=
  polyMul ([tm 6 1 0 0 0 (1)])
    (chartCore107)

/-- KERNEL-CHECKED chart soundness for flat core 154: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore154 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore154)) den one two three four
      = polyEval chartProduct154 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 155 (degree 3), denominators cleared. -/
def flatCore155 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 2 0 0 (-1)]

/-- The certificate-side product for flat core 155: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct155 : Poly :=
  polyMul ([tm 3 1 0 0 0 (1)])
    (chartCore108)

/-- KERNEL-CHECKED chart soundness for flat core 155: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore155 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore155)) den one two three four
      = polyEval chartProduct155 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 156 (degree 5), denominators cleared. -/
def flatCore156 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 1 (-2),
    ftm 0 1 2 2 (1),
    ftm 0 1 3 1 (1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 1 (1),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 2 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 1 (-2),
    ftm 1 1 1 2 (1),
    ftm 1 1 2 1 (1),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (1),
    ftm 1 2 2 0 (-1),
    ftm 1 3 1 0 (-1),
    ftm 2 0 1 2 (-1),
    ftm 2 1 0 1 (-2),
    ftm 2 1 1 1 (1),
    ftm 2 2 0 1 (-1),
    ftm 2 2 1 0 (-1),
    ftm 2 3 0 0 (-1),
    ftm 3 1 0 1 (1)]

/-- The certificate-side product for flat core 156: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct156 : Poly :=
  polyMul ([tm 7 2 1 1 0 (1)])
    (chartCore109)

/-- KERNEL-CHECKED chart soundness for flat core 156: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore156 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore156)) den one two three four
      = polyEval chartProduct156 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 157 (degree 3), denominators cleared. -/
def flatCore157 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 1 1 0 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 2 0 0 (-1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 157: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct157 : Poly :=
  polyMul ([tm 5 1 0 0 0 (1)])
    (chartCore110)

/-- KERNEL-CHECKED chart soundness for flat core 157: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore157 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore157)) den one two three four
      = polyEval chartProduct157 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 158 (degree 4), denominators cleared. -/
def flatCore158 : FlatPoly :=
  [ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-1),
    ftm 0 1 3 0 (-1),
    ftm 0 2 2 0 (-1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 2 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 1 (1),
    ftm 2 2 0 0 (1)]

/-- The certificate-side product for flat core 158: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct158 : Poly :=
  polyMul ([tm 6 2 1 1 0 (-1)])
    (chartCore111)

/-- KERNEL-CHECKED chart soundness for flat core 158: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore158 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore158)) den one two three four
      = polyEval chartProduct158 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 159 (degree 5), denominators cleared. -/
def flatCore159 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 1 (-1),
    ftm 0 1 2 2 (1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 0 3 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (2),
    ftm 1 0 1 3 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 0 2 2 (-1),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 2 0 (1),
    ftm 1 1 2 1 (-1),
    ftm 1 2 1 1 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (2),
    ftm 2 0 0 3 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 0 1 2 (-1),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (1),
    ftm 2 1 0 2 (-1),
    ftm 2 1 1 0 (1),
    ftm 2 2 1 0 (1),
    ftm 3 1 0 1 (1),
    ftm 3 2 0 0 (1)]

/-- The certificate-side product for flat core 159: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct159 : Poly :=
  polyMul ([tm 4 2 1 0 0 (-1)])
    (chartCore112)

/-- KERNEL-CHECKED chart soundness for flat core 159: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore159 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore159)) den one two three four
      = polyEval chartProduct159 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 160 (degree 4), denominators cleared. -/
def flatCore160 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 0 3 (-1),
    ftm 0 0 2 1 (-1),
    ftm 0 0 2 2 (1),
    ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-2),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (2),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 2 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-1),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (-2),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 160: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct160 : Poly :=
  polyMul ([tm 4 1 0 0 0 (1)])
    (chartCore113)

/-- KERNEL-CHECKED chart soundness for flat core 160: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore160 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore160)) den one two three four
      = polyEval chartProduct160 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 161 (degree 5), denominators cleared. -/
def flatCore161 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-2),
    ftm 0 2 1 0 (1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 0 (-2),
    ftm 0 2 2 1 (1),
    ftm 0 3 1 0 (-1),
    ftm 0 3 2 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 1 (-1),
    ftm 1 0 2 2 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 2 (-1),
    ftm 1 1 2 0 (-1),
    ftm 1 1 2 1 (1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (-1),
    ftm 1 3 1 0 (1),
    ftm 2 0 1 1 (-1),
    ftm 2 0 1 2 (1),
    ftm 2 1 0 1 (2),
    ftm 2 1 0 2 (-1),
    ftm 2 1 1 0 (-1),
    ftm 2 2 0 0 (1),
    ftm 2 2 0 1 (-1),
    ftm 2 2 1 0 (-1),
    ftm 3 1 0 1 (-1),
    ftm 3 2 0 0 (-1)]

/-- The certificate-side product for flat core 161: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct161 : Poly :=
  polyMul ([tm 6 3 0 0 0 (1)])
    (chartCore114)

/-- KERNEL-CHECKED chart soundness for flat core 161: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore161 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore161)) den one two three four
      = polyEval chartProduct161 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 162 (degree 5), denominators cleared. -/
def flatCore162 : FlatPoly :=
  [ftm 0 0 0 3 (1),
    ftm 0 0 1 3 (-1),
    ftm 0 1 0 2 (2),
    ftm 0 1 0 3 (-1),
    ftm 0 1 1 1 (-1),
    ftm 0 2 0 1 (1),
    ftm 0 2 0 2 (-2),
    ftm 0 2 1 1 (1),
    ftm 0 3 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 0 3 (-2),
    ftm 1 0 1 2 (-1),
    ftm 1 0 1 3 (1),
    ftm 1 1 0 2 (-2),
    ftm 1 1 1 2 (1),
    ftm 1 2 1 0 (1),
    ftm 1 2 1 1 (-1),
    ftm 1 3 1 0 (-1),
    ftm 2 0 0 2 (-1),
    ftm 2 0 0 3 (1),
    ftm 2 1 0 2 (1),
    ftm 2 2 0 0 (1),
    ftm 2 2 0 1 (-1),
    ftm 2 3 0 0 (-1)]

/-- The certificate-side product for flat core 162: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct162 : Poly :=
  polyMul ([tm 6 0 0 0 0 (1)])
    (chartCore115)

/-- KERNEL-CHECKED chart soundness for flat core 162: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore162 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore162)) den one two three four
      = polyEval chartProduct162 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 163 (degree 5), denominators cleared. -/
def flatCore163 : FlatPoly :=
  [ftm 0 1 2 1 (1),
    ftm 0 1 2 2 (-1),
    ftm 0 2 2 1 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-2),
    ftm 1 0 1 3 (1),
    ftm 1 0 2 1 (-1),
    ftm 1 0 2 2 (1),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 1 (-2),
    ftm 1 1 1 2 (1),
    ftm 1 1 2 0 (-1),
    ftm 1 1 2 1 (1),
    ftm 1 2 1 0 (-2),
    ftm 1 2 1 1 (1),
    ftm 1 3 1 0 (1),
    ftm 2 0 1 1 (-1),
    ftm 2 0 1 2 (1),
    ftm 2 1 0 1 (1),
    ftm 2 1 0 2 (-1),
    ftm 2 1 1 0 (-1),
    ftm 2 2 0 1 (-1),
    ftm 2 2 1 0 (-1),
    ftm 3 1 0 1 (-1),
    ftm 3 2 0 0 (-1)]

/-- The certificate-side product for flat core 163: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct163 : Poly :=
  polyMul ([tm 6 4 1 0 0 (1)])
    (chartCore116)

/-- KERNEL-CHECKED chart soundness for flat core 163: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore163 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore163)) den one two three four
      = polyEval chartProduct163 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 164 (degree 3), denominators cleared. -/
def flatCore164 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 1 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 1 0 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 164: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct164 : Poly :=
  polyMul ([tm 4 1 0 0 0 (1)])
    (chartCore117)

/-- KERNEL-CHECKED chart soundness for flat core 164: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore164 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore164)) den one two three four
      = polyEval chartProduct164 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 165 (degree 4), denominators cleared. -/
def flatCore165 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 2 1 1 (-1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 0 3 (1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 2 (1),
    ftm 1 2 1 0 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 165: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct165 : Poly :=
  polyMul ([tm 6 2 1 0 0 (-1)])
    (chartCore118)

/-- KERNEL-CHECKED chart soundness for flat core 165: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore165 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore165)) den one two three four
      = polyEval chartProduct165 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 166 (degree 3), denominators cleared. -/
def flatCore166 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 1 0 1 (-1),
    ftm 2 0 0 1 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 166: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct166 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    (chartCore119)

/-- KERNEL-CHECKED chart soundness for flat core 166: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore166 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore166)) den one two three four
      = polyEval chartProduct166 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 167 (degree 5), denominators cleared. -/
def flatCore167 : FlatPoly :=
  [ftm 0 0 2 2 (1),
    ftm 0 0 3 2 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 1 3 1 (-1),
    ftm 1 0 2 0 (1),
    ftm 1 0 2 2 (-1),
    ftm 1 0 3 0 (-1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 2 0 (1),
    ftm 1 1 2 1 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 0 (2),
    ftm 2 0 1 1 (-2),
    ftm 2 0 1 2 (1),
    ftm 2 0 2 0 (-2),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 1 (1),
    ftm 3 0 0 0 (1),
    ftm 3 0 0 1 (-2),
    ftm 3 0 0 2 (1),
    ftm 3 0 1 0 (-1),
    ftm 3 1 0 0 (-1),
    ftm 3 1 0 1 (1)]

/-- The certificate-side product for flat core 167: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct167 : Poly :=
  polyMul ([tm 3 2 0 0 0 (1)])
    (chartCore120)

/-- KERNEL-CHECKED chart soundness for flat core 167: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore167 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore167)) den one two three four
      = polyEval chartProduct167 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 168 (degree 5), denominators cleared. -/
def flatCore168 : FlatPoly :=
  [ftm 0 0 2 2 (1),
    ftm 0 0 2 3 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-1),
    ftm 0 1 2 2 (-1),
    ftm 0 1 3 0 (-1),
    ftm 0 1 3 1 (1),
    ftm 0 2 1 0 (1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 0 (-2),
    ftm 0 2 3 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (2),
    ftm 1 0 1 3 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 0 2 2 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 2 0 (-1),
    ftm 1 2 0 0 (1),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-2),
    ftm 1 2 1 1 (1),
    ftm 1 2 2 0 (1),
    ftm 2 0 1 1 (1),
    ftm 2 0 1 2 (-1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 0 2 (1),
    ftm 2 1 1 1 (-1),
    ftm 2 2 0 0 (-1),
    ftm 2 2 0 1 (1)]

/-- The certificate-side product for flat core 168: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct168 : Poly :=
  polyMul ([tm 5 3 0 0 0 (1)])
    (chartCore121)

/-- KERNEL-CHECKED chart soundness for flat core 168: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore168 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore168)) den one two three four
      = polyEval chartProduct168 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 169 (degree 4), denominators cleared. -/
def flatCore169 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 2 0 (-2),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (2),
    ftm 1 0 1 2 (-2),
    ftm 1 0 2 0 (-1),
    ftm 1 1 1 0 (-2),
    ftm 1 2 0 0 (-1),
    ftm 1 2 1 0 (2),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 0 (-2),
    ftm 2 2 0 0 (1),
    ftm 3 0 0 0 (-1)]

/-- The certificate-side product for flat core 169: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct169 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore122)

/-- KERNEL-CHECKED chart soundness for flat core 169: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore169 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore169)) den one two three four
      = polyEval chartProduct169 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 170 (degree 5), denominators cleared. -/
def flatCore170 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 2 3 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 2 (-1),
    ftm 0 2 1 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 0 1 3 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 2 0 (1),
    ftm 1 1 2 1 (-1),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (1),
    ftm 1 2 1 1 (1),
    ftm 1 2 2 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-2),
    ftm 2 0 1 1 (-1),
    ftm 2 0 1 2 (1),
    ftm 2 1 0 1 (-2),
    ftm 2 1 0 2 (1),
    ftm 2 1 1 0 (1),
    ftm 2 2 0 1 (1),
    ftm 2 2 1 0 (-1),
    ftm 3 0 0 1 (-1),
    ftm 3 0 0 2 (1),
    ftm 3 1 0 1 (1)]

/-- The certificate-side product for flat core 170: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct170 : Poly :=
  polyMul ([tm 6 1 0 0 0 (1)])
    (chartCore123)

/-- KERNEL-CHECKED chart soundness for flat core 170: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore170 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore170)) den one two three four
      = polyEval chartProduct170 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 171 (degree 3), denominators cleared. -/
def flatCore171 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 1 1 1 (1),
    ftm 1 0 0 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 1 0 (1),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 2 0 0 (-1),
    ftm 2 0 0 0 (1)]

/-- The certificate-side product for flat core 171: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct171 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    (chartCore124)

/-- KERNEL-CHECKED chart soundness for flat core 171: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore171 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore171)) den one two three four
      = polyEval chartProduct171 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 172 (degree 5), denominators cleared. -/
def flatCore172 : FlatPoly :=
  [ftm 0 0 2 3 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 1 (2),
    ftm 0 1 2 2 (1),
    ftm 0 1 3 1 (-1),
    ftm 0 2 1 1 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 0 1 3 (1),
    ftm 1 0 2 2 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 1 (2),
    ftm 1 1 2 1 (-1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (-1),
    ftm 1 2 1 1 (-1),
    ftm 1 2 2 0 (1),
    ftm 2 0 1 2 (1),
    ftm 2 1 0 1 (2),
    ftm 2 1 0 2 (-1),
    ftm 2 1 1 1 (-1),
    ftm 2 2 0 1 (-1),
    ftm 2 2 1 0 (1),
    ftm 3 1 0 1 (-1)]

/-- The certificate-side product for flat core 172: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct172 : Poly :=
  polyMul ([tm 7 2 0 0 0 (1)])
    (chartCore125)

/-- KERNEL-CHECKED chart soundness for flat core 172: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore172 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore172)) den one two three four
      = polyEval chartProduct172 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 173 (degree 4), denominators cleared. -/
def flatCore173 : FlatPoly :=
  [ftm 0 0 2 2 (1),
    ftm 0 1 2 1 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 2 0 (1),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (1),
    ftm 3 0 0 1 (-1)]

/-- The certificate-side product for flat core 173: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct173 : Poly :=
  polyMul ([tm 6 2 0 0 0 (1)])
    (chartCore126)

/-- KERNEL-CHECKED chart soundness for flat core 173: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore173 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore173)) den one two three four
      = polyEval chartProduct173 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 174 (degree 5), denominators cleared. -/
def flatCore174 : FlatPoly :=
  [ftm 0 0 2 2 (1),
    ftm 0 0 3 2 (-1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 1 (2),
    ftm 0 1 2 2 (-1),
    ftm 0 1 3 1 (-1),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 0 3 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 0 1 3 (1),
    ftm 1 0 2 1 (-1),
    ftm 1 0 2 2 (-1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 1 2 0 (-1),
    ftm 1 2 1 0 (-1),
    ftm 1 2 1 1 (-1),
    ftm 1 2 2 0 (1),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-2),
    ftm 2 0 0 3 (1),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (-2),
    ftm 2 1 0 2 (1),
    ftm 2 1 1 0 (-1),
    ftm 2 1 1 1 (1),
    ftm 2 2 0 0 (-1),
    ftm 2 2 1 0 (1)]

/-- The certificate-side product for flat core 174: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct174 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    (chartCore127)

/-- KERNEL-CHECKED chart soundness for flat core 174: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore174 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore174)) den one two three four
      = polyEval chartProduct174 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 175 (degree 5), denominators cleared. -/
def flatCore175 : FlatPoly :=
  [ftm 0 0 2 2 (1),
    ftm 0 0 2 3 (-1),
    ftm 0 1 0 2 (1),
    ftm 0 1 0 3 (-1),
    ftm 0 1 2 2 (-1),
    ftm 0 2 0 1 (2),
    ftm 0 2 0 2 (-2),
    ftm 0 2 1 0 (1),
    ftm 0 2 1 1 (-2),
    ftm 0 2 2 0 (-1),
    ftm 0 2 2 1 (1),
    ftm 0 3 0 0 (1),
    ftm 0 3 0 1 (-1),
    ftm 0 3 1 0 (-2),
    ftm 0 3 2 0 (1),
    ftm 1 0 1 2 (1),
    ftm 1 0 1 3 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 2 (-1),
    ftm 1 2 1 0 (-1),
    ftm 1 2 1 1 (1),
    ftm 1 3 0 0 (-1),
    ftm 1 3 1 0 (1)]

/-- The certificate-side product for flat core 175: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct175 : Poly :=
  polyMul ([tm 6 2 0 0 0 (1)])
    (chartCore128)

/-- KERNEL-CHECKED chart soundness for flat core 175: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore175 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore175)) den one two three four
      = polyEval chartProduct175 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 176 (degree 5), denominators cleared. -/
def flatCore176 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 0 3 2 (-1),
    ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-1),
    ftm 0 1 3 1 (-1),
    ftm 0 2 1 0 (1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 0 (-2),
    ftm 0 2 2 1 (1),
    ftm 0 3 1 0 (-1),
    ftm 0 3 2 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 0 2 1 (-1),
    ftm 1 0 2 2 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 2 (-1),
    ftm 1 1 2 0 (-1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (-2),
    ftm 1 2 2 0 (1),
    ftm 1 3 1 0 (1),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 1 (1),
    ftm 2 1 0 2 (-1),
    ftm 2 1 1 0 (-1),
    ftm 2 1 1 1 (1),
    ftm 2 2 0 1 (-1),
    ftm 2 2 1 0 (1)]

/-- The certificate-side product for flat core 176: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct176 : Poly :=
  polyMul ([tm 6 2 0 0 0 (1)])
    (chartCore129)

/-- KERNEL-CHECKED chart soundness for flat core 176: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore176 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore176)) den one two three four
      = polyEval chartProduct176 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 177 (degree 4), denominators cleared. -/
def flatCore177 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-2),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-2),
    ftm 0 2 1 0 (1),
    ftm 0 2 2 0 (-1),
    ftm 0 3 0 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 1 0 1 (-2),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (2),
    ftm 2 2 0 0 (1)]

/-- The certificate-side product for flat core 177: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct177 : Poly :=
  polyMul ([tm 4 0 0 0 0 (1)])
    (chartCore130)

/-- KERNEL-CHECKED chart soundness for flat core 177: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore177 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore177)) den one two three four
      = polyEval chartProduct177 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 178 (degree 5), denominators cleared. -/
def flatCore178 : FlatPoly :=
  [ftm 0 0 3 2 (1),
    ftm 0 1 2 1 (-1),
    ftm 0 1 2 2 (1),
    ftm 0 1 3 1 (1),
    ftm 0 2 2 1 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (2),
    ftm 1 0 1 3 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 0 2 2 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (2),
    ftm 1 1 1 2 (-1),
    ftm 1 1 2 0 (1),
    ftm 1 2 1 0 (2),
    ftm 1 2 1 1 (-1),
    ftm 1 2 2 0 (-1),
    ftm 1 3 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 0 2 (1),
    ftm 2 1 1 0 (1),
    ftm 2 1 1 1 (-1),
    ftm 2 2 0 1 (1),
    ftm 2 2 1 0 (-1)]

/-- The certificate-side product for flat core 178: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct178 : Poly :=
  polyMul ([tm 6 3 0 0 0 (1)])
    (chartCore131)

/-- KERNEL-CHECKED chart soundness for flat core 178: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore178 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore178)) den one two three four
      = polyEval chartProduct178 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 179 (degree 3), denominators cleared. -/
def flatCore179 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 1 0 0 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 1 0 (1),
    ftm 0 2 0 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (1),
    ftm 1 1 1 0 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 179: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct179 : Poly :=
  polyMul ([tm 2 2 0 0 0 (1)])
    (chartCore132)

/-- KERNEL-CHECKED chart soundness for flat core 179: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore179 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore179)) den one two three four
      = polyEval chartProduct179 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 180 (degree 4), denominators cleared. -/
def flatCore180 : FlatPoly :=
  [ftm 0 0 2 2 (1),
    ftm 0 2 1 0 (1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 0 (-1),
    ftm 0 3 1 0 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 0 2 (1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (-1)]

/-- The certificate-side product for flat core 180: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct180 : Poly :=
  polyMul ([tm 7 2 0 0 0 (1)])
    (chartCore133)

/-- KERNEL-CHECKED chart soundness for flat core 180: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore180 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore180)) den one two three four
      = polyEval chartProduct180 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 181 (degree 3), denominators cleared. -/
def flatCore181 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 0 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 2 0 0 (1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 2 0 0 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 181: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct181 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    (chartCore134)

/-- KERNEL-CHECKED chart soundness for flat core 181: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore181 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore181)) den one two three four
      = polyEval chartProduct181 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 182 (degree 3), denominators cleared. -/
def flatCore182 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 1 0 0 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 2 0 0 (-1),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 182: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct182 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    (chartCore135)

/-- KERNEL-CHECKED chart soundness for flat core 182: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore182 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore182)) den one two three four
      = polyEval chartProduct182 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 183 (degree 4), denominators cleared. -/
def flatCore183 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 2 0 0 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 0 (2),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (-1),
    ftm 2 2 0 0 (-1),
    ftm 3 1 0 0 (-1)]

/-- The certificate-side product for flat core 183: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct183 : Poly :=
  polyMul ([tm 3 3 0 0 0 (1)])
    (chartCore136)

/-- KERNEL-CHECKED chart soundness for flat core 183: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore183 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore183)) den one two three four
      = polyEval chartProduct183 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 184 (degree 4), denominators cleared. -/
def flatCore184 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 1 2 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 1 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (2),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-1),
    ftm 1 3 0 0 (-1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 0 (1),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 184: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct184 : Poly :=
  polyMul ([tm 3 0 0 0 0 (1)])
    (chartCore137)

/-- KERNEL-CHECKED chart soundness for flat core 184: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore184 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore184)) den one two three four
      = polyEval chartProduct184 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 185 (degree 2), denominators cleared. -/
def flatCore185 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-1),
    ftm 1 1 0 0 (1)]

/-- The certificate-side product for flat core 185: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct185 : Poly :=
  polyMul ([tm 3 2 0 0 0 (1)])
    ([tm 3 0 0 0 0 (1),
      tm 2 0 1 0 0 (1),
      tm 1 0 1 1 0 (1),
      tm 0 0 1 1 1 (1),
      tm 0 0 2 1 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 185: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore185 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore185)) den one two three four
      = polyEval chartProduct185 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 186 (degree 2), denominators cleared. -/
def flatCore186 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 1 1 (-1),
    ftm 1 1 0 0 (1)]

/-- The certificate-side product for flat core 186: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct186 : Poly :=
  polyMul ([tm 3 0 0 0 0 (1)])
    ([tm 5 0 0 0 0 (1),
      tm 3 1 1 0 0 (1),
      tm 2 1 1 1 0 (1),
      tm 1 1 1 1 1 (1),
      tm 0 2 2 1 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 186: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore186 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore186)) den one two three four
      = polyEval chartProduct186 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 187 (degree 1), denominators cleared. -/
def flatCore187 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 1 0 0 (-1)]

/-- The certificate-side product for flat core 187: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct187 : Poly :=
  polyMul ([tm 2 0 0 0 0 (1)])
    (chartCore138)

/-- KERNEL-CHECKED chart soundness for flat core 187: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore187 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 1 flatCore187)) den one two three four
      = polyEval chartProduct187 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 188 (degree 1), denominators cleared. -/
def flatCore188 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 1 0 0 0 (-1)]

/-- The certificate-side product for flat core 188: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct188 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    (chartCore139)

/-- KERNEL-CHECKED chart soundness for flat core 188: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore188 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 1 flatCore188)) den one two three four
      = polyEval chartProduct188 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 189 (degree 4), denominators cleared. -/
def flatCore189 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 1 (-2),
    ftm 0 0 2 2 (1),
    ftm 0 0 3 1 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 1 3 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-4),
    ftm 1 0 1 2 (3),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (3),
    ftm 1 1 0 1 (-2),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (3),
    ftm 1 1 2 0 (3),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (2),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (2),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (2),
    ftm 2 1 1 0 (2)]

/-- The certificate-side product for flat core 189: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct189 : Poly :=
  polyMul ([tm 2 1 1 0 0 (-1)])
    (chartCore140)

/-- KERNEL-CHECKED chart soundness for flat core 189: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore189 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore189)) den one two three four
      = polyEval chartProduct189 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 190 (degree 4), denominators cleared. -/
def flatCore190 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-2),
    ftm 0 0 1 3 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 0 2 2 (1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-4),
    ftm 0 1 1 2 (3),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (3),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 1 1 (2),
    ftm 0 2 2 0 (2),
    ftm 1 0 0 2 (-1),
    ftm 1 0 0 3 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (-2),
    ftm 1 1 0 2 (3),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (3),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (2),
    ftm 1 2 1 0 (2)]

/-- The certificate-side product for flat core 190: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct190 : Poly :=
  polyMul ([tm 4 2 1 0 0 (1)])
    (chartCore141)

/-- KERNEL-CHECKED chart soundness for flat core 190: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore190 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore190)) den one two three four
      = polyEval chartProduct190 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 191 (degree 4), denominators cleared. -/
def flatCore191 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-3),
    ftm 0 0 2 2 (1),
    ftm 0 0 3 1 (1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-3),
    ftm 0 1 2 1 (2),
    ftm 0 1 3 0 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-3),
    ftm 1 0 1 2 (2),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (3),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-3),
    ftm 1 1 1 1 (3),
    ftm 1 1 2 0 (3),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (2),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (2)]

/-- The certificate-side product for flat core 191: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct191 : Poly :=
  polyMul ([tm 4 1 0 0 0 (-1)])
    (chartCore142)

/-- KERNEL-CHECKED chart soundness for flat core 191: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore191 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore191)) den one two three four
      = polyEval chartProduct191 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 192 (degree 4), denominators cleared. -/
def flatCore192 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-3),
    ftm 0 0 1 3 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 0 2 2 (1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 1 (-3),
    ftm 0 1 1 2 (3),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (2),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 1 (2),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-3),
    ftm 1 0 0 3 (1),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (2),
    ftm 1 1 0 1 (-3),
    ftm 1 1 0 2 (3),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (3),
    ftm 1 2 0 1 (2),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 192: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct192 : Poly :=
  polyMul ([tm 5 0 0 0 0 (1)])
    (chartCore143)

/-- KERNEL-CHECKED chart soundness for flat core 192: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore192 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore192)) den one two three four
      = polyEval chartProduct192 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 193 (degree 4), denominators cleared. -/
def flatCore193 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 0 3 1 (-1),
    ftm 0 1 2 1 (-1),
    ftm 0 1 3 0 (-1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (3),
    ftm 1 0 1 2 (-3),
    ftm 1 0 2 0 (1),
    ftm 1 0 2 1 (-3),
    ftm 1 1 1 0 (2),
    ftm 1 1 1 1 (-4),
    ftm 1 1 2 0 (-3),
    ftm 1 2 1 0 (-1),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 0 (1),
    ftm 2 0 1 1 (-2),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (-2)]

/-- The certificate-side product for flat core 193: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct193 : Poly :=
  polyMul ([tm 4 2 1 0 0 (-1)])
    (chartCore144)

/-- KERNEL-CHECKED chart soundness for flat core 193: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore193 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore193)) den one two three four
      = polyEval chartProduct193 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 194 (degree 4), denominators cleared. -/
def flatCore194 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 1 3 (-1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 0 2 (1),
    ftm 0 1 1 1 (3),
    ftm 0 1 1 2 (-3),
    ftm 0 1 2 1 (-3),
    ftm 0 2 0 1 (1),
    ftm 0 2 1 1 (-2),
    ftm 0 2 2 0 (-1),
    ftm 1 0 0 3 (-1),
    ftm 1 0 1 2 (-1),
    ftm 1 1 0 1 (2),
    ftm 1 1 0 2 (-3),
    ftm 1 1 1 1 (-4),
    ftm 1 2 0 1 (-2),
    ftm 1 2 1 0 (-1),
    ftm 2 1 0 1 (-1)]

/-- The certificate-side product for flat core 194: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct194 : Poly :=
  polyMul ([tm 6 1 1 0 0 (-1)])
    (chartCore145)

/-- KERNEL-CHECKED chart soundness for flat core 194: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore194 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore194)) den one two three four
      = polyEval chartProduct194 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 195 (degree 3), denominators cleared. -/
def flatCore195 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-2),
    ftm 1 1 0 1 (-2),
    ftm 1 1 1 0 (-1),
    ftm 2 0 0 1 (-1)]

/-- The certificate-side product for flat core 195: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct195 : Poly :=
  polyMul ([tm 5 1 1 0 0 (-1)])
    (chartCore146)

/-- KERNEL-CHECKED chart soundness for flat core 195: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore195 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore195)) den one two three four
      = polyEval chartProduct195 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 196 (degree 3), denominators cleared. -/
def flatCore196 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-2),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 1 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-2)]

/-- The certificate-side product for flat core 196: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct196 : Poly :=
  polyMul ([tm 5 1 1 0 0 (-1)])
    (chartCore147)

/-- KERNEL-CHECKED chart soundness for flat core 196: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore196 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore196)) den one two three four
      = polyEval chartProduct196 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 197 (degree 4), denominators cleared. -/
def flatCore197 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 2 1 (-2),
    ftm 0 0 3 1 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 1 3 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-4),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (3),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (1),
    ftm 1 1 2 0 (3),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (2),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (2)]

/-- The certificate-side product for flat core 197: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct197 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore148)

/-- KERNEL-CHECKED chart soundness for flat core 197: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore197 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore197)) den one two three four
      = polyEval chartProduct197 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 198 (degree 4), denominators cleared. -/
def flatCore198 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 1 (-1),
    ftm 0 0 2 2 (1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-3),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (3),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 0 (2),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (3),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (2)]

/-- The certificate-side product for flat core 198: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct198 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    (chartCore149)

/-- KERNEL-CHECKED chart soundness for flat core 198: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore198 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore198)) den one two three four
      = polyEval chartProduct198 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 199 (degree 3), denominators cleared. -/
def flatCore199 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-3),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-3),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-3),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (3),
    ftm 1 1 0 0 (-3),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (3),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (2),
    ftm 2 1 0 0 (2)]

/-- The certificate-side product for flat core 199: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct199 : Poly :=
  polyMul ([tm 1 0 0 0 0 (1)])
    ([tm 11 0 0 0 0 (1),
      tm 9 1 1 0 0 (2),
      tm 7 1 1 1 1 (2),
      tm 9 2 0 0 0 (1),
      tm 7 2 1 1 0 (2),
      tm 6 2 1 1 1 (1),
      tm 7 2 2 0 0 (1),
      tm 5 2 2 1 1 (3),
      tm 5 2 2 2 0 (1),
      tm 4 2 2 2 1 (1),
      tm 3 2 2 2 2 (1),
      tm 8 3 0 0 0 (1),
      tm 7 3 1 0 0 (1),
      tm 6 3 1 1 0 (2),
      tm 5 3 1 1 1 (2),
      tm 5 3 2 1 0 (2),
      tm 4 3 2 1 1 (1),
      tm 4 3 2 2 0 (1),
      tm 3 3 2 2 1 (3),
      tm 2 3 2 2 2 (1),
      tm 3 3 3 1 1 (1),
      tm 3 3 3 2 0 (1),
      tm 2 3 3 2 1 (1),
      tm 1 3 3 2 2 (1),
      tm 1 3 3 3 1 (1),
      tm 0 3 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 199: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore199 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore199)) den one two three four
      = polyEval chartProduct199 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 200 (degree 4), denominators cleared. -/
def flatCore200 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-2),
    ftm 0 0 2 1 (-1),
    ftm 0 0 2 2 (1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (2),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (2),
    ftm 1 1 0 1 (-2),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (3),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 200: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct200 : Poly :=
  polyMul ([tm 5 0 0 0 0 (1)])
    (chartCore150)

/-- KERNEL-CHECKED chart soundness for flat core 200: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore200 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore200)) den one two three four
      = polyEval chartProduct200 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 201 (degree 3), denominators cleared. -/
def flatCore201 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 2 0 (-1),
    ftm 1 0 0 0 (-1),
    ftm 1 0 0 1 (3),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-3),
    ftm 1 1 0 0 (2),
    ftm 1 1 0 1 (-2),
    ftm 1 1 1 0 (-3),
    ftm 1 2 0 0 (-1),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-2),
    ftm 2 1 0 0 (-2)]

/-- The certificate-side product for flat core 201: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct201 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    (chartCore151)

/-- KERNEL-CHECKED chart soundness for flat core 201: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore201 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore201)) den one two three four
      = polyEval chartProduct201 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 202 (degree 4), denominators cleared. -/
def flatCore202 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 0 2 (1),
    ftm 0 1 1 1 (3),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 1 (-3),
    ftm 0 2 0 1 (1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 0 (-1),
    ftm 1 0 1 2 (-1),
    ftm 1 1 0 1 (2),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 1 (-4),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-1),
    ftm 2 1 0 1 (-1)]

/-- The certificate-side product for flat core 202: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct202 : Poly :=
  polyMul ([tm 6 1 0 0 0 (1)])
    (chartCore152)

/-- KERNEL-CHECKED chart soundness for flat core 202: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore202 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore202)) den one two three four
      = polyEval chartProduct202 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 203 (degree 3), denominators cleared. -/
def flatCore203 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 2 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 1 (-2),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-1),
    ftm 2 0 0 1 (-1)]

/-- The certificate-side product for flat core 203: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct203 : Poly :=
  polyMul ([tm 5 1 0 0 0 (1)])
    (chartCore153)

/-- KERNEL-CHECKED chart soundness for flat core 203: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore203 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore203)) den one two three four
      = polyEval chartProduct203 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 204 (degree 2), denominators cleared. -/
def flatCore204 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-2),
    ftm 0 2 0 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 1 0 0 (-2)]

/-- The certificate-side product for flat core 204: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct204 : Poly :=
  polyMul ([tm 2 0 0 0 0 (1)])
    (chartCore154)

/-- KERNEL-CHECKED chart soundness for flat core 204: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore204 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore204)) den one two three four
      = polyEval chartProduct204 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 205 (degree 4), denominators cleared. -/
def flatCore205 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 1 (-1),
    ftm 0 0 2 2 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 1 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-3),
    ftm 1 0 1 2 (3),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 0 1 (-2),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (3),
    ftm 1 1 2 0 (1),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (2),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (2),
    ftm 2 1 1 0 (1)]

/-- The certificate-side product for flat core 205: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct205 : Poly :=
  polyMul ([tm 2 1 0 0 0 (-1)])
    (chartCore155)

/-- KERNEL-CHECKED chart soundness for flat core 205: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore205 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore205)) den one two three four
      = polyEval chartProduct205 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 206 (degree 4), denominators cleared. -/
def flatCore206 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-2),
    ftm 0 0 1 3 (1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-4),
    ftm 0 1 1 2 (3),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 1 1 (2),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 0 3 (1),
    ftm 1 1 0 1 (-2),
    ftm 1 1 0 2 (3),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (1),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (2),
    ftm 1 2 1 0 (1)]

/-- The certificate-side product for flat core 206: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct206 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    (chartCore156)

/-- KERNEL-CHECKED chart soundness for flat core 206: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore206 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore206)) den one two three four
      = polyEval chartProduct206 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 207 (degree 4), denominators cleared. -/
def flatCore207 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-2),
    ftm 0 0 2 2 (1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (2),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (2),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (3),
    ftm 1 1 2 0 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (1)]

/-- The certificate-side product for flat core 207: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct207 : Poly :=
  polyMul ([tm 4 1 0 0 0 (-1)])
    (chartCore157)

/-- KERNEL-CHECKED chart soundness for flat core 207: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore207 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore207)) den one two three four
      = polyEval chartProduct207 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 208 (degree 3), denominators cleared. -/
def flatCore208 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-3),
    ftm 0 0 1 2 (1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-3),
    ftm 0 1 1 1 (3),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (2),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-3),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-3),
    ftm 1 1 0 1 (3),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (2),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 208: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct208 : Poly :=
  polyMul ([tm 1 0 0 0 0 (1)])
    ([tm 11 0 0 0 0 (1),
      tm 10 1 0 0 0 (1),
      tm 9 1 1 0 0 (2),
      tm 8 1 1 1 0 (1),
      tm 7 1 1 1 1 (2),
      tm 8 2 1 0 0 (2),
      tm 6 2 1 1 1 (1),
      tm 7 2 2 0 0 (1),
      tm 6 2 2 1 0 (2),
      tm 5 2 2 1 1 (3),
      tm 4 2 2 2 1 (1),
      tm 3 2 2 2 2 (1),
      tm 8 3 0 0 0 (1),
      tm 6 3 1 1 0 (2),
      tm 5 3 1 1 1 (2),
      tm 6 3 2 0 0 (1),
      tm 4 3 2 1 1 (1),
      tm 4 3 2 2 0 (1),
      tm 3 3 2 2 1 (3),
      tm 2 3 2 2 2 (1),
      tm 4 3 3 1 0 (1),
      tm 3 3 3 1 1 (1),
      tm 2 3 3 2 1 (1),
      tm 1 3 3 2 2 (1),
      tm 1 3 3 3 1 (1),
      tm 0 3 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 208: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore208 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore208)) den one two three four
      = polyEval chartProduct208 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 209 (degree 4), denominators cleared. -/
def flatCore209 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 2 1 (-1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (3),
    ftm 1 0 1 2 (-3),
    ftm 1 0 2 0 (1),
    ftm 1 0 2 1 (-1),
    ftm 1 1 1 0 (2),
    ftm 1 1 1 1 (-4),
    ftm 1 1 2 0 (-1),
    ftm 1 2 1 0 (-1),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 0 (1),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (-1)]

/-- The certificate-side product for flat core 209: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct209 : Poly :=
  polyMul ([tm 4 2 0 0 0 (-1)])
    (chartCore158)

/-- KERNEL-CHECKED chart soundness for flat core 209: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore209 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore209)) den one two three four
      = polyEval chartProduct209 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 210 (degree 3), denominators cleared. -/
def flatCore210 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 0 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 1 0 (3),
    ftm 0 1 1 1 (-3),
    ftm 0 1 2 0 (-1),
    ftm 0 2 0 0 (1),
    ftm 0 2 1 0 (-2),
    ftm 1 0 0 2 (-1),
    ftm 1 1 0 0 (2),
    ftm 1 1 0 1 (-3),
    ftm 1 1 1 0 (-2),
    ftm 1 2 0 0 (-2),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 210: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct210 : Poly :=
  polyMul ([tm 2 1 0 0 0 (-1)])
    (chartCore159)

/-- KERNEL-CHECKED chart soundness for flat core 210: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore210 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore210)) den one two three four
      = polyEval chartProduct210 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 211 (degree 2), denominators cleared. -/
def flatCore211 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 1 1 0 (-1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 1 0 (-1),
    ftm 1 1 0 0 (-2),
    ftm 2 0 0 0 (-1)]

/-- The certificate-side product for flat core 211: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct211 : Poly :=
  polyMul ([tm 1 1 0 0 0 (-1)])
    (chartCore160)

/-- KERNEL-CHECKED chart soundness for flat core 211: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore211 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore211)) den one two three four
      = polyEval chartProduct211 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 212 (degree 3), denominators cleared. -/
def flatCore212 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 2 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-1)]

/-- The certificate-side product for flat core 212: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct212 : Poly :=
  polyMul ([tm 5 1 0 0 0 (-1)])
    (chartCore161)

/-- KERNEL-CHECKED chart soundness for flat core 212: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore212 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore212)) den one two three four
      = polyEval chartProduct212 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 213 (degree 4), denominators cleared. -/
def flatCore213 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 2 1 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-3),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (1),
    ftm 1 1 2 0 (1),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (1)]

/-- The certificate-side product for flat core 213: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct213 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    ([tm 13 0 0 0 0 (1),
      tm 12 1 0 0 0 (1),
      tm 11 1 1 0 0 (2),
      tm 10 1 1 1 0 (2),
      tm 9 1 1 1 1 (2),
      tm 8 1 2 2 0 (1),
      tm 7 1 2 2 1 (1),
      tm 10 2 1 0 0 (1),
      tm 9 2 1 1 0 (1),
      tm 8 2 1 1 1 (1),
      tm 9 2 2 0 0 (1),
      tm 8 2 2 1 0 (2),
      tm 7 2 2 1 1 (2),
      tm 7 2 2 2 0 (2),
      tm 6 2 2 2 1 (3),
      tm 5 2 2 2 2 (1),
      tm 6 2 3 2 0 (1),
      tm 5 2 3 2 1 (1),
      tm 5 2 3 3 0 (1),
      tm 4 2 3 3 1 (2),
      tm 3 2 3 3 2 (1),
      tm 7 3 2 1 0 (1),
      tm 6 3 2 2 0 (1),
      tm 5 3 2 2 1 (1),
      tm 5 3 3 2 0 (2),
      tm 4 3 3 2 1 (1),
      tm 4 3 3 3 0 (2),
      tm 3 3 3 3 1 (3),
      tm 2 3 3 3 2 (1),
      tm 3 3 4 3 0 (1),
      tm 2 3 4 3 1 (1),
      tm 2 3 4 4 0 (1),
      tm 1 3 4 4 1 (2),
      tm 0 3 4 4 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 213: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore213 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore213)) den one two three four
      = polyEval chartProduct213 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 214 (degree 4), denominators cleared. -/
def flatCore214 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-3),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 0 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (1),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (1)]

/-- The certificate-side product for flat core 214: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct214 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    ([tm 10 0 0 0 0 (1),
      tm 9 0 1 0 0 (1),
      tm 8 0 1 1 0 (1),
      tm 7 0 1 1 1 (1),
      tm 8 0 2 0 0 (1),
      tm 7 0 2 1 0 (1),
      tm 6 0 2 1 1 (1),
      tm 9 1 0 0 0 (1),
      tm 8 1 1 0 0 (2),
      tm 7 1 1 1 0 (2),
      tm 6 1 1 1 1 (2),
      tm 7 1 2 0 0 (2),
      tm 6 1 2 1 0 (2),
      tm 5 1 2 1 1 (3),
      tm 5 1 2 2 0 (1),
      tm 4 1 2 2 1 (2),
      tm 3 1 2 2 2 (1),
      tm 6 1 3 0 0 (2),
      tm 5 1 3 1 0 (2),
      tm 4 1 3 1 1 (3),
      tm 3 1 3 2 1 (1),
      tm 2 1 3 2 2 (1),
      tm 6 2 2 0 0 (1),
      tm 4 2 2 1 1 (1),
      tm 5 2 3 0 0 (1),
      tm 4 2 3 1 0 (1),
      tm 3 2 3 1 1 (2),
      tm 2 2 3 2 1 (1),
      tm 1 2 3 2 2 (1),
      tm 4 2 4 0 0 (1),
      tm 3 2 4 1 0 (1),
      tm 2 2 4 1 1 (2),
      tm 1 2 4 2 1 (1),
      tm 0 2 4 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 214: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore214 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore214)) den one two three four
      = polyEval chartProduct214 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 215 (degree 3), denominators cleared. -/
def flatCore215 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (1),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-2),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 215: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct215 : Poly :=
  polyMul ([tm 1 0 0 0 0 (1)])
    ([tm 11 0 0 0 0 (1),
      tm 10 1 0 0 0 (1),
      tm 9 1 1 0 0 (2),
      tm 8 1 1 1 0 (1),
      tm 7 1 1 1 1 (2),
      tm 9 2 0 0 0 (1),
      tm 8 2 1 0 0 (2),
      tm 7 2 1 1 0 (2),
      tm 6 2 1 1 1 (2),
      tm 7 2 2 0 0 (1),
      tm 6 2 2 1 0 (2),
      tm 5 2 2 1 1 (3),
      tm 5 2 2 2 0 (1),
      tm 4 2 2 2 1 (2),
      tm 3 2 2 2 2 (1),
      tm 8 3 0 0 0 (1),
      tm 7 3 1 0 0 (1),
      tm 6 3 1 1 0 (2),
      tm 5 3 1 1 1 (2),
      tm 6 3 2 0 0 (1),
      tm 5 3 2 1 0 (2),
      tm 4 3 2 1 1 (2),
      tm 4 3 2 2 0 (1),
      tm 3 3 2 2 1 (3),
      tm 2 3 2 2 2 (1),
      tm 4 3 3 1 0 (1),
      tm 3 3 3 1 1 (1),
      tm 3 3 3 2 0 (1),
      tm 2 3 3 2 1 (2),
      tm 1 3 3 2 2 (1),
      tm 1 3 3 3 1 (1),
      tm 0 3 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 215: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore215 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore215)) den one two three four
      = polyEval chartProduct215 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 216 (degree 3), denominators cleared. -/
def flatCore216 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 1 0 0 0 (-1),
    ftm 1 0 0 1 (3),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 1 0 0 (2),
    ftm 1 1 0 1 (-2),
    ftm 1 1 1 0 (-1),
    ftm 1 2 0 0 (-1),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 216: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct216 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    (chartCore162)

/-- KERNEL-CHECKED chart soundness for flat core 216: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore216 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore216)) den one two three four
      = polyEval chartProduct216 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 217 (degree 3), denominators cleared. -/
def flatCore217 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 1 0 0 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 1 0 (3),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 0 0 (1),
    ftm 0 2 1 0 (-1),
    ftm 1 1 0 0 (2),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-2),
    ftm 1 2 0 0 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 217: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct217 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore163)

/-- KERNEL-CHECKED chart soundness for flat core 217: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore217 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore217)) den one two three four
      = polyEval chartProduct217 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 218 (degree 2), denominators cleared. -/
def flatCore218 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 1 0 (-1),
    ftm 1 1 0 0 (-1),
    ftm 2 0 0 0 (-1)]

/-- The certificate-side product for flat core 218: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct218 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    ([tm 6 0 0 0 0 (1),
      tm 5 1 0 0 0 (1),
      tm 4 1 1 0 0 (1),
      tm 3 1 1 1 0 (1),
      tm 2 1 1 1 1 (1),
      tm 0 1 2 2 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 218: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore218 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore218)) den one two three four
      = polyEval chartProduct218 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 219 (degree 2), denominators cleared. -/
def flatCore219 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 2 0 0 (-1),
    ftm 1 1 0 0 (-1)]

/-- The certificate-side product for flat core 219: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct219 : Poly :=
  polyMul ([tm 2 0 0 0 0 (1)])
    ([tm 6 0 0 0 0 (1),
      tm 5 1 0 0 0 (1),
      tm 4 1 1 0 0 (1),
      tm 3 1 1 1 0 (1),
      tm 2 1 1 1 1 (1),
      tm 0 2 2 1 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 219: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore219 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore219)) den one two three four
      = polyEval chartProduct219 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 220 (degree 4), denominators cleared. -/
def flatCore220 : FlatPoly :=
  [ftm 0 0 1 1 (2),
    ftm 0 0 1 2 (-2),
    ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-4),
    ftm 0 0 2 2 (2),
    ftm 0 0 3 0 (-1),
    ftm 0 0 3 1 (2),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-3),
    ftm 0 1 2 1 (2),
    ftm 0 1 3 0 (2),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 0 (2),
    ftm 1 0 1 1 (-6),
    ftm 1 0 1 2 (4),
    ftm 1 0 2 0 (-2),
    ftm 1 0 2 1 (4),
    ftm 1 1 0 1 (-2),
    ftm 1 1 1 0 (-4),
    ftm 1 1 1 1 (4),
    ftm 1 1 2 0 (4),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (2),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (2),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (2),
    ftm 2 1 1 0 (2)]

/-- The certificate-side product for flat core 220: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct220 : Poly :=
  polyMul ([tm 2 1 0 0 0 (-1)])
    (chartCore164)

/-- KERNEL-CHECKED chart soundness for flat core 220: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore220 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore220)) den one two three four
      = polyEval chartProduct220 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 221 (degree 5), denominators cleared. -/
def flatCore221 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-2),
    ftm 0 1 2 2 (1),
    ftm 0 1 3 0 (-1),
    ftm 0 1 3 1 (1),
    ftm 0 2 1 0 (1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 0 (-2),
    ftm 0 2 2 1 (1),
    ftm 0 2 3 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-2),
    ftm 1 0 1 3 (1),
    ftm 1 0 2 1 (-1),
    ftm 1 0 2 2 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 0 (2),
    ftm 1 1 1 1 (-6),
    ftm 1 1 1 2 (4),
    ftm 1 1 2 0 (-3),
    ftm 1 1 2 1 (4),
    ftm 1 2 0 0 (1),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-4),
    ftm 1 2 1 1 (3),
    ftm 1 2 2 0 (3),
    ftm 2 0 0 2 (-1),
    ftm 2 0 0 3 (1),
    ftm 2 0 1 1 (-1),
    ftm 2 0 1 2 (1),
    ftm 2 1 0 1 (-2),
    ftm 2 1 0 2 (3),
    ftm 2 1 1 0 (-2),
    ftm 2 1 1 1 (3),
    ftm 2 2 0 0 (-1),
    ftm 2 2 0 1 (2),
    ftm 2 2 1 0 (2)]

/-- The certificate-side product for flat core 221: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct221 : Poly :=
  polyMul ([tm 5 3 1 0 0 (1)])
    (chartCore165)

/-- KERNEL-CHECKED chart soundness for flat core 221: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore221 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore221)) den one two three four
      = polyEval chartProduct221 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 222 (degree 5), denominators cleared. -/
def flatCore222 : FlatPoly :=
  [ftm 0 0 3 0 (1),
    ftm 0 0 3 1 (-1),
    ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-1),
    ftm 0 1 3 0 (-2),
    ftm 0 1 3 1 (1),
    ftm 0 2 2 0 (-1),
    ftm 0 2 3 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 0 (2),
    ftm 1 0 2 1 (-4),
    ftm 1 0 2 2 (1),
    ftm 1 0 3 0 (-1),
    ftm 1 0 3 1 (2),
    ftm 1 1 1 0 (2),
    ftm 1 1 1 1 (-2),
    ftm 1 1 2 0 (-6),
    ftm 1 1 2 1 (3),
    ftm 1 1 3 0 (2),
    ftm 1 2 1 0 (-1),
    ftm 1 2 2 0 (2),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 0 (1),
    ftm 2 0 1 1 (-3),
    ftm 2 0 1 2 (2),
    ftm 2 0 2 0 (-2),
    ftm 2 0 2 1 (4),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (-4),
    ftm 2 1 1 1 (3),
    ftm 2 1 2 0 (4),
    ftm 2 2 1 0 (1),
    ftm 3 0 0 2 (1),
    ftm 3 0 1 0 (-1),
    ftm 3 0 1 1 (2),
    ftm 3 1 0 1 (1),
    ftm 3 1 1 0 (2)]

/-- The certificate-side product for flat core 222: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct222 : Poly :=
  polyMul ([tm 5 2 0 0 0 (-1)])
    (chartCore166)

/-- KERNEL-CHECKED chart soundness for flat core 222: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore222 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore222)) den one two three four
      = polyEval chartProduct222 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 223 (degree 5), denominators cleared. -/
def flatCore223 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 1 (-1),
    ftm 0 1 2 2 (1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 1 (1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (2),
    ftm 1 0 1 2 (-5),
    ftm 1 0 1 3 (1),
    ftm 1 0 2 1 (-2),
    ftm 1 0 2 2 (2),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 1 (-6),
    ftm 1 1 1 2 (4),
    ftm 1 1 2 0 (-1),
    ftm 1 1 2 1 (3),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-1),
    ftm 1 2 1 1 (3),
    ftm 1 2 2 0 (1),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-3),
    ftm 2 0 0 3 (1),
    ftm 2 0 1 1 (-3),
    ftm 2 0 1 2 (3),
    ftm 2 1 0 1 (-3),
    ftm 2 1 0 2 (3),
    ftm 2 1 1 0 (-1),
    ftm 2 1 1 1 (4),
    ftm 2 2 0 1 (2),
    ftm 2 2 1 0 (1),
    ftm 3 0 0 1 (-1),
    ftm 3 0 0 2 (1),
    ftm 3 1 0 1 (1)]

/-- The certificate-side product for flat core 223: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct223 : Poly :=
  polyMul ([tm 6 1 0 0 0 (1)])
    ([tm 13 0 0 0 0 (1),
      tm 11 0 1 1 0 (1),
      tm 12 1 0 0 0 (1),
      tm 11 1 1 0 0 (2),
      tm 10 1 1 1 0 (2),
      tm 9 1 1 1 1 (2),
      tm 9 1 2 1 0 (2),
      tm 8 1 2 2 0 (1),
      tm 7 1 2 2 1 (2),
      tm 10 2 1 0 0 (2),
      tm 9 2 1 1 0 (1),
      tm 8 2 1 1 1 (1),
      tm 9 2 2 0 0 (1),
      tm 8 2 2 1 0 (4),
      tm 7 2 2 1 1 (3),
      tm 7 2 2 2 0 (1),
      tm 6 2 2 2 1 (3),
      tm 5 2 2 2 2 (1),
      tm 7 2 3 1 0 (1),
      tm 6 2 3 2 0 (2),
      tm 5 2 3 2 1 (3),
      tm 4 2 3 3 1 (1),
      tm 3 2 3 3 2 (1),
      tm 8 3 2 0 0 (1),
      tm 7 3 2 1 0 (2),
      tm 6 3 2 1 1 (1),
      tm 5 3 2 2 1 (2),
      tm 6 3 3 1 0 (2),
      tm 5 3 3 1 1 (1),
      tm 5 3 3 2 0 (2),
      tm 4 3 3 2 1 (4),
      tm 3 3 3 2 2 (1),
      tm 3 3 3 3 1 (3),
      tm 2 3 3 3 2 (2),
      tm 4 3 4 2 0 (1),
      tm 3 3 4 2 1 (1),
      tm 2 3 4 3 1 (1),
      tm 1 3 4 3 2 (1),
      tm 1 3 4 4 1 (1),
      tm 0 3 4 4 2 (1),
      tm 5 4 3 1 0 (1),
      tm 3 4 3 2 1 (1),
      tm 3 4 4 2 0 (1),
      tm 2 4 4 2 1 (1),
      tm 1 4 4 3 1 (1),
      tm 0 4 4 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 223: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore223 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore223)) den one two three four
      = polyEval chartProduct223 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 224 (degree 3), denominators cleared. -/
def flatCore224 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-3),
    ftm 0 0 1 2 (2),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (2),
    ftm 0 1 1 0 (-3),
    ftm 0 1 1 1 (3),
    ftm 0 1 2 0 (2),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (2)]

/-- The certificate-side product for flat core 224: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct224 : Poly :=
  polyMul ([tm 3 1 1 0 0 (1)])
    (chartCore167)

/-- KERNEL-CHECKED chart soundness for flat core 224: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore224 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore224)) den one two three four
      = polyEval chartProduct224 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 225 (degree 5), denominators cleared. -/
def flatCore225 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 1 (-2),
    ftm 0 1 2 2 (1),
    ftm 0 1 3 1 (1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 1 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 0 1 3 (1),
    ftm 1 0 2 2 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 1 (-6),
    ftm 1 1 1 2 (4),
    ftm 1 1 2 1 (5),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-1),
    ftm 1 2 1 1 (3),
    ftm 1 2 2 0 (1),
    ftm 2 0 0 3 (1),
    ftm 2 0 1 2 (1),
    ftm 2 1 0 1 (-2),
    ftm 2 1 0 2 (3),
    ftm 2 1 1 1 (5),
    ftm 2 2 0 1 (2),
    ftm 2 2 1 0 (1),
    ftm 3 1 0 1 (1)]

/-- The certificate-side product for flat core 225: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct225 : Poly :=
  polyMul ([tm 7 2 2 1 0 (1)])
    (chartCore168)

/-- KERNEL-CHECKED chart soundness for flat core 225: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore225 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore225)) den one two three four
      = polyEval chartProduct225 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 226 (degree 3), denominators cleared. -/
def flatCore226 : FlatPoly :=
  [ftm 0 0 1 1 (2),
    ftm 0 0 1 2 (-2),
    ftm 0 0 2 1 (-2),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-3),
    ftm 1 1 0 1 (-2),
    ftm 1 1 1 0 (-1),
    ftm 2 0 0 1 (-1)]

/-- The certificate-side product for flat core 226: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct226 : Poly :=
  polyMul ([tm 5 1 1 0 0 (-1)])
    (chartCore169)

/-- KERNEL-CHECKED chart soundness for flat core 226: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore226 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore226)) den one two three four
      = polyEval chartProduct226 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 227 (degree 4), denominators cleared. -/
def flatCore227 : FlatPoly :=
  [ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-1),
    ftm 0 1 3 0 (-1),
    ftm 0 2 2 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 1 (-1),
    ftm 1 1 1 0 (2),
    ftm 1 1 1 1 (-2),
    ftm 1 1 2 0 (-3),
    ftm 1 2 1 0 (-1),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (-2)]

/-- The certificate-side product for flat core 227: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct227 : Poly :=
  polyMul ([tm 6 2 2 1 0 (-1)])
    (chartCore170)

/-- KERNEL-CHECKED chart soundness for flat core 227: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore227 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore227)) den one two three four
      = polyEval chartProduct227 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 228 (degree 5), denominators cleared. -/
def flatCore228 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 1 (-2),
    ftm 0 1 2 2 (1),
    ftm 0 1 3 1 (1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 0 (-1),
    ftm 0 2 2 1 (1),
    ftm 0 2 3 0 (1),
    ftm 1 0 0 2 (1),
    ftm 1 0 0 3 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-2),
    ftm 1 0 1 3 (1),
    ftm 1 0 2 1 (-1),
    ftm 1 0 2 2 (1),
    ftm 1 1 0 1 (2),
    ftm 1 1 0 2 (-3),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 1 (-6),
    ftm 1 1 1 2 (4),
    ftm 1 1 2 0 (-1),
    ftm 1 1 2 1 (4),
    ftm 1 2 0 1 (-2),
    ftm 1 2 1 0 (-2),
    ftm 1 2 1 1 (3),
    ftm 1 2 2 0 (3),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-2),
    ftm 2 0 0 3 (1),
    ftm 2 0 1 1 (-1),
    ftm 2 0 1 2 (1),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (-4),
    ftm 2 1 0 2 (3),
    ftm 2 1 1 0 (-1),
    ftm 2 1 1 1 (3),
    ftm 2 2 0 0 (-1),
    ftm 2 2 0 1 (2),
    ftm 2 2 1 0 (2)]

/-- The certificate-side product for flat core 228: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct228 : Poly :=
  polyMul ([tm 4 2 1 0 0 (1)])
    (chartCore171)

/-- KERNEL-CHECKED chart soundness for flat core 228: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore228 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore228)) den one two three four
      = polyEval chartProduct228 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 229 (degree 4), denominators cleared. -/
def flatCore229 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 0 3 (-1),
    ftm 0 0 1 1 (2),
    ftm 0 0 1 2 (-4),
    ftm 0 0 1 3 (2),
    ftm 0 0 2 1 (-2),
    ftm 0 0 2 2 (2),
    ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-2),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-6),
    ftm 0 1 1 2 (4),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (4),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 1 1 (2),
    ftm 0 2 2 0 (2),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-3),
    ftm 1 0 0 3 (2),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (2),
    ftm 1 1 0 1 (-4),
    ftm 1 1 0 2 (4),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (4),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (2),
    ftm 1 2 1 0 (2)]

/-- The certificate-side product for flat core 229: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct229 : Poly :=
  polyMul ([tm 4 1 0 0 0 (1)])
    (chartCore172)

/-- KERNEL-CHECKED chart soundness for flat core 229: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore229 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore229)) den one two three four
      = polyEval chartProduct229 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 230 (degree 5), denominators cleared. -/
def flatCore230 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 1 1 (2),
    ftm 0 1 1 2 (-2),
    ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-5),
    ftm 0 1 2 2 (2),
    ftm 0 1 3 1 (1),
    ftm 0 2 1 0 (1),
    ftm 0 2 1 1 (-3),
    ftm 0 2 2 0 (-3),
    ftm 0 2 2 1 (3),
    ftm 0 2 3 0 (1),
    ftm 0 3 1 0 (-1),
    ftm 0 3 2 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 1 (-1),
    ftm 1 0 2 2 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 1 (-6),
    ftm 1 1 1 2 (3),
    ftm 1 1 2 0 (-1),
    ftm 1 1 2 1 (4),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-3),
    ftm 1 2 1 1 (4),
    ftm 1 2 2 0 (3),
    ftm 1 3 1 0 (1),
    ftm 2 0 1 1 (-1),
    ftm 2 0 1 2 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 0 2 (1),
    ftm 2 1 1 0 (-1),
    ftm 2 1 1 1 (3),
    ftm 2 2 0 1 (1),
    ftm 2 2 1 0 (2)]

/-- The certificate-side product for flat core 230: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct230 : Poly :=
  polyMul ([tm 6 3 0 0 0 (1)])
    ([tm 11 0 0 0 0 (1),
      tm 10 0 1 0 0 (1),
      tm 9 0 1 1 0 (2),
      tm 8 0 1 1 1 (1),
      tm 8 0 2 1 0 (2),
      tm 7 0 2 1 1 (2),
      tm 7 0 2 2 0 (1),
      tm 6 0 2 2 1 (1),
      tm 6 0 3 2 0 (1),
      tm 5 0 3 2 1 (1),
      tm 10 1 0 0 0 (1),
      tm 9 1 1 0 0 (2),
      tm 8 1 1 1 0 (2),
      tm 7 1 1 1 1 (2),
      tm 8 1 2 0 0 (1),
      tm 7 1 2 1 0 (4),
      tm 6 1 2 1 1 (3),
      tm 6 1 2 2 0 (1),
      tm 5 1 2 2 1 (3),
      tm 4 1 2 2 2 (1),
      tm 6 1 3 1 0 (2),
      tm 5 1 3 1 1 (3),
      tm 5 1 3 2 0 (2),
      tm 4 1 3 2 1 (4),
      tm 3 1 3 2 2 (2),
      tm 3 1 3 3 1 (1),
      tm 2 1 3 3 2 (1),
      tm 4 1 4 2 0 (1),
      tm 3 1 4 2 1 (1),
      tm 2 1 4 3 1 (1),
      tm 1 1 4 3 2 (1),
      tm 8 2 1 0 0 (1),
      tm 7 2 2 0 0 (1),
      tm 6 2 2 1 0 (2),
      tm 5 2 2 1 1 (2),
      tm 5 2 3 1 0 (2),
      tm 4 2 3 1 1 (1),
      tm 4 2 3 2 0 (1),
      tm 3 2 3 2 1 (3),
      tm 2 2 3 2 2 (1),
      tm 3 2 4 1 1 (1),
      tm 3 2 4 2 0 (1),
      tm 2 2 4 2 1 (1),
      tm 1 2 4 2 2 (1),
      tm 1 2 4 3 1 (1),
      tm 0 2 4 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 230: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore230 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore230)) den one two three four
      = polyEval chartProduct230 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 231 (degree 5), denominators cleared. -/
def flatCore231 : FlatPoly :=
  [ftm 0 0 0 3 (1),
    ftm 0 0 1 3 (-1),
    ftm 0 1 0 2 (2),
    ftm 0 1 0 3 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-4),
    ftm 0 1 1 3 (2),
    ftm 0 1 2 1 (-1),
    ftm 0 1 2 2 (1),
    ftm 0 2 0 1 (1),
    ftm 0 2 0 2 (-2),
    ftm 0 2 1 1 (-3),
    ftm 0 2 1 2 (4),
    ftm 0 2 2 0 (-1),
    ftm 0 2 2 1 (2),
    ftm 0 3 0 1 (-1),
    ftm 0 3 1 1 (2),
    ftm 0 3 2 0 (1),
    ftm 1 0 0 2 (1),
    ftm 1 0 0 3 (-2),
    ftm 1 0 1 2 (-1),
    ftm 1 0 1 3 (1),
    ftm 1 1 0 1 (2),
    ftm 1 1 0 2 (-6),
    ftm 1 1 0 3 (2),
    ftm 1 1 1 1 (-2),
    ftm 1 1 1 2 (3),
    ftm 1 2 0 1 (-4),
    ftm 1 2 0 2 (4),
    ftm 1 2 1 0 (-1),
    ftm 1 2 1 1 (3),
    ftm 1 3 0 1 (2),
    ftm 1 3 1 0 (1),
    ftm 2 0 0 2 (-1),
    ftm 2 0 0 3 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 0 2 (2),
    ftm 2 2 0 1 (1)]

/-- The certificate-side product for flat core 231: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct231 : Poly :=
  polyMul ([tm 7 0 0 0 0 (1)])
    (chartCore173)

/-- KERNEL-CHECKED chart soundness for flat core 231: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore231 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore231)) den one two three four
      = polyEval chartProduct231 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 232 (degree 5), denominators cleared. -/
def flatCore232 : FlatPoly :=
  [ftm 0 1 2 1 (1),
    ftm 0 1 2 2 (-1),
    ftm 0 1 3 1 (-1),
    ftm 0 2 2 1 (-1),
    ftm 0 2 3 0 (-1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (2),
    ftm 1 0 1 3 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 0 2 2 (-1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (6),
    ftm 1 1 1 2 (-5),
    ftm 1 1 2 0 (1),
    ftm 1 1 2 1 (-4),
    ftm 1 2 1 0 (2),
    ftm 1 2 1 1 (-5),
    ftm 1 2 2 0 (-3),
    ftm 1 3 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 0 1 2 (-1),
    ftm 2 1 0 1 (1),
    ftm 2 1 0 2 (-1),
    ftm 2 1 1 0 (1),
    ftm 2 1 1 1 (-3),
    ftm 2 2 0 1 (-1),
    ftm 2 2 1 0 (-2)]

/-- The certificate-side product for flat core 232: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct232 : Poly :=
  polyMul ([tm 6 4 2 0 0 (1)])
    (chartCore174)

/-- KERNEL-CHECKED chart soundness for flat core 232: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore232 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore232)) den one two three four
      = polyEval chartProduct232 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 233 (degree 3), denominators cleared. -/
def flatCore233 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-3),
    ftm 0 0 1 2 (2),
    ftm 0 0 2 1 (2),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 1 (2),
    ftm 0 1 2 0 (1),
    ftm 1 0 0 1 (-3),
    ftm 1 0 0 2 (2),
    ftm 1 0 1 1 (3),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 233: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct233 : Poly :=
  polyMul ([tm 4 1 1 0 0 (1)])
    (chartCore175)

/-- KERNEL-CHECKED chart soundness for flat core 233: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore233 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore233)) den one two three four
      = polyEval chartProduct233 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 234 (degree 4), denominators cleared. -/
def flatCore234 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 1 (-1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 0 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 0 3 (-1),
    ftm 1 0 1 2 (-1),
    ftm 1 1 0 1 (2),
    ftm 1 1 0 2 (-3),
    ftm 1 1 1 1 (-2),
    ftm 1 2 0 1 (-2),
    ftm 1 2 1 0 (-1),
    ftm 2 0 0 2 (-1),
    ftm 2 1 0 1 (-1)]

/-- The certificate-side product for flat core 234: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct234 : Poly :=
  polyMul ([tm 7 2 2 0 0 (1)])
    (chartCore176)

/-- KERNEL-CHECKED chart soundness for flat core 234: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore234 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore234)) den one two three four
      = polyEval chartProduct234 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 235 (degree 3), denominators cleared. -/
def flatCore235 : FlatPoly :=
  [ftm 0 0 1 1 (2),
    ftm 0 0 1 2 (-2),
    ftm 0 0 2 1 (-2),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-3),
    ftm 0 1 2 0 (-2),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 1 (-2),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-2)]

/-- The certificate-side product for flat core 235: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct235 : Poly :=
  polyMul ([tm 5 2 1 0 0 (1)])
    (chartCore177)

/-- KERNEL-CHECKED chart soundness for flat core 235: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore235 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore235)) den one two three four
      = polyEval chartProduct235 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 236 (degree 5), denominators cleared. -/
def flatCore236 : FlatPoly :=
  [ftm 0 1 2 1 (1),
    ftm 0 1 3 1 (-1),
    ftm 0 2 2 0 (1),
    ftm 0 2 3 0 (-1),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (4),
    ftm 1 0 2 2 (-1),
    ftm 1 0 3 0 (1),
    ftm 1 0 3 1 (-2),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (2),
    ftm 1 1 2 0 (3),
    ftm 1 1 2 1 (-3),
    ftm 1 1 3 0 (-2),
    ftm 1 2 1 0 (1),
    ftm 1 2 2 0 (-2),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (-2),
    ftm 2 0 1 1 (6),
    ftm 2 0 1 2 (-2),
    ftm 2 0 2 0 (2),
    ftm 2 0 2 1 (-4),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (4),
    ftm 2 1 1 1 (-3),
    ftm 2 1 2 0 (-4),
    ftm 2 2 1 0 (-1),
    ftm 3 0 0 0 (-1),
    ftm 3 0 0 1 (2),
    ftm 3 0 0 2 (-1),
    ftm 3 0 1 0 (1),
    ftm 3 0 1 1 (-2),
    ftm 3 1 0 0 (1),
    ftm 3 1 0 1 (-1),
    ftm 3 1 1 0 (-2)]

/-- The certificate-side product for flat core 236: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct236 : Poly :=
  polyMul ([tm 3 2 1 0 0 (-1)])
    (chartCore178)

/-- KERNEL-CHECKED chart soundness for flat core 236: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore236 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore236)) den one two three four
      = polyEval chartProduct236 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 237 (degree 5), denominators cleared. -/
def flatCore237 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-3),
    ftm 0 1 2 2 (2),
    ftm 0 1 3 0 (-1),
    ftm 0 1 3 1 (1),
    ftm 0 2 1 0 (1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 0 (-3),
    ftm 0 2 2 1 (3),
    ftm 0 2 3 0 (1),
    ftm 0 3 2 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 1 (-1),
    ftm 1 0 2 2 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 0 (2),
    ftm 1 1 1 1 (-6),
    ftm 1 1 1 2 (3),
    ftm 1 1 2 0 (-3),
    ftm 1 1 2 1 (4),
    ftm 1 2 0 0 (1),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-5),
    ftm 1 2 1 1 (4),
    ftm 1 2 2 0 (3),
    ftm 1 3 1 0 (1),
    ftm 2 0 1 1 (-1),
    ftm 2 0 1 2 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 0 2 (1),
    ftm 2 1 1 0 (-2),
    ftm 2 1 1 1 (3),
    ftm 2 2 0 0 (-1),
    ftm 2 2 0 1 (1),
    ftm 2 2 1 0 (2)]

/-- The certificate-side product for flat core 237: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct237 : Poly :=
  polyMul ([tm 5 3 1 0 0 (1)])
    ([tm 11 0 0 0 0 (1),
      tm 10 0 0 1 0 (1),
      tm 10 0 1 0 0 (1),
      tm 9 0 1 1 0 (2),
      tm 8 0 1 1 1 (1),
      tm 8 0 1 2 0 (1),
      tm 7 0 1 2 1 (1),
      tm 8 0 2 1 0 (1),
      tm 7 0 2 2 0 (1),
      tm 6 0 2 2 1 (1),
      tm 9 1 1 0 0 (2),
      tm 8 1 1 1 0 (2),
      tm 7 1 1 1 1 (1),
      tm 6 1 1 2 1 (1),
      tm 8 1 2 0 0 (2),
      tm 7 1 2 1 0 (4),
      tm 6 1 2 1 1 (3),
      tm 6 1 2 2 0 (2),
      tm 5 1 2 2 1 (4),
      tm 4 1 2 2 2 (1),
      tm 4 1 2 3 1 (1),
      tm 3 1 2 3 2 (1),
      tm 6 1 3 1 0 (2),
      tm 5 1 3 2 0 (2),
      tm 4 1 3 2 1 (3),
      tm 3 1 3 3 1 (1),
      tm 2 1 3 3 2 (1),
      tm 6 2 1 1 1 (1),
      tm 7 2 2 0 0 (1),
      tm 6 2 2 1 0 (1),
      tm 5 2 2 1 1 (1),
      tm 4 2 2 2 1 (3),
      tm 3 2 2 2 2 (1),
      tm 6 2 3 0 0 (1),
      tm 5 2 3 1 0 (2),
      tm 4 2 3 1 1 (2),
      tm 4 2 3 2 0 (1),
      tm 3 2 3 2 1 (3),
      tm 2 2 3 2 2 (1),
      tm 2 2 3 3 1 (2),
      tm 1 2 3 3 2 (2),
      tm 4 2 4 1 0 (1),
      tm 3 2 4 2 0 (1),
      tm 2 2 4 2 1 (2),
      tm 1 2 4 3 1 (1),
      tm 0 2 4 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 237: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore237 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore237)) den one two three four
      = polyEval chartProduct237 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 238 (degree 4), denominators cleared. -/
def flatCore238 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (2),
    ftm 0 2 1 0 (-2),
    ftm 0 2 2 0 (2),
    ftm 1 0 0 1 (1),
    ftm 1 0 1 0 (2),
    ftm 1 0 1 1 (-4),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (2),
    ftm 1 1 0 0 (2),
    ftm 1 1 0 1 (-2),
    ftm 1 1 1 0 (-6),
    ftm 1 1 1 1 (4),
    ftm 1 1 2 0 (2),
    ftm 1 2 0 0 (-2),
    ftm 1 2 1 0 (4),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-3),
    ftm 2 0 1 0 (-2),
    ftm 2 0 1 1 (4),
    ftm 2 1 0 0 (-4),
    ftm 2 1 0 1 (2),
    ftm 2 1 1 0 (4),
    ftm 2 2 0 0 (2),
    ftm 3 0 0 0 (-1),
    ftm 3 0 0 1 (2),
    ftm 3 1 0 0 (2)]

/-- The certificate-side product for flat core 238: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct238 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore179)

/-- KERNEL-CHECKED chart soundness for flat core 238: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore238 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore238)) den one two three four
      = polyEval chartProduct238 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 239 (degree 5), denominators cleared. -/
def flatCore239 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 1 (-2),
    ftm 0 1 2 2 (2),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 0 (-1),
    ftm 0 2 2 1 (3),
    ftm 0 3 2 0 (1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (2),
    ftm 1 0 1 2 (-4),
    ftm 1 0 2 1 (-2),
    ftm 1 0 2 2 (2),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 1 (-6),
    ftm 1 1 1 2 (3),
    ftm 1 1 2 0 (-1),
    ftm 1 1 2 1 (3),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-2),
    ftm 1 2 1 1 (4),
    ftm 1 2 2 0 (1),
    ftm 1 3 1 0 (1),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-2),
    ftm 2 0 1 1 (-3),
    ftm 2 0 1 2 (3),
    ftm 2 1 0 1 (-2),
    ftm 2 1 0 2 (1),
    ftm 2 1 1 0 (-1),
    ftm 2 1 1 1 (4),
    ftm 2 2 0 1 (1),
    ftm 2 2 1 0 (1),
    ftm 3 0 0 1 (-1),
    ftm 3 0 0 2 (1),
    ftm 3 1 0 1 (1)]

/-- The certificate-side product for flat core 239: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct239 : Poly :=
  polyMul ([tm 6 1 0 0 0 (1)])
    (chartCore180)

/-- KERNEL-CHECKED chart soundness for flat core 239: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore239 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore239)) den one two three four
      = polyEval chartProduct239 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 240 (degree 3), denominators cleared. -/
def flatCore240 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-3),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 0 (-3),
    ftm 1 1 0 1 (3),
    ftm 1 1 1 0 (2),
    ftm 1 2 0 0 (2),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (2),
    ftm 2 1 0 0 (2)]

/-- The certificate-side product for flat core 240: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct240 : Poly :=
  polyMul ([tm 1 1 1 0 0 (-1)])
    (chartCore181)

/-- KERNEL-CHECKED chart soundness for flat core 240: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore240 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore240)) den one two three four
      = polyEval chartProduct240 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 241 (degree 5), denominators cleared. -/
def flatCore241 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 1 (-2),
    ftm 0 1 2 2 (2),
    ftm 0 1 3 1 (1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 1 (3),
    ftm 0 3 2 0 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 2 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 1 (-6),
    ftm 1 1 1 2 (3),
    ftm 1 1 2 1 (5),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-1),
    ftm 1 2 1 1 (4),
    ftm 1 2 2 0 (1),
    ftm 1 3 1 0 (1),
    ftm 2 0 1 2 (1),
    ftm 2 1 0 1 (-2),
    ftm 2 1 0 2 (1),
    ftm 2 1 1 1 (5),
    ftm 2 2 0 1 (1),
    ftm 2 2 1 0 (1),
    ftm 3 1 0 1 (1)]

/-- The certificate-side product for flat core 241: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct241 : Poly :=
  polyMul ([tm 7 2 1 0 0 (-1)])
    (chartCore182)

/-- KERNEL-CHECKED chart soundness for flat core 241: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore241 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore241)) den one two three four
      = polyEval chartProduct241 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 242 (degree 4), denominators cleared. -/
def flatCore242 : FlatPoly :=
  [ftm 0 1 2 1 (1),
    ftm 0 2 2 0 (1),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 1 (2),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (2),
    ftm 1 1 2 0 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 1 (3),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (1),
    ftm 3 0 0 1 (1)]

/-- The certificate-side product for flat core 242: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct242 : Poly :=
  polyMul ([tm 6 2 1 0 0 (-1)])
    (chartCore183)

/-- KERNEL-CHECKED chart soundness for flat core 242: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore242 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore242)) den one two three four
      = polyEval chartProduct242 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 243 (degree 3), denominators cleared. -/
def flatCore243 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-1),
    ftm 0 2 1 0 (-2),
    ftm 1 0 0 1 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 1 0 0 (2),
    ftm 1 1 0 1 (-2),
    ftm 1 1 1 0 (-3),
    ftm 1 2 0 0 (-2),
    ftm 2 0 0 1 (-1),
    ftm 2 1 0 0 (-2)]

/-- The certificate-side product for flat core 243: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct243 : Poly :=
  polyMul ([tm 3 1 1 0 0 (1)])
    (chartCore184)

/-- KERNEL-CHECKED chart soundness for flat core 243: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore243 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore243)) den one two three four
      = polyEval chartProduct243 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 244 (degree 5), denominators cleared. -/
def flatCore244 : FlatPoly :=
  [ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 1 (-1),
    ftm 0 1 2 2 (1),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 1 (1),
    ftm 1 0 0 2 (1),
    ftm 1 0 0 3 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-3),
    ftm 1 0 1 3 (1),
    ftm 1 0 2 1 (-1),
    ftm 1 0 2 2 (2),
    ftm 1 1 0 1 (2),
    ftm 1 1 0 2 (-3),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 1 (-6),
    ftm 1 1 1 2 (4),
    ftm 1 1 2 0 (-1),
    ftm 1 1 2 1 (3),
    ftm 1 2 0 1 (-2),
    ftm 1 2 1 0 (-1),
    ftm 1 2 1 1 (3),
    ftm 1 2 2 0 (1),
    ftm 2 0 0 1 (1),
    ftm 2 0 0 2 (-3),
    ftm 2 0 0 3 (1),
    ftm 2 0 1 1 (-1),
    ftm 2 0 1 2 (3),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (-5),
    ftm 2 1 0 2 (3),
    ftm 2 1 1 0 (-1),
    ftm 2 1 1 1 (4),
    ftm 2 2 0 0 (-1),
    ftm 2 2 0 1 (2),
    ftm 2 2 1 0 (1),
    ftm 3 0 0 2 (1),
    ftm 3 1 0 1 (1)]

/-- The certificate-side product for flat core 244: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct244 : Poly :=
  polyMul ([tm 4 2 1 0 0 (1)])
    ([tm 9 0 1 2 1 (1),
      tm 12 1 0 0 0 (1),
      tm 11 1 0 1 0 (1),
      tm 10 1 1 1 0 (2),
      tm 9 1 1 1 1 (1),
      tm 9 1 1 2 0 (2),
      tm 8 1 1 2 1 (1),
      tm 8 1 2 2 0 (1),
      tm 7 1 2 2 1 (3),
      tm 7 1 2 3 0 (1),
      tm 6 1 2 3 1 (1),
      tm 5 1 2 3 2 (1),
      tm 10 2 1 0 0 (1),
      tm 9 2 1 1 0 (2),
      tm 8 2 1 1 1 (1),
      tm 8 2 1 2 0 (1),
      tm 7 2 1 2 1 (1),
      tm 8 2 2 1 0 (2),
      tm 7 2 2 1 1 (1),
      tm 7 2 2 2 0 (4),
      tm 6 2 2 2 1 (4),
      tm 5 2 2 2 2 (1),
      tm 6 2 2 3 0 (2),
      tm 5 2 2 3 1 (3),
      tm 4 2 2 3 2 (1),
      tm 6 2 3 2 0 (1),
      tm 5 2 3 2 1 (2),
      tm 5 2 3 3 0 (2),
      tm 4 2 3 3 1 (3),
      tm 3 2 3 3 2 (2),
      tm 4 2 3 4 0 (1),
      tm 3 2 3 4 1 (2),
      tm 2 2 3 4 2 (1),
      tm 7 3 2 1 0 (1),
      tm 6 3 2 2 0 (1),
      tm 5 3 2 2 1 (1),
      tm 5 3 3 2 0 (2),
      tm 4 3 3 2 1 (1),
      tm 4 3 3 3 0 (2),
      tm 3 3 3 3 1 (3),
      tm 2 3 3 3 2 (1),
      tm 3 3 4 3 0 (1),
      tm 2 3 4 3 1 (1),
      tm 2 3 4 4 0 (1),
      tm 1 3 4 4 1 (2),
      tm 0 3 4 4 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 244: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore244 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore244)) den one two three four
      = polyEval chartProduct244 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 245 (degree 5), denominators cleared. -/
def flatCore245 : FlatPoly :=
  [ftm 0 1 0 2 (1),
    ftm 0 1 0 3 (-1),
    ftm 0 1 1 1 (2),
    ftm 0 1 1 2 (-4),
    ftm 0 1 1 3 (2),
    ftm 0 1 2 1 (-1),
    ftm 0 1 2 2 (1),
    ftm 0 2 0 1 (2),
    ftm 0 2 0 2 (-2),
    ftm 0 2 1 0 (1),
    ftm 0 2 1 1 (-6),
    ftm 0 2 1 2 (4),
    ftm 0 2 2 0 (-1),
    ftm 0 2 2 1 (2),
    ftm 0 3 0 0 (1),
    ftm 0 3 0 1 (-1),
    ftm 0 3 1 0 (-2),
    ftm 0 3 1 1 (2),
    ftm 0 3 2 0 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 0 1 3 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-3),
    ftm 1 1 0 3 (2),
    ftm 1 1 1 1 (-2),
    ftm 1 1 1 2 (3),
    ftm 1 2 0 1 (-4),
    ftm 1 2 0 2 (4),
    ftm 1 2 1 0 (-1),
    ftm 1 2 1 1 (3),
    ftm 1 3 0 0 (-1),
    ftm 1 3 0 1 (2),
    ftm 1 3 1 0 (1),
    ftm 2 0 0 2 (-1),
    ftm 2 0 0 3 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 0 2 (2),
    ftm 2 2 0 1 (1)]

/-- The certificate-side product for flat core 245: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct245 : Poly :=
  polyMul ([tm 6 2 1 0 0 (1)])
    (chartCore185)

/-- KERNEL-CHECKED chart soundness for flat core 245: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore245 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore245)) den one two three four
      = polyEval chartProduct245 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 246 (degree 5), denominators cleared. -/
def flatCore246 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 1 1 (2),
    ftm 0 1 1 2 (-2),
    ftm 0 1 2 0 (1),
    ftm 0 1 2 1 (-4),
    ftm 0 1 2 2 (2),
    ftm 0 2 1 0 (1),
    ftm 0 2 1 1 (-3),
    ftm 0 2 2 0 (-2),
    ftm 0 2 2 1 (3),
    ftm 0 3 1 0 (-1),
    ftm 0 3 2 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-2),
    ftm 1 0 2 1 (-1),
    ftm 1 0 2 2 (2),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 1 1 1 (-6),
    ftm 1 1 1 2 (3),
    ftm 1 1 2 0 (-1),
    ftm 1 1 2 1 (3),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-2),
    ftm 1 2 1 1 (4),
    ftm 1 2 2 0 (1),
    ftm 1 3 1 0 (1),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 1 (-1),
    ftm 2 0 1 2 (3),
    ftm 2 1 0 1 (-2),
    ftm 2 1 0 2 (1),
    ftm 2 1 1 0 (-1),
    ftm 2 1 1 1 (4),
    ftm 2 2 0 1 (1),
    ftm 2 2 1 0 (1),
    ftm 3 0 0 2 (1),
    ftm 3 1 0 1 (1)]

/-- The certificate-side product for flat core 246: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct246 : Poly :=
  polyMul ([tm 6 2 0 0 0 (-1)])
    (chartCore186)

/-- KERNEL-CHECKED chart soundness for flat core 246: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore246 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore246)) den one two three four
      = polyEval chartProduct246 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 247 (degree 4), denominators cleared. -/
def flatCore247 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-4),
    ftm 0 1 1 2 (2),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-2),
    ftm 0 2 1 0 (-3),
    ftm 0 2 1 1 (4),
    ftm 0 3 0 0 (-1),
    ftm 0 3 1 0 (2),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (2),
    ftm 1 1 0 0 (2),
    ftm 1 1 0 1 (-6),
    ftm 1 1 0 2 (2),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (4),
    ftm 1 2 0 0 (-4),
    ftm 1 2 0 1 (4),
    ftm 1 2 1 0 (2),
    ftm 1 3 0 0 (2),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (2),
    ftm 2 1 0 0 (-2),
    ftm 2 1 0 1 (4),
    ftm 2 2 0 0 (2)]

/-- The certificate-side product for flat core 247: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct247 : Poly :=
  polyMul ([tm 3 0 0 0 0 (1)])
    (chartCore187)

/-- KERNEL-CHECKED chart soundness for flat core 247: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore247 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore247)) den one two three four
      = polyEval chartProduct247 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 248 (degree 5), denominators cleared. -/
def flatCore248 : FlatPoly :=
  [ftm 0 1 2 1 (1),
    ftm 0 1 2 2 (-1),
    ftm 0 2 2 1 (-1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (2),
    ftm 1 0 1 3 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 0 2 2 (-2),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (6),
    ftm 1 1 1 2 (-5),
    ftm 1 1 2 0 (1),
    ftm 1 1 2 1 (-3),
    ftm 1 2 1 0 (2),
    ftm 1 2 1 1 (-5),
    ftm 1 2 2 0 (-1),
    ftm 1 3 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 0 1 2 (-3),
    ftm 2 1 0 1 (1),
    ftm 2 1 0 2 (-1),
    ftm 2 1 1 0 (1),
    ftm 2 1 1 1 (-4),
    ftm 2 2 0 1 (-1),
    ftm 2 2 1 0 (-1),
    ftm 3 0 0 2 (-1),
    ftm 3 1 0 1 (-1)]

/-- The certificate-side product for flat core 248: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct248 : Poly :=
  polyMul ([tm 6 3 1 0 0 (-1)])
    (chartCore188)

/-- KERNEL-CHECKED chart soundness for flat core 248: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore248 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 5 flatCore248)) den one two three four
      = polyEval chartProduct248 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 249 (degree 3), denominators cleared. -/
def flatCore249 : FlatPoly :=
  [ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-3),
    ftm 0 1 1 1 (2),
    ftm 0 1 2 0 (1),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (2),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-3),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (3),
    ftm 1 2 0 0 (2),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (2)]

/-- The certificate-side product for flat core 249: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct249 : Poly :=
  polyMul ([tm 2 2 1 0 0 (1)])
    (chartCore189)

/-- KERNEL-CHECKED chart soundness for flat core 249: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore249 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore249)) den one two three four
      = polyEval chartProduct249 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 250 (degree 3), denominators cleared. -/
def flatCore250 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 1 (-2),
    ftm 1 1 0 0 (2),
    ftm 1 1 0 1 (-3),
    ftm 1 1 1 0 (-2),
    ftm 1 2 0 0 (-2),
    ftm 2 0 0 1 (-2),
    ftm 2 1 0 0 (-2)]

/-- The certificate-side product for flat core 250: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct250 : Poly :=
  polyMul ([tm 3 2 1 0 0 (-1)])
    (chartCore190)

/-- KERNEL-CHECKED chart soundness for flat core 250: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore250 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore250)) den one two three four
      = polyEval chartProduct250 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 251 (degree 4), denominators cleared. -/
def flatCore251 : FlatPoly :=
  [ftm 0 1 1 1 (2),
    ftm 0 1 1 2 (-2),
    ftm 0 1 2 1 (-1),
    ftm 0 2 1 0 (1),
    ftm 0 2 1 1 (-3),
    ftm 0 2 2 0 (-1),
    ftm 0 3 1 0 (-1),
    ftm 1 0 1 2 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 1 (-2),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-1),
    ftm 2 0 0 2 (-1),
    ftm 2 1 0 1 (-1)]

/-- The certificate-side product for flat core 251: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct251 : Poly :=
  polyMul ([tm 7 2 1 0 0 (-1)])
    (chartCore191)

/-- KERNEL-CHECKED chart soundness for flat core 251: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore251 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore251)) den one two three four
      = polyEval chartProduct251 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 252 (degree 3), denominators cleared. -/
def flatCore252 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-2),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (2),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 1 (-2),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (2),
    ftm 0 1 2 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (2),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (1)]

/-- The certificate-side product for flat core 252: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct252 : Poly :=
  polyMul ([tm 1 0 0 0 0 (-1)])
    (chartCore192)

/-- KERNEL-CHECKED chart soundness for flat core 252: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore252 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore252)) den one two three four
      = polyEval chartProduct252 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 253 (degree 4), denominators cleared. -/
def flatCore253 : FlatPoly :=
  [ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 0 3 (1),
    ftm 1 1 0 1 (-2),
    ftm 1 1 0 2 (3),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (1),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (2),
    ftm 1 2 1 0 (1)]

/-- The certificate-side product for flat core 253: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct253 : Poly :=
  polyMul ([tm 4 2 1 0 0 (1)])
    (chartCore193)

/-- KERNEL-CHECKED chart soundness for flat core 253: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore253 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore253)) den one two three four
      = polyEval chartProduct253 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 254 (degree 4), denominators cleared. -/
def flatCore254 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (2),
    ftm 1 1 2 0 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (1)]

/-- The certificate-side product for flat core 254: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct254 : Poly :=
  polyMul ([tm 4 1 0 0 0 (-1)])
    (chartCore194)

/-- KERNEL-CHECKED chart soundness for flat core 254: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore254 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore254)) den one two three four
      = polyEval chartProduct254 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 255 (degree 3), denominators cleared. -/
def flatCore255 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-3),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-3),
    ftm 1 1 0 1 (3),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (2),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 255: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct255 : Poly :=
  polyMul ([tm 1 0 0 0 0 (1)])
    ([tm 11 0 0 0 0 (1),
      tm 10 1 0 0 0 (1),
      tm 9 1 1 0 0 (2),
      tm 8 1 1 1 0 (1),
      tm 7 1 1 1 1 (2),
      tm 8 2 1 0 0 (2),
      tm 6 2 1 1 1 (1),
      tm 7 2 2 0 0 (1),
      tm 6 2 2 1 0 (2),
      tm 5 2 2 1 1 (3),
      tm 4 2 2 2 1 (1),
      tm 3 2 2 2 2 (1),
      tm 6 3 2 0 0 (1),
      tm 4 3 2 1 1 (1),
      tm 3 3 2 2 1 (1),
      tm 4 3 3 1 0 (1),
      tm 3 3 3 1 1 (1),
      tm 2 3 3 2 1 (1),
      tm 1 3 3 2 2 (1),
      tm 1 3 3 3 1 (1),
      tm 0 3 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 255: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore255 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore255)) den one two three four
      = polyEval chartProduct255 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 256 (degree 3), denominators cleared. -/
def flatCore256 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (2),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (3),
    ftm 0 1 2 0 (1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1)]

/-- The certificate-side product for flat core 256: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct256 : Poly :=
  polyMul ([tm 3 1 0 0 0 (1)])
    ([tm 8 0 0 0 0 (1),
      tm 6 0 1 1 0 (1),
      tm 6 1 1 0 0 (1),
      tm 4 1 2 1 0 (1),
      tm 3 2 1 1 1 (1),
      tm 1 2 2 2 1 (1),
      tm 0 2 2 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 256: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore256 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore256)) den one two three four
      = polyEval chartProduct256 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 257 (degree 3), denominators cleared. -/
def flatCore257 : FlatPoly :=
  [ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 2 (1),
    ftm 1 1 0 0 (-2),
    ftm 1 1 0 1 (3),
    ftm 1 1 1 0 (2),
    ftm 1 2 0 0 (2),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 257: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct257 : Poly :=
  polyMul ([tm 2 1 1 1 0 (1)])
    ([tm 7 0 0 0 0 (1),
      tm 5 1 1 0 0 (2),
      tm 4 1 1 0 1 (1),
      tm 3 2 2 0 0 (1),
      tm 2 2 2 0 1 (1),
      tm 0 2 2 1 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 257: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore257 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore257)) den one two three four
      = polyEval chartProduct257 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 258 (degree 3), denominators cleared. -/
def flatCore258 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 2 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-1)]

/-- The certificate-side product for flat core 258: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct258 : Poly :=
  polyMul ([tm 5 1 1 1 0 (-1)])
    (chartCore195)

/-- KERNEL-CHECKED chart soundness for flat core 258: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore258 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore258)) den one two three four
      = polyEval chartProduct258 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 259 (degree 4), denominators cleared. -/
def flatCore259 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 1 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-2),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 2 0 (1),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (1)]

/-- The certificate-side product for flat core 259: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct259 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    ([tm 13 0 0 0 0 (1),
      tm 11 1 1 0 0 (2),
      tm 10 1 1 1 0 (1),
      tm 9 1 1 1 1 (1),
      tm 8 1 2 2 0 (1),
      tm 7 1 2 2 1 (1),
      tm 9 2 1 1 0 (1),
      tm 9 2 2 0 0 (1),
      tm 8 2 2 1 0 (1),
      tm 7 2 2 1 1 (1),
      tm 7 2 2 2 0 (2),
      tm 6 2 2 2 1 (2),
      tm 6 2 3 2 0 (1),
      tm 5 2 3 2 1 (1),
      tm 5 2 3 3 0 (1),
      tm 4 2 3 3 1 (2),
      tm 3 2 3 3 2 (1),
      tm 7 3 2 1 0 (1),
      tm 6 3 2 2 0 (1),
      tm 5 3 2 2 1 (1),
      tm 5 3 3 2 0 (2),
      tm 4 3 3 2 1 (1),
      tm 4 3 3 3 0 (2),
      tm 3 3 3 3 1 (3),
      tm 2 3 3 3 2 (1),
      tm 3 3 4 3 0 (1),
      tm 2 3 4 3 1 (1),
      tm 2 3 4 4 0 (1),
      tm 1 3 4 4 1 (2),
      tm 0 3 4 4 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 259: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore259 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore259)) den one two three four
      = polyEval chartProduct259 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 260 (degree 4), denominators cleared. -/
def flatCore260 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 1 3 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 2 0 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (1),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (1)]

/-- The certificate-side product for flat core 260: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct260 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    ([tm 10 0 0 0 0 (1),
      tm 9 0 1 0 0 (1),
      tm 8 0 1 1 0 (1),
      tm 7 0 1 1 1 (1),
      tm 8 0 2 0 0 (1),
      tm 7 0 2 1 0 (1),
      tm 6 0 2 1 1 (1),
      tm 8 1 1 0 0 (2),
      tm 7 1 2 0 0 (2),
      tm 6 1 2 1 0 (2),
      tm 5 1 2 1 1 (3),
      tm 6 1 3 0 0 (2),
      tm 5 1 3 1 0 (2),
      tm 4 1 3 1 1 (3),
      tm 3 1 3 2 1 (1),
      tm 2 1 3 2 2 (1),
      tm 6 2 2 0 0 (1),
      tm 4 2 2 1 1 (1),
      tm 5 2 3 0 0 (1),
      tm 4 2 3 1 0 (1),
      tm 3 2 3 1 1 (2),
      tm 2 2 3 2 1 (1),
      tm 1 2 3 2 2 (1),
      tm 4 2 4 0 0 (1),
      tm 3 2 4 1 0 (1),
      tm 2 2 4 1 1 (2),
      tm 1 2 4 2 1 (1),
      tm 0 2 4 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 260: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore260 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore260)) den one two three four
      = polyEval chartProduct260 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 261 (degree 3), denominators cleared. -/
def flatCore261 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 0 (1),
    ftm 0 1 1 0 (-2),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-2),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 261: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct261 : Poly :=
  polyMul ([tm 1 0 0 0 0 (1)])
    ([tm 11 0 0 0 0 (1),
      tm 9 1 1 0 0 (2),
      tm 7 1 1 1 1 (1),
      tm 9 2 0 0 0 (1),
      tm 8 2 1 0 0 (1),
      tm 7 2 1 1 0 (2),
      tm 6 2 1 1 1 (1),
      tm 7 2 2 0 0 (1),
      tm 6 2 2 1 0 (1),
      tm 5 2 2 1 1 (2),
      tm 5 2 2 2 0 (1),
      tm 4 2 2 2 1 (1),
      tm 8 3 0 0 0 (1),
      tm 7 3 1 0 0 (1),
      tm 6 3 1 1 0 (2),
      tm 5 3 1 1 1 (2),
      tm 6 3 2 0 0 (1),
      tm 5 3 2 1 0 (2),
      tm 4 3 2 1 1 (2),
      tm 4 3 2 2 0 (1),
      tm 3 3 2 2 1 (3),
      tm 2 3 2 2 2 (1),
      tm 4 3 3 1 0 (1),
      tm 3 3 3 1 1 (1),
      tm 3 3 3 2 0 (1),
      tm 2 3 3 2 1 (2),
      tm 1 3 3 2 2 (1),
      tm 1 3 3 3 1 (1),
      tm 0 3 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 261: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore261 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore261)) den one two three four
      = polyEval chartProduct261 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 262 (degree 3), denominators cleared. -/
def flatCore262 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 1 (-1),
    ftm 0 2 0 0 (-1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-2),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 262: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct262 : Poly :=
  polyMul ([tm 1 0 0 0 0 (1)])
    ([tm 11 0 0 0 0 (1),
      tm 10 1 0 0 0 (1),
      tm 9 1 1 0 0 (2),
      tm 8 1 1 1 0 (1),
      tm 7 1 1 1 1 (2),
      tm 9 2 0 0 0 (1),
      tm 8 2 1 0 0 (2),
      tm 7 2 1 1 0 (2),
      tm 6 2 1 1 1 (2),
      tm 7 2 2 0 0 (1),
      tm 6 2 2 1 0 (2),
      tm 5 2 2 1 1 (3),
      tm 5 2 2 2 0 (1),
      tm 4 2 2 2 1 (2),
      tm 3 2 2 2 2 (1),
      tm 7 3 1 0 0 (1),
      tm 6 3 2 0 0 (1),
      tm 5 3 2 1 0 (2),
      tm 4 3 2 1 1 (2),
      tm 3 3 2 2 1 (1),
      tm 4 3 3 1 0 (1),
      tm 3 3 3 1 1 (1),
      tm 3 3 3 2 0 (1),
      tm 2 3 3 2 1 (2),
      tm 1 3 3 2 2 (1),
      tm 1 3 3 3 1 (1),
      tm 0 3 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 262: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore262 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore262)) den one two three four
      = polyEval chartProduct262 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 263 (degree 3), denominators cleared. -/
def flatCore263 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 1 1 1 (1),
    ftm 1 0 0 0 (-1),
    ftm 1 0 0 1 (2),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 1 0 0 (2),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-1),
    ftm 1 2 0 0 (-1),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 263: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct263 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    (chartCore196)

/-- KERNEL-CHECKED chart soundness for flat core 263: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore263 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore263)) den one two three four
      = polyEval chartProduct263 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 264 (degree 3), denominators cleared. -/
def flatCore264 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 1 0 0 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 1 0 (2),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 0 0 (1),
    ftm 1 1 0 0 (2),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-2),
    ftm 1 2 0 0 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 264: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct264 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore197)

/-- KERNEL-CHECKED chart soundness for flat core 264: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore264 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore264)) den one two three four
      = polyEval chartProduct264 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 265 (degree 2), denominators cleared. -/
def flatCore265 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 1 1 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 1 0 (-1),
    ftm 1 1 0 0 (-1),
    ftm 2 0 0 0 (-1)]

/-- The certificate-side product for flat core 265: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct265 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    ([tm 6 0 0 0 0 (1),
      tm 4 1 1 0 0 (1),
      tm 0 1 2 2 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 265: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore265 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore265)) den one two three four
      = polyEval chartProduct265 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 266 (degree 2), denominators cleared. -/
def flatCore266 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 1 0 0 (1),
    ftm 0 1 1 0 (-1),
    ftm 0 2 0 0 (-1),
    ftm 1 1 0 0 (-1)]

/-- The certificate-side product for flat core 266: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct266 : Poly :=
  polyMul ([tm 2 0 0 0 0 (1)])
    ([tm 6 0 0 0 0 (1),
      tm 4 1 1 0 0 (1),
      tm 0 2 2 1 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 266: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore266 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore266)) den one two three four
      = polyEval chartProduct266 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 267 (degree 3), denominators cleared. -/
def flatCore267 : FlatPoly :=
  [ftm 0 0 0 1 (2),
    ftm 0 0 0 2 (-2),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-4),
    ftm 0 0 1 2 (2),
    ftm 0 0 2 0 (-1),
    ftm 0 0 2 1 (2),
    ftm 0 1 0 1 (-2),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (2),
    ftm 0 1 2 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-4),
    ftm 1 0 0 2 (2),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (3),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 267: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct267 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    ([tm 10 0 0 0 0 (1),
      tm 8 0 1 1 0 (1),
      tm 7 0 1 1 1 (2),
      tm 9 1 0 0 0 (1),
      tm 8 1 1 0 0 (1),
      tm 7 1 1 1 0 (2),
      tm 6 1 1 1 1 (2),
      tm 6 1 2 1 0 (1),
      tm 5 1 2 1 1 (2),
      tm 5 1 2 2 0 (1),
      tm 4 1 2 2 1 (2),
      tm 3 1 2 2 2 (2),
      tm 7 2 1 0 0 (1),
      tm 6 2 1 1 0 (1),
      tm 5 2 1 1 1 (1),
      tm 5 2 2 1 0 (2),
      tm 4 2 2 1 1 (1),
      tm 4 2 2 2 0 (2),
      tm 3 2 2 2 1 (3),
      tm 2 2 2 2 2 (1),
      tm 3 2 3 2 0 (1),
      tm 2 2 3 2 1 (1),
      tm 2 2 3 3 0 (1),
      tm 1 2 3 3 1 (2),
      tm 0 2 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 267: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore267 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore267)) den one two three four
      = polyEval chartProduct267 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 268 (degree 4), denominators cleared. -/
def flatCore268 : FlatPoly :=
  [ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 0 3 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (-3),
    ftm 1 1 0 2 (3),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (2),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (2),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 268: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct268 : Poly :=
  polyMul ([tm 4 2 1 0 0 (1)])
    ([tm 9 0 0 0 0 (1),
      tm 8 0 1 0 0 (1),
      tm 7 0 1 1 0 (1),
      tm 6 0 1 1 1 (1),
      tm 8 1 0 0 0 (1),
      tm 7 1 1 0 0 (2),
      tm 6 1 1 1 0 (1),
      tm 5 1 1 1 1 (2),
      tm 4 1 1 2 1 (1),
      tm 6 1 2 0 0 (2),
      tm 5 1 2 1 0 (2),
      tm 4 1 2 1 1 (3),
      tm 3 1 2 2 1 (1),
      tm 2 1 2 2 2 (1),
      tm 2 1 2 3 1 (1),
      tm 1 1 2 3 2 (1),
      tm 6 2 1 0 0 (1),
      tm 4 2 1 1 1 (1),
      tm 5 2 2 0 0 (1),
      tm 4 2 2 1 0 (1),
      tm 3 2 2 1 1 (2),
      tm 2 2 2 2 1 (1),
      tm 1 2 2 2 2 (1),
      tm 4 2 3 0 0 (1),
      tm 3 2 3 1 0 (1),
      tm 2 2 3 1 1 (2),
      tm 1 2 3 2 1 (1),
      tm 0 2 3 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 268: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore268 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore268)) den one two three four
      = polyEval chartProduct268 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 269 (degree 4), denominators cleared. -/
def flatCore269 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-3),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (2),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (2),
    ftm 1 1 2 0 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (3),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (1),
    ftm 3 0 0 1 (1)]

/-- The certificate-side product for flat core 269: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct269 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    ([tm 5 0 2 2 1 (1),
      tm 9 1 0 0 0 (1),
      tm 8 1 1 0 0 (1),
      tm 7 1 1 1 0 (2),
      tm 6 1 1 1 1 (1),
      tm 6 1 2 1 0 (1),
      tm 5 1 2 1 1 (1),
      tm 5 1 2 2 0 (1),
      tm 4 1 2 2 1 (1),
      tm 3 1 3 2 1 (1),
      tm 1 1 3 3 2 (1),
      tm 8 2 0 0 0 (1),
      tm 7 2 1 0 0 (1),
      tm 6 2 1 1 0 (2),
      tm 5 2 1 1 1 (2),
      tm 6 2 2 0 0 (1),
      tm 5 2 2 1 0 (2),
      tm 4 2 2 1 1 (2),
      tm 4 2 2 2 0 (1),
      tm 3 2 2 2 1 (3),
      tm 2 2 2 2 2 (1),
      tm 4 2 3 1 0 (1),
      tm 3 2 3 1 1 (1),
      tm 3 2 3 2 0 (1),
      tm 2 2 3 2 1 (2),
      tm 1 2 3 2 2 (1),
      tm 1 2 3 3 1 (1),
      tm 0 2 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 269: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore269 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore269)) den one two three four
      = polyEval chartProduct269 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 270 (degree 3), denominators cleared. -/
def flatCore270 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 0 (2),
    ftm 1 0 0 1 (-4),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-2),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 0 (-4),
    ftm 1 1 0 1 (3),
    ftm 1 1 1 0 (2),
    ftm 1 2 0 0 (2),
    ftm 2 0 0 0 (-2),
    ftm 2 0 0 1 (2),
    ftm 2 1 0 0 (2)]

/-- The certificate-side product for flat core 270: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct270 : Poly :=
  polyMul ([tm 1 0 0 0 0 (1)])
    ([tm 11 0 0 0 0 (1),
      tm 10 1 0 0 0 (1),
      tm 9 1 1 0 0 (2),
      tm 8 1 1 1 0 (1),
      tm 7 1 1 1 1 (2),
      tm 8 2 1 0 0 (2),
      tm 7 2 1 1 0 (1),
      tm 6 2 1 1 1 (1),
      tm 7 2 2 0 0 (1),
      tm 6 2 2 1 0 (2),
      tm 5 2 2 1 1 (3),
      tm 5 2 2 2 0 (1),
      tm 4 2 2 2 1 (2),
      tm 3 2 2 2 2 (1),
      tm 6 3 2 0 0 (1),
      tm 5 3 2 1 0 (1),
      tm 4 3 2 1 1 (1),
      tm 3 3 2 2 1 (2),
      tm 4 3 3 1 0 (1),
      tm 3 3 3 1 1 (1),
      tm 3 3 3 2 0 (1),
      tm 2 3 3 2 1 (2),
      tm 1 3 3 2 2 (1),
      tm 1 3 3 3 1 (2),
      tm 0 3 3 3 2 (2)])

/-- KERNEL-CHECKED chart soundness for flat core 270: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore270 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore270)) den one two three four
      = polyEval chartProduct270 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 271 (degree 2), denominators cleared. -/
def flatCore271 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 1 1 0 (-1),
    ftm 1 0 0 1 (-1)]

/-- The certificate-side product for flat core 271: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct271 : Poly :=
  polyMul ([tm 3 1 0 0 0 (-1)])
    (chartCore198)

/-- KERNEL-CHECKED chart soundness for flat core 271: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore271 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore271)) den one two three four
      = polyEval chartProduct271 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 272 (degree 2), denominators cleared. -/
def flatCore272 : FlatPoly :=
  [ftm 0 1 0 0 (1),
    ftm 0 1 1 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 1 0 0 (-2)]

/-- The certificate-side product for flat core 272: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct272 : Poly :=
  polyMul ([tm 2 1 1 0 0 (1)])
    (chartCore199)

/-- KERNEL-CHECKED chart soundness for flat core 272: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore272 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore272)) den one two three four
      = polyEval chartProduct272 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 273 (degree 2), denominators cleared. -/
def flatCore273 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 1 0 0 1 (1)]

/-- The certificate-side product for flat core 273: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct273 : Poly :=
  polyMul ([tm 5 1 1 0 0 (1)])
    ([tm 0 0 0 1 0 (1),
      tm 0 1 0 0 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 273: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore273 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore273)) den one two three four
      = polyEval chartProduct273 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 274 (degree 4), denominators cleared. -/
def flatCore274 : FlatPoly :=
  [ftm 0 1 2 0 (1),
    ftm 0 1 3 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (2),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 0 (1),
    ftm 1 0 2 1 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (2),
    ftm 1 1 1 1 (-1),
    ftm 1 1 2 0 (-3),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (2),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 0 (1),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (-2)]

/-- The certificate-side product for flat core 274: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct274 : Poly :=
  polyMul ([tm 2 2 1 0 0 (-1)])
    (chartCore200)

/-- KERNEL-CHECKED chart soundness for flat core 274: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore274 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore274)) den one two three four
      = polyEval chartProduct274 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 275 (degree 3), denominators cleared. -/
def flatCore275 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 0 (-2),
    ftm 0 0 2 1 (2),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (2),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-2),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (2)]

/-- The certificate-side product for flat core 275: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct275 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore201)

/-- KERNEL-CHECKED chart soundness for flat core 275: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore275 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore275)) den one two three four
      = polyEval chartProduct275 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 276 (degree 3), denominators cleared. -/
def flatCore276 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-3),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-3),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (3),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (2)]

/-- The certificate-side product for flat core 276: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct276 : Poly :=
  polyMul ([tm 1 2 0 0 0 (1)])
    ([tm 9 0 0 0 0 (1),
      tm 7 0 1 1 0 (2),
      tm 6 0 1 1 1 (1),
      tm 5 0 2 1 1 (1),
      tm 5 0 2 2 0 (1),
      tm 4 0 2 2 1 (1),
      tm 8 1 0 0 0 (1),
      tm 7 1 1 0 0 (1),
      tm 6 1 1 1 0 (2),
      tm 5 1 1 1 1 (2),
      tm 5 1 2 1 0 (2),
      tm 4 1 2 1 1 (1),
      tm 4 1 2 2 0 (1),
      tm 3 1 2 2 1 (3),
      tm 2 1 2 2 2 (1),
      tm 3 1 3 1 1 (1),
      tm 3 1 3 2 0 (1),
      tm 2 1 3 2 1 (1),
      tm 1 1 3 2 2 (1),
      tm 1 1 3 3 1 (1),
      tm 0 1 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 276: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore276 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore276)) den one two three four
      = polyEval chartProduct276 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 277 (degree 4), denominators cleared. -/
def flatCore277 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (-2),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (2),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 277: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct277 : Poly :=
  polyMul ([tm 5 0 0 0 0 (1)])
    (chartCore202)

/-- KERNEL-CHECKED chart soundness for flat core 277: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore277 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore277)) den one two three four
      = polyEval chartProduct277 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 278 (degree 3), denominators cleared. -/
def flatCore278 : FlatPoly :=
  [ftm 0 1 2 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-2),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (3),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (2)]

/-- The certificate-side product for flat core 278: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct278 : Poly :=
  polyMul ([tm 1 3 1 0 0 (1)])
    ([tm 7 0 0 0 0 (1),
      tm 5 0 1 1 0 (2),
      tm 3 0 1 2 1 (1),
      tm 3 0 2 2 0 (1),
      tm 1 0 2 3 1 (1),
      tm 0 0 2 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 278: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore278 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore278)) den one two three four
      = polyEval chartProduct278 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 279 (degree 3), denominators cleared. -/
def flatCore279 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 1 (2),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (3),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 279: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct279 : Poly :=
  polyMul ([tm 4 1 0 0 0 (1)])
    ([tm 4 0 1 1 1 (1),
      tm 6 1 0 0 0 (1),
      tm 4 1 1 1 0 (1),
      tm 2 1 2 1 1 (1),
      tm 0 1 2 2 2 (1),
      tm 4 2 1 0 0 (1),
      tm 2 2 2 1 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 279: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore279 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore279)) den one two three four
      = polyEval chartProduct279 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 280 (degree 3), denominators cleared. -/
def flatCore280 : FlatPoly :=
  [ftm 0 1 2 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 280: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct280 : Poly :=
  polyMul ([tm 5 2 1 0 0 (-1)])
    (chartCore203)

/-- KERNEL-CHECKED chart soundness for flat core 280: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore280 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore280)) den one two three four
      = polyEval chartProduct280 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 281 (degree 4), denominators cleared. -/
def flatCore281 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 0 3 1 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (1),
    ftm 1 1 2 0 (1),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (1)]

/-- The certificate-side product for flat core 281: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct281 : Poly :=
  polyMul ([tm 2 2 0 0 0 (1)])
    ([tm 12 0 0 0 0 (1),
      tm 10 0 1 1 0 (2),
      tm 8 0 2 2 0 (1),
      tm 7 0 2 2 1 (1),
      tm 10 1 1 0 0 (1),
      tm 9 1 1 1 0 (1),
      tm 8 1 1 1 1 (1),
      tm 8 1 2 1 0 (2),
      tm 7 1 2 2 0 (2),
      tm 6 1 2 2 1 (3),
      tm 6 1 3 2 0 (1),
      tm 5 1 3 2 1 (1),
      tm 5 1 3 3 0 (1),
      tm 4 1 3 3 1 (2),
      tm 3 1 3 3 2 (1),
      tm 7 2 2 1 0 (1),
      tm 6 2 2 2 0 (1),
      tm 5 2 2 2 1 (1),
      tm 5 2 3 2 0 (2),
      tm 4 2 3 2 1 (1),
      tm 4 2 3 3 0 (2),
      tm 3 2 3 3 1 (3),
      tm 2 2 3 3 2 (1),
      tm 3 2 4 3 0 (1),
      tm 2 2 4 3 1 (1),
      tm 2 2 4 4 0 (1),
      tm 1 2 4 4 1 (2),
      tm 0 2 4 4 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 281: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore281 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore281)) den one two three four
      = polyEval chartProduct281 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 282 (degree 4), denominators cleared. -/
def flatCore282 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 0 0 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 1 1 (1),
    ftm 0 2 2 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (1)]

/-- The certificate-side product for flat core 282: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct282 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    ([tm 9 0 1 0 0 (1),
      tm 8 0 2 0 0 (1),
      tm 7 0 2 1 0 (1),
      tm 6 0 2 1 1 (1),
      tm 9 1 0 0 0 (1),
      tm 8 1 1 0 0 (1),
      tm 7 1 1 1 0 (2),
      tm 6 1 1 1 1 (1),
      tm 7 1 2 0 0 (2),
      tm 6 1 2 1 0 (1),
      tm 5 1 2 1 1 (2),
      tm 5 1 2 2 0 (1),
      tm 4 1 2 2 1 (1),
      tm 6 1 3 0 0 (2),
      tm 5 1 3 1 0 (2),
      tm 4 1 3 1 1 (3),
      tm 3 1 3 2 1 (1),
      tm 2 1 3 2 2 (1),
      tm 6 2 2 0 0 (1),
      tm 4 2 2 1 1 (1),
      tm 5 2 3 0 0 (1),
      tm 4 2 3 1 0 (1),
      tm 3 2 3 1 1 (2),
      tm 2 2 3 2 1 (1),
      tm 1 2 3 2 2 (1),
      tm 4 2 4 0 0 (1),
      tm 3 2 4 1 0 (1),
      tm 2 2 4 1 1 (2),
      tm 1 2 4 2 1 (1),
      tm 0 2 4 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 282: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore282 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore282)) den one two three four
      = polyEval chartProduct282 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 283 (degree 3), denominators cleared. -/
def flatCore283 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (1),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (-1),
    ftm 1 1 0 0 (-2),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 0 (-1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 283: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct283 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    ([tm 10 0 0 0 0 (1),
      tm 8 0 1 1 0 (1),
      tm 9 1 0 0 0 (1),
      tm 8 1 1 0 0 (2),
      tm 7 1 1 1 0 (2),
      tm 6 1 1 1 1 (2),
      tm 6 1 2 1 0 (2),
      tm 5 1 2 1 1 (1),
      tm 5 1 2 2 0 (1),
      tm 4 1 2 2 1 (2),
      tm 8 2 0 0 0 (1),
      tm 7 2 1 0 0 (1),
      tm 6 2 1 1 0 (2),
      tm 5 2 1 1 1 (2),
      tm 6 2 2 0 0 (1),
      tm 5 2 2 1 0 (2),
      tm 4 2 2 1 1 (2),
      tm 4 2 2 2 0 (1),
      tm 3 2 2 2 1 (3),
      tm 2 2 2 2 2 (1),
      tm 4 2 3 1 0 (1),
      tm 3 2 3 1 1 (1),
      tm 3 2 3 2 0 (1),
      tm 2 2 3 2 1 (2),
      tm 1 2 3 2 2 (1),
      tm 1 2 3 3 1 (1),
      tm 0 2 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 283: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore283 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore283)) den one two three four
      = polyEval chartProduct283 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 284 (degree 3), denominators cleared. -/
def flatCore284 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 0 0 (-1),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 1 0 0 (-2),
    ftm 1 1 0 1 (1),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 284: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct284 : Poly :=
  polyMul ([tm 1 0 0 0 0 (1)])
    ([tm 11 0 0 0 0 (1),
      tm 10 1 0 0 0 (1),
      tm 9 1 1 0 0 (2),
      tm 8 1 1 1 0 (1),
      tm 7 1 1 1 1 (2),
      tm 8 2 1 0 0 (2),
      tm 7 2 1 1 0 (1),
      tm 6 2 1 1 1 (1),
      tm 7 2 2 0 0 (1),
      tm 6 2 2 1 0 (2),
      tm 5 2 2 1 1 (3),
      tm 5 2 2 2 0 (1),
      tm 4 2 2 2 1 (2),
      tm 3 2 2 2 2 (1),
      tm 8 3 0 0 0 (1),
      tm 6 3 1 1 0 (2),
      tm 5 3 1 1 1 (1),
      tm 6 3 2 0 0 (1),
      tm 5 3 2 1 0 (1),
      tm 4 3 2 1 1 (1),
      tm 4 3 2 2 0 (1),
      tm 3 3 2 2 1 (2),
      tm 4 3 3 1 0 (1),
      tm 3 3 3 1 1 (1),
      tm 3 3 3 2 0 (1),
      tm 2 3 3 2 1 (2),
      tm 1 3 3 2 2 (1),
      tm 1 3 3 3 1 (1),
      tm 0 3 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 284: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore284 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore284)) den one two three four
      = polyEval chartProduct284 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 285 (degree 3), denominators cleared. -/
def flatCore285 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 1 0 0 0 (-1),
    ftm 1 0 0 1 (2),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (2),
    ftm 1 1 0 1 (-2),
    ftm 1 1 1 0 (-1),
    ftm 1 2 0 0 (-1),
    ftm 2 0 0 0 (1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 285: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct285 : Poly :=
  polyMul ([tm 1 2 0 0 0 (1)])
    (chartCore204)

/-- KERNEL-CHECKED chart soundness for flat core 285: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore285 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore285)) den one two three four
      = polyEval chartProduct285 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 286 (degree 3), denominators cleared. -/
def flatCore286 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 1 0 0 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 1 0 (2),
    ftm 0 1 1 1 (-1),
    ftm 0 2 0 0 (1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (2),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-1),
    ftm 1 2 0 0 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 286: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct286 : Poly :=
  polyMul ([tm 2 2 0 0 0 (1)])
    (chartCore205)

/-- KERNEL-CHECKED chart soundness for flat core 286: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore286 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore286)) den one two three four
      = polyEval chartProduct286 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 287 (degree 2), denominators cleared. -/
def flatCore287 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 1 0 0 (-1),
    ftm 2 0 0 0 (-1)]

/-- The certificate-side product for flat core 287: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct287 : Poly :=
  polyMul ([tm 1 2 0 0 0 (1)])
    ([tm 5 0 0 0 0 (1),
      tm 3 0 1 1 0 (1),
      tm 0 0 2 2 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 287: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore287 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore287)) den one two three four
      = polyEval chartProduct287 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 288 (degree 2), denominators cleared. -/
def flatCore288 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 2 0 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 1 0 0 (-1)]

/-- The certificate-side product for flat core 288: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct288 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    ([tm 5 0 0 0 0 (1),
      tm 3 0 1 1 0 (1),
      tm 0 1 2 1 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 288: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore288 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore288)) den one two three four
      = polyEval chartProduct288 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 289 (degree 4), denominators cleared. -/
def flatCore289 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (1),
    ftm 0 1 3 0 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-1),
    ftm 1 0 2 1 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-3),
    ftm 1 1 1 1 (2),
    ftm 1 1 2 0 (3),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (-1),
    ftm 2 0 1 1 (1),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (2)]

/-- The certificate-side product for flat core 289: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct289 : Poly :=
  polyMul ([tm 2 2 1 1 0 (1)])
    ([tm 10 0 0 0 0 (1),
      tm 8 0 1 1 0 (1),
      tm 7 0 1 1 1 (1),
      tm 9 1 0 0 0 (1),
      tm 8 1 1 0 0 (1),
      tm 7 1 1 0 1 (1),
      tm 7 1 1 1 0 (2),
      tm 6 1 1 1 1 (2),
      tm 6 1 2 1 0 (1),
      tm 5 1 2 1 1 (1),
      tm 5 1 2 2 0 (1),
      tm 4 1 2 2 1 (2),
      tm 3 1 2 2 2 (1),
      tm 7 2 1 0 0 (1),
      tm 6 2 1 1 0 (1),
      tm 5 2 1 1 1 (1),
      tm 5 2 2 0 1 (1),
      tm 5 2 2 1 0 (2),
      tm 4 2 2 1 1 (1),
      tm 3 2 2 1 2 (1),
      tm 4 2 2 2 0 (2),
      tm 3 2 2 2 1 (3),
      tm 2 2 2 2 2 (1),
      tm 3 2 3 2 0 (1),
      tm 2 2 3 2 1 (1),
      tm 2 2 3 3 0 (1),
      tm 1 2 3 3 1 (2),
      tm 0 2 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 289: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore289 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore289)) den one two three four
      = polyEval chartProduct289 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 290 (degree 3), denominators cleared. -/
def flatCore290 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 0 (2),
    ftm 0 0 1 1 (-4),
    ftm 0 0 1 2 (2),
    ftm 0 0 2 0 (-2),
    ftm 0 0 2 1 (2),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-4),
    ftm 0 1 1 1 (3),
    ftm 0 1 2 0 (2),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-2),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (2)]

/-- The certificate-side product for flat core 290: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct290 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    ([tm 9 0 0 0 0 (1),
      tm 8 0 1 0 0 (1),
      tm 7 0 1 1 0 (1),
      tm 6 0 1 1 1 (1),
      tm 8 1 0 0 0 (1),
      tm 7 1 1 0 0 (2),
      tm 6 1 1 1 0 (1),
      tm 5 1 1 1 1 (2),
      tm 6 1 2 0 0 (2),
      tm 5 1 2 1 0 (2),
      tm 4 1 2 1 1 (3),
      tm 3 1 2 2 1 (1),
      tm 2 1 2 2 2 (1),
      tm 6 2 1 0 0 (1),
      tm 4 2 1 1 1 (2),
      tm 5 2 2 0 0 (1),
      tm 4 2 2 1 0 (1),
      tm 3 2 2 1 1 (2),
      tm 2 2 2 2 1 (2),
      tm 1 2 2 2 2 (2),
      tm 4 2 3 0 0 (1),
      tm 3 2 3 1 0 (1),
      tm 2 2 3 1 1 (2),
      tm 1 2 3 2 1 (1),
      tm 0 2 3 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 290: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore290 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore290)) den one two three four
      = polyEval chartProduct290 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 291 (degree 3), denominators cleared. -/
def flatCore291 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 1 0 0 (2),
    ftm 0 1 0 1 (-2),
    ftm 0 1 1 0 (-4),
    ftm 0 1 1 1 (2),
    ftm 0 1 2 0 (1),
    ftm 0 2 0 0 (-2),
    ftm 0 2 1 0 (2),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (-4),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (3),
    ftm 1 2 0 0 (2),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (2)]

/-- The certificate-side product for flat core 291: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct291 : Poly :=
  polyMul ([tm 1 2 0 0 0 (1)])
    ([tm 9 0 0 0 0 (1),
      tm 8 0 1 0 0 (1),
      tm 7 0 1 1 0 (2),
      tm 6 0 1 1 1 (1),
      tm 6 0 2 1 0 (1),
      tm 5 0 2 1 1 (2),
      tm 5 0 2 2 0 (1),
      tm 4 0 2 2 1 (1),
      tm 8 1 0 0 0 (1),
      tm 7 1 1 0 0 (1),
      tm 6 1 1 1 0 (2),
      tm 5 1 1 1 1 (2),
      tm 6 1 2 0 0 (1),
      tm 5 1 2 1 0 (2),
      tm 4 1 2 1 1 (2),
      tm 4 1 2 2 0 (1),
      tm 3 1 2 2 1 (3),
      tm 2 1 2 2 2 (1),
      tm 4 1 3 1 0 (1),
      tm 3 1 3 1 1 (2),
      tm 3 1 3 2 0 (1),
      tm 2 1 3 2 1 (2),
      tm 1 1 3 2 2 (2),
      tm 1 1 3 3 1 (1),
      tm 0 1 3 3 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 291: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore291 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore291)) den one two three four
      = polyEval chartProduct291 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 292 (degree 4), denominators cleared. -/
def flatCore292 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 1 (1),
    ftm 0 1 0 2 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-3),
    ftm 0 1 1 2 (2),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 1 (-1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 1 1 (3),
    ftm 0 2 2 0 (1),
    ftm 0 3 1 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (-2),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (2),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 292: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct292 : Poly :=
  polyMul ([tm 5 0 0 0 0 (1)])
    ([tm 11 0 0 0 0 (1),
      tm 10 1 0 0 0 (1),
      tm 9 1 1 0 0 (2),
      tm 8 1 1 1 0 (1),
      tm 7 1 1 1 1 (2),
      tm 8 2 1 0 0 (2),
      tm 7 2 1 1 0 (1),
      tm 6 2 1 1 1 (1),
      tm 7 2 2 0 0 (1),
      tm 6 2 2 1 0 (2),
      tm 5 2 2 1 1 (3),
      tm 5 2 2 2 0 (1),
      tm 4 2 2 2 1 (2),
      tm 3 2 2 2 2 (1),
      tm 6 3 2 0 0 (1),
      tm 5 3 2 1 0 (1),
      tm 4 3 2 1 1 (1),
      tm 3 3 2 2 1 (1),
      tm 4 3 3 1 0 (1),
      tm 3 3 3 1 1 (1),
      tm 3 3 3 2 0 (1),
      tm 2 3 3 2 1 (2),
      tm 1 3 3 2 2 (1),
      tm 1 3 3 3 1 (1),
      tm 0 3 3 3 2 (1),
      tm 3 4 2 1 1 (1),
      tm 1 4 3 2 1 (1),
      tm 0 4 3 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 292: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore292 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore292)) den one two three four
      = polyEval chartProduct292 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 293 (degree 2), denominators cleared. -/
def flatCore293 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 1 0 0 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 1 0 0 (2)]

/-- The certificate-side product for flat core 293: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct293 : Poly :=
  polyMul ([tm 1 2 1 0 0 (1)])
    (chartCore206)

/-- KERNEL-CHECKED chart soundness for flat core 293: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore293 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore293)) den one two three four
      = polyEval chartProduct293 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 294 (degree 2), denominators cleared. -/
def flatCore294 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 1 1 (-2),
    ftm 0 1 1 0 (-1),
    ftm 1 0 0 1 (-1)]

/-- The certificate-side product for flat core 294: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct294 : Poly :=
  polyMul ([tm 4 0 0 0 0 (1)])
    (chartCore207)

/-- KERNEL-CHECKED chart soundness for flat core 294: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore294 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore294)) den one two three four
      = polyEval chartProduct294 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 295 (degree 4), denominators cleared. -/
def flatCore295 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 1 (-2),
    ftm 0 0 2 2 (1),
    ftm 0 0 3 1 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 1 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 0 2 0 (1),
    ftm 1 0 2 1 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (1),
    ftm 1 1 2 0 (-1),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (2),
    ftm 2 0 0 2 (-1),
    ftm 2 0 1 0 (1),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (-1)]

/-- The certificate-side product for flat core 295: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct295 : Poly :=
  polyMul ([tm 2 2 1 1 0 (-1)])
    (chartCore208)

/-- KERNEL-CHECKED chart soundness for flat core 295: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore295 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore295)) den one two three four
      = polyEval chartProduct295 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 296 (degree 4), denominators cleared. -/
def flatCore296 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-2),
    ftm 0 0 1 3 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 0 2 2 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 0 2 (1),
    ftm 0 1 1 0 (-1),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 0 (1),
    ftm 0 2 0 0 (-1),
    ftm 0 2 0 1 (1),
    ftm 0 2 1 0 (2),
    ftm 0 2 2 0 (-1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (1),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-1)]

/-- The certificate-side product for flat core 296: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct296 : Poly :=
  polyMul ([tm 4 2 1 0 0 (-1)])
    (chartCore209)

/-- KERNEL-CHECKED chart soundness for flat core 296: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore296 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore296)) den one two three four
      = polyEval chartProduct296 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 297 (degree 3), denominators cleared. -/
def flatCore297 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 0 (-1),
    ftm 0 0 1 1 (-1),
    ftm 0 0 1 2 (1),
    ftm 0 0 2 1 (1),
    ftm 0 1 0 0 (-1),
    ftm 0 1 1 0 (2),
    ftm 0 2 0 0 (1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (1),
    ftm 1 0 1 1 (1),
    ftm 1 1 0 0 (2),
    ftm 1 1 1 0 (-1),
    ftm 1 2 0 0 (-1),
    ftm 2 0 0 0 (1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 297: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct297 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    (chartCore210)

/-- KERNEL-CHECKED chart soundness for flat core 297: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore297 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore297)) den one two three four
      = polyEval chartProduct297 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 298 (degree 3), denominators cleared. -/
def flatCore298 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 1 0 (-1),
    ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 0 0 (1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-1),
    ftm 0 2 0 0 (-1),
    ftm 1 0 0 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 1 0 0 (-2),
    ftm 1 1 0 1 (1),
    ftm 1 2 0 0 (1),
    ftm 2 0 0 0 (-1),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 298: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct298 : Poly :=
  polyMul ([tm 1 0 0 0 0 (1)])
    (chartCore211)

/-- KERNEL-CHECKED chart soundness for flat core 298: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore298 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore298)) den one two three four
      = polyEval chartProduct298 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 299 (degree 2), denominators cleared. -/
def flatCore299 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 1 0 0 0 (1),
    ftm 1 1 0 0 (-1)]

/-- The certificate-side product for flat core 299: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct299 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    ([tm 6 0 0 0 0 (1),
      tm 4 0 1 1 0 (1),
      tm 3 1 1 1 0 (1),
      tm 1 1 2 2 0 (1),
      tm 0 1 2 2 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 299: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore299 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore299)) den one two three four
      = polyEval chartProduct299 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 300 (degree 2), denominators cleared. -/
def flatCore300 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 1 0 0 (1),
    ftm 1 1 0 0 (-1)]

/-- The certificate-side product for flat core 300: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct300 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    ([tm 5 0 0 0 0 (1),
      tm 4 0 1 0 0 (1),
      tm 3 1 1 0 0 (1),
      tm 2 1 2 0 0 (1),
      tm 0 1 2 1 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 300: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore300 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore300)) den one two three four
      = polyEval chartProduct300 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 301 (degree 4), denominators cleared. -/
def flatCore301 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 1 (-2),
    ftm 0 0 2 2 (1),
    ftm 0 0 3 1 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 1 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (2),
    ftm 1 0 1 0 (-2),
    ftm 1 0 1 1 (2),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 0 (2),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 2 0 (-1),
    ftm 1 2 0 0 (-1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 0 (-2),
    ftm 2 0 0 1 (4),
    ftm 2 0 0 2 (-2),
    ftm 2 0 1 0 (2),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 1 (-1),
    ftm 2 2 0 0 (1),
    ftm 3 1 0 0 (1)]

/-- The certificate-side product for flat core 301: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct301 : Poly :=
  polyMul ([tm 2 2 1 1 0 (-1)])
    (chartCore212)

/-- KERNEL-CHECKED chart soundness for flat core 301: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore301 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore301)) den one two three four
      = polyEval chartProduct301 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 302 (degree 4), denominators cleared. -/
def flatCore302 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-2),
    ftm 0 0 1 3 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 0 2 2 (1),
    ftm 0 1 0 1 (-2),
    ftm 0 1 0 2 (2),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (2),
    ftm 0 1 2 0 (2),
    ftm 0 1 2 1 (-1),
    ftm 0 2 0 0 (-2),
    ftm 0 2 0 1 (2),
    ftm 0 2 1 0 (4),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 0 (-2),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 2 1 0 (-1),
    ftm 1 3 0 0 (1),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (1),
    ftm 2 2 0 0 (1)]

/-- The certificate-side product for flat core 302: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct302 : Poly :=
  polyMul ([tm 3 2 1 0 0 (-1)])
    (chartCore213)

/-- KERNEL-CHECKED chart soundness for flat core 302: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore302 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore302)) den one two three four
      = polyEval chartProduct302 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 303 (degree 4), denominators cleared. -/
def flatCore303 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 0 (-2),
    ftm 0 0 2 2 (1),
    ftm 0 0 3 1 (1),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (4),
    ftm 0 1 2 1 (-1),
    ftm 0 2 1 0 (2),
    ftm 0 2 2 0 (-2),
    ftm 1 0 1 0 (-2),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (2),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (2),
    ftm 1 1 2 0 (-1),
    ftm 1 2 0 0 (-1),
    ftm 1 2 1 0 (-1),
    ftm 2 0 1 0 (2),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 0 (-2),
    ftm 2 1 0 1 (1),
    ftm 2 2 0 0 (1),
    ftm 3 1 0 0 (1)]

/-- The certificate-side product for flat core 303: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct303 : Poly :=
  polyMul ([tm 3 2 0 0 0 (1)])
    (chartCore214)

/-- KERNEL-CHECKED chart soundness for flat core 303: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore303 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore303)) den one two three four
      = polyEval chartProduct303 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 304 (degree 4), denominators cleared. -/
def flatCore304 : FlatPoly :=
  [ftm 0 0 0 2 (2),
    ftm 0 0 1 1 (-1),
    ftm 0 0 1 3 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-2),
    ftm 0 1 2 1 (-1),
    ftm 0 2 0 1 (-2),
    ftm 0 2 1 1 (1),
    ftm 1 0 0 1 (2),
    ftm 1 0 0 2 (-4),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (-2),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (2),
    ftm 1 2 1 0 (-1),
    ftm 1 3 0 0 (-1),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (2),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (1),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 304: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct304 : Poly :=
  polyMul ([tm 3 0 0 0 0 (1)])
    (chartCore215)

/-- KERNEL-CHECKED chart soundness for flat core 304: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore304 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore304)) den one two three four
      = polyEval chartProduct304 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 305 (degree 3), denominators cleared. -/
def flatCore305 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 1 0 1 0 (2),
    ftm 1 0 1 1 (-1),
    ftm 1 1 1 0 (-1),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 305: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct305 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    ([tm 6 0 0 0 0 (1),
      tm 4 0 1 1 0 (1),
      tm 3 1 1 1 0 (2),
      tm 2 1 2 1 0 (1),
      tm 1 1 2 2 0 (2),
      tm 0 1 2 2 1 (2),
      tm 0 1 3 2 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 305: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore305 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore305)) den one two three four
      = polyEval chartProduct305 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 306 (degree 3), denominators cleared. -/
def flatCore306 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 1 0 1 (2),
    ftm 0 1 1 1 (-1),
    ftm 1 1 0 1 (-1),
    ftm 1 2 0 0 (1)]

/-- The certificate-side product for flat core 306: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct306 : Poly :=
  polyMul ([tm 5 1 0 0 0 (1)])
    ([tm 6 0 0 0 0 (1),
      tm 5 0 1 0 0 (2),
      tm 4 1 1 0 0 (1),
      tm 3 1 2 0 0 (2),
      tm 2 1 2 1 0 (1),
      tm 1 1 2 1 1 (2),
      tm 0 2 3 1 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 306: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore306 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore306)) den one two three four
      = polyEval chartProduct306 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 307 (degree 2), denominators cleared. -/
def flatCore307 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 1 0 0 (1)]

/-- The certificate-side product for flat core 307: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct307 : Poly :=
  polyMul ([tm 3 1 0 0 0 (1)])
    (chartCore216)

/-- KERNEL-CHECKED chart soundness for flat core 307: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore307 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore307)) den one two three four
      = polyEval chartProduct307 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 308 (degree 2), denominators cleared. -/
def flatCore308 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 1 1 0 (-2),
    ftm 1 1 0 0 (1)]

/-- The certificate-side product for flat core 308: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct308 : Poly :=
  polyMul ([tm 3 1 0 0 0 (1)])
    (chartCore217)

/-- KERNEL-CHECKED chart soundness for flat core 308: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore308 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore308)) den one two three four
      = polyEval chartProduct308 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 309 (degree 2), denominators cleared. -/
def flatCore309 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (1),
    ftm 0 1 0 0 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 2 0 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 1 0 0 (1)]

/-- The certificate-side product for flat core 309: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct309 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore218)

/-- KERNEL-CHECKED chart soundness for flat core 309: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore309 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore309)) den one two three four
      = polyEval chartProduct309 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 310 (degree 2), denominators cleared. -/
def flatCore310 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (1),
    ftm 0 0 2 0 (-1),
    ftm 0 1 1 0 (1),
    ftm 1 0 0 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 1 0 0 (1),
    ftm 2 0 0 0 (1)]

/-- The certificate-side product for flat core 310: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct310 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    (chartCore219)

/-- KERNEL-CHECKED chart soundness for flat core 310: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore310 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore310)) den one two three four
      = polyEval chartProduct310 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 311 (degree 2), denominators cleared. -/
def flatCore311 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-1),
    ftm 0 1 0 0 (-1),
    ftm 0 1 1 0 (-1),
    ftm 0 2 0 0 (1),
    ftm 1 0 0 1 (-1),
    ftm 1 1 0 0 (-1)]

/-- The certificate-side product for flat core 311: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct311 : Poly :=
  polyMul ([tm 2 1 1 0 0 (1)])
    (chartCore220)

/-- KERNEL-CHECKED chart soundness for flat core 311: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore311 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore311)) den one two three four
      = polyEval chartProduct311 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 312 (degree 2), denominators cleared. -/
def flatCore312 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 0 2 0 (-1),
    ftm 0 1 1 0 (-1),
    ftm 1 0 0 0 (-1),
    ftm 1 0 0 1 (-1),
    ftm 1 1 0 0 (-1),
    ftm 2 0 0 0 (1)]

/-- The certificate-side product for flat core 312: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct312 : Poly :=
  polyMul ([tm 1 1 1 1 0 (-1)])
    (chartCore221)

/-- KERNEL-CHECKED chart soundness for flat core 312: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore312 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore312)) den one two three four
      = polyEval chartProduct312 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 313 (degree 4), denominators cleared. -/
def flatCore313 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (1),
    ftm 0 1 3 0 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (3),
    ftm 1 0 0 2 (-3),
    ftm 1 0 1 0 (2),
    ftm 1 0 1 1 (-6),
    ftm 1 0 1 2 (3),
    ftm 1 0 2 0 (-2),
    ftm 1 0 2 1 (3),
    ftm 1 1 0 1 (-3),
    ftm 1 1 1 0 (-4),
    ftm 1 1 1 1 (4),
    ftm 1 1 2 0 (4),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 0 (2),
    ftm 2 0 0 1 (-6),
    ftm 2 0 0 2 (3),
    ftm 2 0 1 0 (-2),
    ftm 2 0 1 1 (4),
    ftm 2 1 0 0 (-2),
    ftm 2 1 0 1 (3),
    ftm 2 1 1 0 (3),
    ftm 3 0 0 1 (1)]

/-- The certificate-side product for flat core 313: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct313 : Poly :=
  polyMul ([tm 2 2 1 1 0 (1)])
    ([tm 10 0 0 0 0 (2),
      tm 8 0 1 1 0 (2),
      tm 7 0 1 1 1 (3),
      tm 9 1 0 0 0 (2),
      tm 8 1 1 0 0 (2),
      tm 7 1 1 0 1 (1),
      tm 7 1 1 1 0 (4),
      tm 6 1 1 1 1 (4),
      tm 6 1 2 1 0 (2),
      tm 5 1 2 1 1 (3),
      tm 5 1 2 2 0 (2),
      tm 4 1 2 2 1 (4),
      tm 3 1 2 2 2 (3),
      tm 7 2 1 0 0 (2),
      tm 6 2 1 1 0 (2),
      tm 5 2 1 1 1 (2),
      tm 5 2 2 0 1 (1),
      tm 5 2 2 1 0 (4),
      tm 4 2 2 1 1 (2),
      tm 3 2 2 1 2 (1),
      tm 4 2 2 2 0 (4),
      tm 3 2 2 2 1 (6),
      tm 2 2 2 2 2 (2),
      tm 3 2 3 2 0 (2),
      tm 2 2 3 2 1 (2),
      tm 2 2 3 3 0 (2),
      tm 1 2 3 3 1 (4),
      tm 0 2 3 3 2 (2)])

/-- KERNEL-CHECKED chart soundness for flat core 313: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore313 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore313)) den one two three four
      = polyEval chartProduct313 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 314 (degree 4), denominators cleared. -/
def flatCore314 : FlatPoly :=
  [ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-2),
    ftm 0 1 1 0 (3),
    ftm 0 1 1 1 (-6),
    ftm 0 1 1 2 (3),
    ftm 0 1 2 0 (-3),
    ftm 0 1 2 1 (3),
    ftm 0 2 0 0 (2),
    ftm 0 2 0 1 (-2),
    ftm 0 2 1 0 (-6),
    ftm 0 2 1 1 (4),
    ftm 0 2 2 0 (3),
    ftm 0 3 1 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 0 3 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (-4),
    ftm 1 1 0 2 (4),
    ftm 1 1 1 0 (-3),
    ftm 1 1 1 1 (4),
    ftm 1 2 0 0 (-2),
    ftm 1 2 0 1 (3),
    ftm 1 2 1 0 (3),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 314: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct314 : Poly :=
  polyMul ([tm 4 2 1 0 0 (1)])
    ([tm 9 0 0 0 0 (2),
      tm 8 0 1 0 0 (2),
      tm 7 0 1 1 0 (2),
      tm 6 0 1 1 1 (2),
      tm 8 1 0 0 0 (2),
      tm 7 1 1 0 0 (4),
      tm 6 1 1 1 0 (2),
      tm 5 1 1 1 1 (4),
      tm 4 1 1 2 1 (1),
      tm 6 1 2 0 0 (4),
      tm 5 1 2 1 0 (4),
      tm 4 1 2 1 1 (6),
      tm 3 1 2 2 1 (2),
      tm 2 1 2 2 2 (2),
      tm 2 1 2 3 1 (1),
      tm 1 1 2 3 2 (1),
      tm 6 2 1 0 0 (2),
      tm 4 2 1 1 1 (3),
      tm 5 2 2 0 0 (2),
      tm 4 2 2 1 0 (2),
      tm 3 2 2 1 1 (4),
      tm 2 2 2 2 1 (3),
      tm 1 2 2 2 2 (3),
      tm 4 2 3 0 0 (2),
      tm 3 2 3 1 0 (2),
      tm 2 2 3 1 1 (4),
      tm 1 2 3 2 1 (2),
      tm 0 2 3 2 2 (2)])

/-- KERNEL-CHECKED chart soundness for flat core 314: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore314 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore314)) den one two three four
      = polyEval chartProduct314 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 315 (degree 4), denominators cleared. -/
def flatCore315 : FlatPoly :=
  [ftm 0 0 2 0 (2),
    ftm 0 0 2 1 (-2),
    ftm 0 1 1 0 (3),
    ftm 0 1 1 1 (-3),
    ftm 0 1 2 0 (-6),
    ftm 0 1 2 1 (3),
    ftm 0 1 3 0 (1),
    ftm 0 2 1 0 (-3),
    ftm 0 2 2 0 (3),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (2),
    ftm 1 0 1 1 (-4),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-2),
    ftm 1 0 2 1 (3),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-6),
    ftm 1 1 1 1 (4),
    ftm 1 1 2 0 (4),
    ftm 1 2 1 0 (3),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (-2),
    ftm 2 0 1 1 (4),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (3),
    ftm 3 0 0 1 (1)]

/-- The certificate-side product for flat core 315: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct315 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    ([tm 5 0 2 2 1 (1),
      tm 9 1 0 0 0 (2),
      tm 8 1 1 0 0 (2),
      tm 7 1 1 1 0 (4),
      tm 6 1 1 1 1 (2),
      tm 6 1 2 1 0 (2),
      tm 5 1 2 1 1 (3),
      tm 5 1 2 2 0 (2),
      tm 4 1 2 2 1 (2),
      tm 3 1 3 2 1 (1),
      tm 1 1 3 3 2 (1),
      tm 8 2 0 0 0 (2),
      tm 7 2 1 0 0 (2),
      tm 6 2 1 1 0 (4),
      tm 5 2 1 1 1 (4),
      tm 6 2 2 0 0 (2),
      tm 5 2 2 1 0 (4),
      tm 4 2 2 1 1 (4),
      tm 4 2 2 2 0 (2),
      tm 3 2 2 2 1 (6),
      tm 2 2 2 2 2 (2),
      tm 4 2 3 1 0 (2),
      tm 3 2 3 1 1 (3),
      tm 3 2 3 2 0 (2),
      tm 2 2 3 2 1 (4),
      tm 1 2 3 2 2 (3),
      tm 1 2 3 3 1 (2),
      tm 0 2 3 3 2 (2)])

/-- KERNEL-CHECKED chart soundness for flat core 315: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore315 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore315)) den one two three four
      = polyEval chartProduct315 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 316 (degree 4), denominators cleared. -/
def flatCore316 : FlatPoly :=
  [ftm 0 0 0 2 (2),
    ftm 0 0 1 2 (-2),
    ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-2),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-4),
    ftm 0 1 1 2 (3),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 1 (-2),
    ftm 0 2 1 0 (-2),
    ftm 0 2 1 1 (4),
    ftm 0 2 2 0 (1),
    ftm 0 3 1 0 (1),
    ftm 1 0 0 1 (3),
    ftm 1 0 0 2 (-6),
    ftm 1 0 0 3 (1),
    ftm 1 0 1 1 (-3),
    ftm 1 0 1 2 (3),
    ftm 1 1 0 1 (-6),
    ftm 1 1 0 2 (4),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (4),
    ftm 1 2 0 1 (3),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (-3),
    ftm 2 0 0 2 (3),
    ftm 2 1 0 1 (3)]

/-- The certificate-side product for flat core 316: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct316 : Poly :=
  polyMul ([tm 5 0 0 0 0 (1)])
    ([tm 11 0 0 0 0 (2),
      tm 10 1 0 0 0 (2),
      tm 9 1 1 0 0 (4),
      tm 8 1 1 1 0 (2),
      tm 7 1 1 1 1 (4),
      tm 8 2 1 0 0 (4),
      tm 7 2 1 1 0 (2),
      tm 6 2 1 1 1 (2),
      tm 7 2 2 0 0 (2),
      tm 6 2 2 1 0 (4),
      tm 5 2 2 1 1 (6),
      tm 5 2 2 2 0 (2),
      tm 4 2 2 2 1 (4),
      tm 3 2 2 2 2 (2),
      tm 6 3 2 0 0 (2),
      tm 5 3 2 1 0 (2),
      tm 4 3 2 1 1 (2),
      tm 3 3 2 2 1 (3),
      tm 4 3 3 1 0 (2),
      tm 3 3 3 1 1 (2),
      tm 3 3 3 2 0 (2),
      tm 2 3 3 2 1 (4),
      tm 1 3 3 2 2 (2),
      tm 1 3 3 3 1 (3),
      tm 0 3 3 3 2 (3),
      tm 3 4 2 1 1 (1),
      tm 1 4 3 2 1 (1),
      tm 0 4 3 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 316: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore316 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore316)) den one two three four
      = polyEval chartProduct316 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 317 (degree 3), denominators cleared. -/
def flatCore317 : FlatPoly :=
  [ftm 0 1 2 0 (1),
    ftm 1 0 1 0 (-2),
    ftm 1 0 1 1 (3),
    ftm 1 1 1 0 (3),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 317: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct317 : Poly :=
  polyMul ([tm 4 2 1 0 0 (1)])
    (chartCore222)

/-- KERNEL-CHECKED chart soundness for flat core 317: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore317 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore317)) den one two three four
      = polyEval chartProduct317 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 318 (degree 3), denominators cleared. -/
def flatCore318 : FlatPoly :=
  [ftm 0 1 0 1 (2),
    ftm 0 1 1 1 (-3),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 2 (-1),
    ftm 1 1 0 1 (-3)]

/-- The certificate-side product for flat core 318: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct318 : Poly :=
  polyMul ([tm 6 1 1 0 0 (1)])
    (chartCore223)

/-- KERNEL-CHECKED chart soundness for flat core 318: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore318 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore318)) den one two three four
      = polyEval chartProduct318 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 319 (degree 2), denominators cleared. -/
def flatCore319 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 1 0 0 1 (3)]

/-- The certificate-side product for flat core 319: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct319 : Poly :=
  polyMul ([tm 5 1 1 0 0 (1)])
    ([tm 0 0 0 1 0 (3),
      tm 0 1 0 0 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 319: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore319 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore319)) den one two three four
      = polyEval chartProduct319 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 320 (degree 2), denominators cleared. -/
def flatCore320 : FlatPoly :=
  [ftm 0 1 1 0 (3),
    ftm 1 0 0 1 (1)]

/-- The certificate-side product for flat core 320: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct320 : Poly :=
  polyMul ([tm 5 1 1 0 0 (1)])
    ([tm 0 0 0 1 0 (1),
      tm 0 1 0 0 0 (3)])

/-- KERNEL-CHECKED chart soundness for flat core 320: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore320 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore320)) den one two three four
      = polyEval chartProduct320 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 321 (degree 4), denominators cleared. -/
def flatCore321 : FlatPoly :=
  [ftm 0 1 2 0 (1),
    ftm 0 1 3 0 (-1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (2),
    ftm 1 0 1 0 (-2),
    ftm 1 0 1 1 (4),
    ftm 1 0 1 2 (-2),
    ftm 1 0 2 0 (2),
    ftm 1 0 2 1 (-2),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (2),
    ftm 1 1 1 1 (-2),
    ftm 1 1 2 0 (-3),
    ftm 2 0 0 0 (-2),
    ftm 2 0 0 1 (4),
    ftm 2 0 0 2 (-2),
    ftm 2 0 1 0 (2),
    ftm 2 0 1 1 (-2),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (-2),
    ftm 2 1 1 0 (-1),
    ftm 3 1 0 0 (1)]

/-- The certificate-side product for flat core 321: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct321 : Poly :=
  polyMul ([tm 2 2 1 0 0 (-1)])
    (chartCore224)

/-- KERNEL-CHECKED chart soundness for flat core 321: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore321 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore321)) den one two three four
      = polyEval chartProduct321 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 322 (degree 3), denominators cleared. -/
def flatCore322 : FlatPoly :=
  [ftm 0 0 0 1 (2),
    ftm 0 0 0 2 (-2),
    ftm 0 0 1 0 (2),
    ftm 0 0 1 1 (-4),
    ftm 0 0 1 2 (2),
    ftm 0 0 2 0 (-3),
    ftm 0 0 2 1 (3),
    ftm 0 1 0 0 (2),
    ftm 0 1 0 1 (-2),
    ftm 0 1 1 0 (-4),
    ftm 0 1 1 1 (2),
    ftm 0 1 2 0 (3),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (2),
    ftm 1 0 1 0 (-2),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 0 (-2),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (2),
    ftm 2 0 0 0 (1),
    ftm 2 0 0 1 (-1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 322: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct322 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore225)

/-- KERNEL-CHECKED chart soundness for flat core 322: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore322 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore322)) den one two three four
      = polyEval chartProduct322 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 323 (degree 4), denominators cleared. -/
def flatCore323 : FlatPoly :=
  [ftm 0 0 2 0 (2),
    ftm 0 0 2 1 (-2),
    ftm 0 1 1 0 (2),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-5),
    ftm 0 1 2 1 (2),
    ftm 0 1 3 0 (1),
    ftm 0 2 1 0 (-2),
    ftm 0 2 2 0 (2),
    ftm 1 0 1 0 (2),
    ftm 1 0 1 1 (-2),
    ftm 1 0 2 0 (-2),
    ftm 1 0 2 1 (2),
    ftm 1 1 1 0 (-4),
    ftm 1 1 1 1 (2),
    ftm 1 1 2 0 (3),
    ftm 1 2 1 0 (2),
    ftm 2 0 1 0 (-2),
    ftm 2 0 1 1 (2),
    ftm 2 1 0 0 (1),
    ftm 2 1 1 0 (1),
    ftm 3 1 0 0 (-1)]

/-- The certificate-side product for flat core 323: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct323 : Poly :=
  polyMul ([tm 4 3 0 0 0 (1)])
    ([tm 9 0 0 0 0 (2),
      tm 8 0 1 0 0 (1),
      tm 7 0 1 1 0 (4),
      tm 6 0 1 1 1 (2),
      tm 6 0 2 1 0 (2),
      tm 5 0 2 1 1 (2),
      tm 5 0 2 2 0 (2),
      tm 4 0 2 2 1 (2),
      tm 4 0 3 2 0 (1),
      tm 8 1 0 0 0 (2),
      tm 7 1 1 0 0 (2),
      tm 6 1 1 1 0 (4),
      tm 5 1 1 1 1 (4),
      tm 6 1 2 0 0 (1),
      tm 5 1 2 1 0 (4),
      tm 4 1 2 1 1 (3),
      tm 4 1 2 2 0 (2),
      tm 3 1 2 2 1 (6),
      tm 2 1 2 2 2 (2),
      tm 4 1 3 1 0 (2),
      tm 3 1 3 1 1 (2),
      tm 3 1 3 2 0 (2),
      tm 2 1 3 2 1 (4),
      tm 1 1 3 2 2 (2),
      tm 1 1 3 3 1 (2),
      tm 0 1 3 3 2 (2),
      tm 2 1 4 2 0 (1),
      tm 0 1 4 3 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 323: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore323 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore323)) den one two three four
      = polyEval chartProduct323 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 324 (degree 4), denominators cleared. -/
def flatCore324 : FlatPoly :=
  [ftm 0 0 0 2 (2),
    ftm 0 0 1 2 (-2),
    ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-2),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (2),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 1 (-2),
    ftm 0 2 1 1 (2),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (2),
    ftm 1 0 0 2 (-4),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (2),
    ftm 1 1 0 1 (-4),
    ftm 1 1 0 2 (2),
    ftm 1 1 1 1 (2),
    ftm 1 2 0 1 (2),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (2),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (1),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 324: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct324 : Poly :=
  polyMul ([tm 4 0 0 0 0 (1)])
    (chartCore226)

/-- KERNEL-CHECKED chart soundness for flat core 324: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore324 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore324)) den one two three four
      = polyEval chartProduct324 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 325 (degree 4), denominators cleared. -/
def flatCore325 : FlatPoly :=
  [ftm 0 1 3 0 (1),
    ftm 1 0 1 0 (2),
    ftm 1 0 1 1 (-4),
    ftm 1 0 1 2 (2),
    ftm 1 0 2 0 (-2),
    ftm 1 0 2 1 (2),
    ftm 1 1 1 0 (-4),
    ftm 1 1 1 1 (4),
    ftm 1 1 2 0 (3),
    ftm 1 2 1 0 (2),
    ftm 2 0 1 0 (-2),
    ftm 2 0 1 1 (2),
    ftm 2 1 1 0 (1),
    ftm 3 1 0 0 (-1)]

/-- The certificate-side product for flat core 325: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct325 : Poly :=
  polyMul ([tm 4 4 1 0 0 (1)])
    (chartCore227)

/-- KERNEL-CHECKED chart soundness for flat core 325: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore325 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore325)) den one two three four
      = polyEval chartProduct325 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 326 (degree 3), denominators cleared. -/
def flatCore326 : FlatPoly :=
  [ftm 0 0 0 1 (2),
    ftm 0 0 0 2 (-2),
    ftm 0 0 1 1 (-4),
    ftm 0 0 1 2 (2),
    ftm 0 0 2 1 (3),
    ftm 0 1 0 1 (-2),
    ftm 0 1 1 1 (2),
    ftm 0 1 2 0 (1),
    ftm 1 0 0 1 (-4),
    ftm 1 0 0 2 (2),
    ftm 1 0 1 1 (4),
    ftm 1 1 0 1 (2),
    ftm 2 0 0 1 (1),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 326: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct326 : Poly :=
  polyMul ([tm 4 1 0 0 0 (1)])
    (chartCore228)

/-- KERNEL-CHECKED chart soundness for flat core 326: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore326 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore326)) den one two three four
      = polyEval chartProduct326 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 327 (degree 3), denominators cleared. -/
def flatCore327 : FlatPoly :=
  [ftm 0 1 2 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (2),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 1 (2),
    ftm 2 0 0 1 (2),
    ftm 2 1 0 0 (-1)]

/-- The certificate-side product for flat core 327: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct327 : Poly :=
  polyMul ([tm 4 2 1 0 0 (-1)])
    (chartCore229)

/-- KERNEL-CHECKED chart soundness for flat core 327: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore327 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore327)) den one two three four
      = polyEval chartProduct327 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 328 (degree 2), denominators cleared. -/
def flatCore328 : FlatPoly :=
  [ftm 0 0 1 0 (2),
    ftm 0 0 1 1 (-2),
    ftm 0 0 2 0 (-3),
    ftm 0 1 1 0 (-2),
    ftm 1 0 1 0 (-2),
    ftm 2 0 0 0 (1)]

/-- The certificate-side product for flat core 328: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct328 : Poly :=
  polyMul ([tm 2 2 0 0 0 (-1)])
    (chartCore230)

/-- KERNEL-CHECKED chart soundness for flat core 328: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore328 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore328)) den one two three four
      = polyEval chartProduct328 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 329 (degree 4), denominators cleared. -/
def flatCore329 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 0 3 1 (-1),
    ftm 1 0 0 1 (2),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 0 (2),
    ftm 1 0 1 1 (-4),
    ftm 1 0 1 2 (2),
    ftm 1 0 2 0 (-2),
    ftm 1 0 2 1 (1),
    ftm 1 1 0 1 (-2),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (2),
    ftm 1 1 2 0 (2),
    ftm 2 0 0 0 (2),
    ftm 2 0 0 1 (-5),
    ftm 2 0 0 2 (2),
    ftm 2 0 1 0 (-2),
    ftm 2 0 1 1 (3),
    ftm 2 1 0 0 (-2),
    ftm 2 1 0 1 (2),
    ftm 2 1 1 0 (2),
    ftm 3 0 0 1 (1)]

/-- The certificate-side product for flat core 329: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct329 : Poly :=
  polyMul ([tm 2 2 0 0 0 (1)])
    ([tm 12 0 0 0 0 (1),
      tm 10 0 1 1 0 (2),
      tm 8 0 2 2 0 (1),
      tm 7 0 2 2 1 (2),
      tm 10 1 1 0 0 (1),
      tm 9 1 1 1 0 (2),
      tm 8 1 1 1 1 (1),
      tm 8 1 2 1 0 (2),
      tm 7 1 2 2 0 (4),
      tm 6 1 2 2 1 (4),
      tm 6 1 3 2 0 (1),
      tm 5 1 3 2 1 (2),
      tm 5 1 3 3 0 (2),
      tm 4 1 3 3 1 (3),
      tm 3 1 3 3 2 (2),
      tm 7 2 2 1 0 (2),
      tm 6 2 2 2 0 (2),
      tm 5 2 2 2 1 (2),
      tm 5 2 3 2 0 (4),
      tm 4 2 3 2 1 (2),
      tm 4 2 3 3 0 (4),
      tm 3 2 3 3 1 (6),
      tm 2 2 3 3 2 (2),
      tm 3 2 4 3 0 (2),
      tm 2 2 4 3 1 (2),
      tm 2 2 4 4 0 (2),
      tm 1 2 4 4 1 (4),
      tm 0 2 4 4 2 (2)])

/-- KERNEL-CHECKED chart soundness for flat core 329: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore329 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore329)) den one two three four
      = polyEval chartProduct329 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 330 (degree 4), denominators cleared. -/
def flatCore330 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-2),
    ftm 0 1 1 0 (2),
    ftm 0 1 1 1 (-4),
    ftm 0 1 1 2 (2),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 0 (2),
    ftm 0 2 0 1 (-2),
    ftm 0 2 1 0 (-4),
    ftm 0 2 1 1 (2),
    ftm 0 2 2 0 (2),
    ftm 1 1 0 1 (-2),
    ftm 1 1 0 2 (2),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (2),
    ftm 1 2 0 0 (-2),
    ftm 1 2 0 1 (2),
    ftm 1 2 1 0 (2),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 330: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct330 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    (chartCore231)

/-- KERNEL-CHECKED chart soundness for flat core 330: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore330 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore330)) den one two three four
      = polyEval chartProduct330 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 331 (degree 4), denominators cleared. -/
def flatCore331 : FlatPoly :=
  [ftm 0 0 2 0 (2),
    ftm 0 0 2 1 (-1),
    ftm 0 0 3 1 (-1),
    ftm 0 1 1 0 (2),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-4),
    ftm 0 1 2 1 (2),
    ftm 0 2 1 0 (-2),
    ftm 0 2 2 0 (2),
    ftm 1 0 1 0 (2),
    ftm 1 0 1 1 (-2),
    ftm 1 0 2 0 (-2),
    ftm 1 0 2 1 (1),
    ftm 1 1 1 0 (-4),
    ftm 1 1 1 1 (2),
    ftm 1 1 2 0 (2),
    ftm 1 2 1 0 (2),
    ftm 2 0 0 1 (-1),
    ftm 2 0 1 0 (-2),
    ftm 2 0 1 1 (3),
    ftm 2 1 1 0 (2),
    ftm 3 0 0 1 (1)]

/-- The certificate-side product for flat core 331: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct331 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    (chartCore232)

/-- KERNEL-CHECKED chart soundness for flat core 331: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore331 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore331)) den one two three four
      = polyEval chartProduct331 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 332 (degree 3), denominators cleared. -/
def flatCore332 : FlatPoly :=
  [ftm 0 0 0 1 (2),
    ftm 0 0 1 1 (-2),
    ftm 0 0 2 0 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 1 0 0 (2),
    ftm 0 1 0 1 (-2),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (2),
    ftm 0 1 2 0 (-1),
    ftm 0 2 0 0 (-2),
    ftm 0 2 1 0 (2),
    ftm 1 0 0 0 (2),
    ftm 1 0 0 1 (-4),
    ftm 1 0 1 0 (-2),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 0 (-4),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (2),
    ftm 1 2 0 0 (2),
    ftm 2 0 0 0 (-3),
    ftm 2 0 0 1 (3),
    ftm 2 1 0 0 (3)]

/-- The certificate-side product for flat core 332: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct332 : Poly :=
  polyMul ([tm 1 0 0 0 0 (1)])
    (chartCore233)

/-- KERNEL-CHECKED chart soundness for flat core 332: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore332 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore332)) den one two three four
      = polyEval chartProduct332 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 333 (degree 4), denominators cleared. -/
def flatCore333 : FlatPoly :=
  [ftm 0 0 3 1 (1),
    ftm 1 0 1 0 (-2),
    ftm 1 0 1 1 (4),
    ftm 1 0 1 2 (-2),
    ftm 1 0 2 0 (2),
    ftm 1 0 2 1 (-1),
    ftm 1 1 1 0 (4),
    ftm 1 1 1 1 (-4),
    ftm 1 1 2 0 (-2),
    ftm 1 2 1 0 (-2),
    ftm 2 0 1 0 (2),
    ftm 2 0 1 1 (-3),
    ftm 2 1 1 0 (-2),
    ftm 3 0 0 1 (-1)]

/-- The certificate-side product for flat core 333: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct333 : Poly :=
  polyMul ([tm 4 3 0 0 0 (1)])
    (chartCore234)

/-- KERNEL-CHECKED chart soundness for flat core 333: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore333 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore333)) den one two three four
      = polyEval chartProduct333 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 334 (degree 3), denominators cleared. -/
def flatCore334 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 1 0 0 (-2),
    ftm 0 1 0 1 (2),
    ftm 0 1 1 0 (4),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-1),
    ftm 0 2 0 0 (2),
    ftm 0 2 1 0 (-2),
    ftm 1 1 0 0 (4),
    ftm 1 1 0 1 (-2),
    ftm 1 1 1 0 (-4),
    ftm 1 2 0 0 (-2),
    ftm 2 0 0 1 (-1),
    ftm 2 1 0 0 (-3)]

/-- The certificate-side product for flat core 334: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct334 : Poly :=
  polyMul ([tm 2 2 0 0 0 (1)])
    (chartCore235)

/-- KERNEL-CHECKED chart soundness for flat core 334: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore334 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore334)) den one two three four
      = polyEval chartProduct334 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 335 (degree 2), denominators cleared. -/
def flatCore335 : FlatPoly :=
  [ftm 0 0 2 0 (1),
    ftm 1 0 0 0 (2),
    ftm 1 0 0 1 (-2),
    ftm 1 0 1 0 (-2),
    ftm 1 1 0 0 (-2),
    ftm 2 0 0 0 (-3)]

/-- The certificate-side product for flat core 335: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct335 : Poly :=
  polyMul ([tm 1 2 0 0 0 (1)])
    (chartCore236)

/-- KERNEL-CHECKED chart soundness for flat core 335: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore335 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore335)) den one two three four
      = polyEval chartProduct335 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 336 (degree 3), denominators cleared. -/
def flatCore336 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 0 1 1 0 (2),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-2),
    ftm 0 2 1 0 (-2),
    ftm 1 1 1 0 (-2),
    ftm 2 0 0 1 (-1)]

/-- The certificate-side product for flat core 336: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct336 : Poly :=
  polyMul ([tm 5 2 0 0 0 (1)])
    (chartCore237)

/-- KERNEL-CHECKED chart soundness for flat core 336: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore336 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore336)) den one two three four
      = polyEval chartProduct336 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 337 (degree 3), denominators cleared. -/
def flatCore337 : FlatPoly :=
  [ftm 0 0 0 1 (2),
    ftm 0 0 0 2 (-3),
    ftm 0 0 1 0 (2),
    ftm 0 0 1 1 (-4),
    ftm 0 0 1 2 (3),
    ftm 0 0 2 0 (-2),
    ftm 0 0 2 1 (2),
    ftm 0 1 0 1 (-2),
    ftm 0 1 1 0 (-2),
    ftm 0 1 1 1 (2),
    ftm 0 1 2 0 (2),
    ftm 0 2 0 0 (1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 0 (2),
    ftm 1 0 0 1 (-4),
    ftm 1 0 0 2 (3),
    ftm 1 0 1 0 (-2),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 0 (-2),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (2),
    ftm 1 2 0 0 (-1)]

/-- The certificate-side product for flat core 337: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct337 : Poly :=
  polyMul ([tm 1 0 0 0 0 (-1)])
    (chartCore238)

/-- KERNEL-CHECKED chart soundness for flat core 337: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore337 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore337)) den one two three four
      = polyEval chartProduct337 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 338 (degree 4), denominators cleared. -/
def flatCore338 : FlatPoly :=
  [ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-2),
    ftm 0 1 1 0 (2),
    ftm 0 1 1 1 (-4),
    ftm 0 1 1 2 (2),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (2),
    ftm 0 2 0 0 (2),
    ftm 0 2 0 1 (-2),
    ftm 0 2 1 0 (-4),
    ftm 0 2 1 1 (2),
    ftm 0 2 2 0 (2),
    ftm 1 0 0 2 (-1),
    ftm 1 0 0 3 (1),
    ftm 1 1 0 1 (-2),
    ftm 1 1 0 2 (3),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (2),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (2),
    ftm 1 3 0 0 (-1)]

/-- The certificate-side product for flat core 338: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct338 : Poly :=
  polyMul ([tm 4 2 1 0 0 (1)])
    (chartCore239)

/-- KERNEL-CHECKED chart soundness for flat core 338: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore338 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore338)) den one two three four
      = polyEval chartProduct338 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 339 (degree 4), denominators cleared. -/
def flatCore339 : FlatPoly :=
  [ftm 0 0 2 0 (2),
    ftm 0 0 2 1 (-2),
    ftm 0 1 1 0 (2),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-4),
    ftm 0 1 2 1 (2),
    ftm 0 2 1 0 (-2),
    ftm 0 2 2 0 (2),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (2),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-2),
    ftm 1 0 2 1 (2),
    ftm 1 1 1 0 (-4),
    ftm 1 1 1 1 (2),
    ftm 1 1 2 0 (2),
    ftm 1 2 0 0 (1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (-2),
    ftm 2 0 1 1 (2),
    ftm 2 1 1 0 (2),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 339: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct339 : Poly :=
  polyMul ([tm 4 1 0 0 0 (-1)])
    (chartCore240)

/-- KERNEL-CHECKED chart soundness for flat core 339: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore339 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore339)) den one two three four
      = polyEval chartProduct339 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 340 (degree 4), denominators cleared. -/
def flatCore340 : FlatPoly :=
  [ftm 0 0 0 2 (2),
    ftm 0 0 1 2 (-2),
    ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-2),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (2),
    ftm 0 2 0 1 (-2),
    ftm 0 2 1 1 (2),
    ftm 1 0 0 1 (2),
    ftm 1 0 0 2 (-5),
    ftm 1 0 0 3 (1),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (2),
    ftm 1 1 0 1 (-4),
    ftm 1 1 0 2 (3),
    ftm 1 1 1 1 (2),
    ftm 1 2 0 0 (1),
    ftm 1 2 0 1 (1),
    ftm 1 3 0 0 (-1),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (2),
    ftm 2 1 0 1 (2)]

/-- The certificate-side product for flat core 340: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct340 : Poly :=
  polyMul ([tm 5 0 0 0 0 (1)])
    ([tm 11 0 0 0 0 (2),
      tm 10 1 0 0 0 (2),
      tm 9 1 1 0 0 (4),
      tm 8 1 1 1 0 (2),
      tm 7 1 1 1 1 (4),
      tm 8 2 1 0 0 (4),
      tm 7 2 1 1 0 (1),
      tm 6 2 1 1 1 (2),
      tm 7 2 2 0 0 (2),
      tm 6 2 2 1 0 (4),
      tm 5 2 2 1 1 (6),
      tm 5 2 2 2 0 (1),
      tm 4 2 2 2 1 (3),
      tm 3 2 2 2 2 (2),
      tm 6 3 2 0 0 (2),
      tm 5 3 2 1 0 (2),
      tm 4 3 2 1 1 (2),
      tm 3 3 2 2 1 (2),
      tm 4 3 3 1 0 (2),
      tm 3 3 3 1 1 (2),
      tm 3 3 3 2 0 (2),
      tm 2 3 3 2 1 (4),
      tm 1 3 3 2 2 (2),
      tm 1 3 3 3 1 (2),
      tm 0 3 3 3 2 (2),
      tm 3 4 3 1 0 (1),
      tm 1 4 4 2 0 (1),
      tm 0 4 4 2 1 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 340: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore340 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore340)) den one two three four
      = polyEval chartProduct340 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 341 (degree 3), denominators cleared. -/
def flatCore341 : FlatPoly :=
  [ftm 0 0 1 0 (2),
    ftm 0 0 1 1 (-4),
    ftm 0 0 1 2 (3),
    ftm 0 0 2 0 (-2),
    ftm 0 0 2 1 (2),
    ftm 0 1 1 0 (-4),
    ftm 0 1 1 1 (4),
    ftm 0 1 2 0 (2),
    ftm 0 2 1 0 (1),
    ftm 1 0 0 2 (1),
    ftm 1 0 1 0 (-2),
    ftm 1 0 1 1 (2),
    ftm 1 1 1 0 (2),
    ftm 1 2 0 0 (-1)]

/-- The certificate-side product for flat core 341: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct341 : Poly :=
  polyMul ([tm 3 1 0 0 0 (1)])
    (chartCore241)

/-- KERNEL-CHECKED chart soundness for flat core 341: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore341 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore341)) den one two three four
      = polyEval chartProduct341 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 342 (degree 4), denominators cleared. -/
def flatCore342 : FlatPoly :=
  [ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-2),
    ftm 0 1 1 1 (-4),
    ftm 0 1 1 2 (2),
    ftm 0 1 2 1 (2),
    ftm 0 2 0 1 (-2),
    ftm 0 2 1 1 (2),
    ftm 1 0 0 3 (1),
    ftm 1 1 0 1 (-4),
    ftm 1 1 0 2 (3),
    ftm 1 1 1 1 (4),
    ftm 1 2 0 1 (1),
    ftm 1 3 0 0 (-1),
    ftm 2 1 0 1 (2)]

/-- The certificate-side product for flat core 342: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct342 : Poly :=
  polyMul ([tm 6 1 1 1 0 (1)])
    (chartCore242)

/-- KERNEL-CHECKED chart soundness for flat core 342: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore342 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore342)) den one two three four
      = polyEval chartProduct342 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 343 (degree 2), denominators cleared. -/
def flatCore343 : FlatPoly :=
  [ftm 0 0 0 1 (2),
    ftm 0 0 0 2 (-3),
    ftm 0 0 1 1 (-2),
    ftm 0 1 0 1 (-2),
    ftm 0 2 0 0 (1),
    ftm 1 0 0 1 (-2)]

/-- The certificate-side product for flat core 343: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct343 : Poly :=
  polyMul ([tm 4 0 0 0 0 (-1)])
    (chartCore243)

/-- KERNEL-CHECKED chart soundness for flat core 343: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore343 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore343)) den one two three four
      = polyEval chartProduct343 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 344 (degree 3), denominators cleared. -/
def flatCore344 : FlatPoly :=
  [ftm 0 1 1 0 (2),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-2),
    ftm 0 2 1 0 (-2),
    ftm 1 0 0 2 (-1),
    ftm 1 1 1 0 (-2),
    ftm 1 2 0 0 (1)]

/-- The certificate-side product for flat core 344: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct344 : Poly :=
  polyMul ([tm 5 1 1 1 0 (-1)])
    (chartCore244)

/-- KERNEL-CHECKED chart soundness for flat core 344: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore344 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore344)) den one two three four
      = polyEval chartProduct344 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 345 (degree 4), denominators cleared. -/
def flatCore345 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (2),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 0 (2),
    ftm 1 0 1 1 (-4),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-2),
    ftm 1 0 2 1 (2),
    ftm 1 1 0 1 (-2),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (2),
    ftm 1 1 2 0 (2),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 0 (2),
    ftm 2 0 0 1 (-4),
    ftm 2 0 0 2 (2),
    ftm 2 0 1 0 (-2),
    ftm 2 0 1 1 (2),
    ftm 2 1 0 0 (-2),
    ftm 2 1 0 1 (2),
    ftm 2 1 1 0 (2)]

/-- The certificate-side product for flat core 345: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct345 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore245)

/-- KERNEL-CHECKED chart soundness for flat core 345: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore345 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore345)) den one two three four
      = polyEval chartProduct345 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 346 (degree 4), denominators cleared. -/
def flatCore346 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 0 1 3 (-1),
    ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-2),
    ftm 0 1 1 0 (2),
    ftm 0 1 1 1 (-4),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (2),
    ftm 0 2 0 0 (2),
    ftm 0 2 0 1 (-2),
    ftm 0 2 1 0 (-5),
    ftm 0 2 1 1 (3),
    ftm 0 2 2 0 (2),
    ftm 0 3 1 0 (1),
    ftm 1 1 0 1 (-2),
    ftm 1 1 0 2 (2),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (2),
    ftm 1 2 0 0 (-2),
    ftm 1 2 0 1 (2),
    ftm 1 2 1 0 (2)]

/-- The certificate-side product for flat core 346: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct346 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    ([tm 10 0 0 0 0 (1),
      tm 9 0 1 0 0 (2),
      tm 8 0 1 1 0 (1),
      tm 7 0 1 1 1 (1),
      tm 8 0 2 0 0 (2),
      tm 7 0 2 1 0 (2),
      tm 6 0 2 1 1 (2),
      tm 8 1 1 0 0 (2),
      tm 7 1 2 0 0 (4),
      tm 6 1 2 1 0 (2),
      tm 5 1 2 1 1 (4),
      tm 6 1 3 0 0 (4),
      tm 5 1 3 1 0 (4),
      tm 4 1 3 1 1 (6),
      tm 3 1 3 2 1 (2),
      tm 2 1 3 2 2 (2),
      tm 6 2 2 0 0 (1),
      tm 4 2 2 1 1 (2),
      tm 5 2 3 0 0 (2),
      tm 4 2 3 1 0 (1),
      tm 3 2 3 1 1 (3),
      tm 2 2 3 2 1 (2),
      tm 1 2 3 2 2 (2),
      tm 4 2 4 0 0 (2),
      tm 3 2 4 1 0 (2),
      tm 2 2 4 1 1 (4),
      tm 1 2 4 2 1 (2),
      tm 0 2 4 2 2 (2)])

/-- KERNEL-CHECKED chart soundness for flat core 346: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore346 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore346)) den one two three four
      = polyEval chartProduct346 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 347 (degree 3), denominators cleared. -/
def flatCore347 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 0 1 0 (2),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (-1),
    ftm 0 1 0 0 (2),
    ftm 0 1 0 1 (-2),
    ftm 0 1 1 0 (-4),
    ftm 0 1 1 1 (2),
    ftm 0 2 0 0 (-3),
    ftm 0 2 1 0 (3),
    ftm 1 0 0 0 (2),
    ftm 1 0 0 1 (-2),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (-2),
    ftm 1 0 1 1 (2),
    ftm 1 1 0 0 (-4),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (2),
    ftm 1 2 0 0 (3),
    ftm 2 0 0 0 (-2),
    ftm 2 0 0 1 (2),
    ftm 2 1 0 0 (2)]

/-- The certificate-side product for flat core 347: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct347 : Poly :=
  polyMul ([tm 1 0 0 0 0 (1)])
    (chartCore246)

/-- KERNEL-CHECKED chart soundness for flat core 347: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore347 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore347)) den one two three four
      = polyEval chartProduct347 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 348 (degree 4), denominators cleared. -/
def flatCore348 : FlatPoly :=
  [ftm 0 0 0 2 (2),
    ftm 0 0 1 2 (-1),
    ftm 0 0 1 3 (-1),
    ftm 0 1 0 1 (2),
    ftm 0 1 0 2 (-2),
    ftm 0 1 1 1 (-2),
    ftm 0 1 1 2 (1),
    ftm 0 2 0 1 (-2),
    ftm 0 2 1 0 (-1),
    ftm 0 2 1 1 (3),
    ftm 0 3 1 0 (1),
    ftm 1 0 0 1 (2),
    ftm 1 0 0 2 (-4),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (2),
    ftm 1 1 0 1 (-4),
    ftm 1 1 0 2 (2),
    ftm 1 1 1 1 (2),
    ftm 1 2 0 1 (2),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (2),
    ftm 2 1 0 1 (2)]

/-- The certificate-side product for flat core 348: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct348 : Poly :=
  polyMul ([tm 5 0 0 0 0 (1)])
    (chartCore247)

/-- KERNEL-CHECKED chart soundness for flat core 348: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore348 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore348)) den one two three four
      = polyEval chartProduct348 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 349 (degree 3), denominators cleared. -/
def flatCore349 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 0 (-2),
    ftm 1 0 0 1 (4),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (2),
    ftm 1 0 1 1 (-2),
    ftm 1 1 0 0 (4),
    ftm 1 1 0 1 (-4),
    ftm 1 1 1 0 (-2),
    ftm 1 2 0 0 (-3),
    ftm 2 0 0 0 (2),
    ftm 2 0 0 1 (-2),
    ftm 2 1 0 0 (-2)]

/-- The certificate-side product for flat core 349: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct349 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    (chartCore248)

/-- KERNEL-CHECKED chart soundness for flat core 349: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore349 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore349)) den one two three four
      = polyEval chartProduct349 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 350 (degree 4), denominators cleared. -/
def flatCore350 : FlatPoly :=
  [ftm 0 0 1 3 (1),
    ftm 0 1 0 1 (-2),
    ftm 0 1 0 2 (2),
    ftm 0 1 1 1 (4),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 1 (-2),
    ftm 0 2 0 1 (2),
    ftm 0 2 1 1 (-3),
    ftm 0 3 1 0 (-1),
    ftm 1 1 0 1 (4),
    ftm 1 1 0 2 (-2),
    ftm 1 1 1 1 (-4),
    ftm 1 2 0 1 (-2),
    ftm 2 1 0 1 (-2)]

/-- The certificate-side product for flat core 350: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct350 : Poly :=
  polyMul ([tm 6 1 0 0 0 (1)])
    (chartCore249)

/-- KERNEL-CHECKED chart soundness for flat core 350: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore350 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore350)) den one two three four
      = polyEval chartProduct350 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 351 (degree 3), denominators cleared. -/
def flatCore351 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 1 (2),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 1 (-2),
    ftm 1 1 0 1 (-2),
    ftm 2 0 0 1 (-2)]

/-- The certificate-side product for flat core 351: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct351 : Poly :=
  polyMul ([tm 5 1 0 0 0 (1)])
    (chartCore250)

/-- KERNEL-CHECKED chart soundness for flat core 351: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore351 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore351)) den one two three four
      = polyEval chartProduct351 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 352 (degree 2), denominators cleared. -/
def flatCore352 : FlatPoly :=
  [ftm 0 0 0 2 (1),
    ftm 0 1 0 0 (2),
    ftm 0 1 0 1 (-2),
    ftm 0 1 1 0 (-2),
    ftm 0 2 0 0 (-3),
    ftm 1 1 0 0 (-2)]

/-- The certificate-side product for flat core 352: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct352 : Poly :=
  polyMul ([tm 2 0 0 0 0 (1)])
    (chartCore251)

/-- KERNEL-CHECKED chart soundness for flat core 352: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore352 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore352)) den one two three four
      = polyEval chartProduct352 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 353 (degree 4), denominators cleared. -/
def flatCore353 : FlatPoly :=
  [ftm 0 0 1 1 (2),
    ftm 0 0 1 2 (-2),
    ftm 0 0 2 1 (-4),
    ftm 0 0 2 2 (2),
    ftm 0 0 3 1 (2),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 1 (2),
    ftm 1 0 0 1 (-3),
    ftm 1 0 0 2 (3),
    ftm 1 0 1 0 (-3),
    ftm 1 0 1 1 (2),
    ftm 1 0 1 2 (-1),
    ftm 1 0 2 0 (3),
    ftm 1 0 2 1 (1),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (2),
    ftm 1 1 1 0 (1),
    ftm 1 1 2 0 (-2),
    ftm 1 2 0 0 (-1),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 0 (-3),
    ftm 2 0 0 1 (6),
    ftm 2 0 0 2 (-3),
    ftm 2 0 1 0 (3),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (-2),
    ftm 2 1 1 0 (-1),
    ftm 2 2 0 0 (1),
    ftm 3 1 0 0 (1)]

/-- The certificate-side product for flat core 353: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct353 : Poly :=
  polyMul ([tm 2 2 1 1 0 (-1)])
    (chartCore252)

/-- KERNEL-CHECKED chart soundness for flat core 353: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore353 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore353)) den one two three four
      = polyEval chartProduct353 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 354 (degree 4), denominators cleared. -/
def flatCore354 : FlatPoly :=
  [ftm 0 0 1 1 (2),
    ftm 0 0 1 2 (-4),
    ftm 0 0 1 3 (2),
    ftm 0 0 2 1 (-2),
    ftm 0 0 2 2 (2),
    ftm 0 1 0 1 (-3),
    ftm 0 1 0 2 (3),
    ftm 0 1 1 0 (-3),
    ftm 0 1 1 1 (2),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 0 (3),
    ftm 0 1 2 1 (-1),
    ftm 0 2 0 0 (-3),
    ftm 0 2 0 1 (3),
    ftm 0 2 1 0 (6),
    ftm 0 2 1 1 (-1),
    ftm 0 2 2 0 (-3),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (2),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (1),
    ftm 1 1 0 2 (-2),
    ftm 1 1 1 0 (2),
    ftm 1 2 0 0 (1),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-2),
    ftm 1 3 0 0 (1),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (1),
    ftm 2 2 0 0 (1)]

/-- The certificate-side product for flat core 354: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct354 : Poly :=
  polyMul ([tm 3 2 1 0 0 (-1)])
    (chartCore253)

/-- KERNEL-CHECKED chart soundness for flat core 354: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore354 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore354)) den one two three four
      = polyEval chartProduct354 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 355 (degree 4), denominators cleared. -/
def flatCore355 : FlatPoly :=
  [ftm 0 0 1 1 (2),
    ftm 0 0 1 2 (-2),
    ftm 0 0 2 0 (-3),
    ftm 0 0 2 1 (-1),
    ftm 0 0 2 2 (2),
    ftm 0 0 3 1 (2),
    ftm 0 1 1 0 (-3),
    ftm 0 1 1 1 (1),
    ftm 0 1 2 0 (6),
    ftm 0 1 2 1 (-1),
    ftm 0 2 1 0 (3),
    ftm 0 2 2 0 (-3),
    ftm 1 0 1 0 (-3),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (2),
    ftm 1 0 2 0 (3),
    ftm 1 0 2 1 (1),
    ftm 1 1 0 0 (1),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (4),
    ftm 1 1 2 0 (-2),
    ftm 1 2 0 0 (-1),
    ftm 1 2 1 0 (-2),
    ftm 2 0 1 0 (3),
    ftm 2 0 1 1 (-1),
    ftm 2 1 0 0 (-2),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (-1),
    ftm 2 2 0 0 (1),
    ftm 3 1 0 0 (1)]

/-- The certificate-side product for flat core 355: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct355 : Poly :=
  polyMul ([tm 3 2 0 0 0 (1)])
    (chartCore254)

/-- KERNEL-CHECKED chart soundness for flat core 355: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore355 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore355)) den one two three four
      = polyEval chartProduct355 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 356 (degree 4), denominators cleared. -/
def flatCore356 : FlatPoly :=
  [ftm 0 0 0 2 (3),
    ftm 0 0 1 1 (-2),
    ftm 0 0 1 2 (1),
    ftm 0 0 1 3 (-2),
    ftm 0 0 2 1 (2),
    ftm 0 0 2 2 (-2),
    ftm 0 1 0 1 (3),
    ftm 0 1 0 2 (-3),
    ftm 0 1 1 1 (1),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 1 (-2),
    ftm 0 2 0 1 (-3),
    ftm 0 2 1 1 (1),
    ftm 1 0 0 1 (3),
    ftm 1 0 0 2 (-6),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 0 (-1),
    ftm 1 1 0 1 (-4),
    ftm 1 1 0 2 (2),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (2),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (-1),
    ftm 1 3 0 0 (-1),
    ftm 2 0 0 1 (-3),
    ftm 2 0 0 2 (3),
    ftm 2 1 0 0 (1),
    ftm 2 1 0 1 (2),
    ftm 2 2 0 0 (-1)]

/-- The certificate-side product for flat core 356: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct356 : Poly :=
  polyMul ([tm 3 0 0 0 0 (1)])
    (chartCore255)

/-- KERNEL-CHECKED chart soundness for flat core 356: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore356 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore356)) den one two three four
      = polyEval chartProduct356 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 357 (degree 3), denominators cleared. -/
def flatCore357 : FlatPoly :=
  [ftm 0 0 2 1 (2),
    ftm 1 0 1 0 (3),
    ftm 1 0 1 1 (-1),
    ftm 1 1 1 0 (-2),
    ftm 2 1 0 0 (1)]

/-- The certificate-side product for flat core 357: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct357 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    ([tm 6 0 0 0 0 (2),
      tm 4 0 1 1 0 (2),
      tm 3 1 1 1 0 (3),
      tm 2 1 2 1 0 (1),
      tm 1 1 2 2 0 (3),
      tm 0 1 2 2 1 (3),
      tm 0 1 3 2 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 357: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore357 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore357)) den one two three four
      = polyEval chartProduct357 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 358 (degree 3), denominators cleared. -/
def flatCore358 : FlatPoly :=
  [ftm 0 0 1 2 (2),
    ftm 0 1 0 1 (3),
    ftm 0 1 1 1 (-1),
    ftm 1 1 0 1 (-2),
    ftm 1 2 0 0 (1)]

/-- The certificate-side product for flat core 358: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct358 : Poly :=
  polyMul ([tm 5 1 0 0 0 (1)])
    ([tm 6 0 0 0 0 (2),
      tm 5 0 1 0 0 (3),
      tm 4 1 1 0 0 (2),
      tm 3 1 2 0 0 (3),
      tm 2 1 2 1 0 (1),
      tm 1 1 2 1 1 (3),
      tm 0 2 3 1 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 358: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore358 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore358)) den one two three four
      = polyEval chartProduct358 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 359 (degree 2), denominators cleared. -/
def flatCore359 : FlatPoly :=
  [ftm 0 0 1 1 (2),
    ftm 1 0 0 1 (-3),
    ftm 1 1 0 0 (1)]

/-- The certificate-side product for flat core 359: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct359 : Poly :=
  polyMul ([tm 3 1 0 0 0 (1)])
    (chartCore256)

/-- KERNEL-CHECKED chart soundness for flat core 359: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore359 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore359)) den one two three four
      = polyEval chartProduct359 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 360 (degree 2), denominators cleared. -/
def flatCore360 : FlatPoly :=
  [ftm 0 0 1 1 (2),
    ftm 0 1 1 0 (-3),
    ftm 1 1 0 0 (1)]

/-- The certificate-side product for flat core 360: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct360 : Poly :=
  polyMul ([tm 3 1 0 0 0 (1)])
    (chartCore257)

/-- KERNEL-CHECKED chart soundness for flat core 360: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore360 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore360)) den one two three four
      = polyEval chartProduct360 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 361 (degree 2), denominators cleared. -/
def flatCore361 : FlatPoly :=
  [ftm 0 0 0 1 (2),
    ftm 0 0 0 2 (-2),
    ftm 0 0 1 1 (1),
    ftm 0 1 0 0 (-1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (1),
    ftm 0 2 0 0 (1),
    ftm 1 0 0 1 (1),
    ftm 1 1 0 0 (1)]

/-- The certificate-side product for flat core 361: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct361 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore258)

/-- KERNEL-CHECKED chart soundness for flat core 361: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore361 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore361)) den one two three four
      = polyEval chartProduct361 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 362 (degree 2), denominators cleared. -/
def flatCore362 : FlatPoly :=
  [ftm 0 0 1 0 (2),
    ftm 0 0 1 1 (1),
    ftm 0 0 2 0 (-2),
    ftm 0 1 1 0 (1),
    ftm 1 0 0 0 (-1),
    ftm 1 0 0 1 (1),
    ftm 1 0 1 0 (-1),
    ftm 1 1 0 0 (1),
    ftm 2 0 0 0 (1)]

/-- The certificate-side product for flat core 362: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct362 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    (chartCore259)

/-- KERNEL-CHECKED chart soundness for flat core 362: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore362 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore362)) den one two three four
      = polyEval chartProduct362 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 363 (degree 2), denominators cleared. -/
def flatCore363 : FlatPoly :=
  [ftm 0 0 0 1 (2),
    ftm 0 0 0 2 (-2),
    ftm 0 0 1 1 (-2),
    ftm 0 1 0 0 (-1),
    ftm 0 1 0 1 (-1),
    ftm 0 1 1 0 (-2),
    ftm 0 2 0 0 (1),
    ftm 1 0 0 1 (-2),
    ftm 1 1 0 0 (-2)]

/-- The certificate-side product for flat core 363: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct363 : Poly :=
  polyMul ([tm 2 1 1 0 0 (1)])
    (chartCore260)

/-- KERNEL-CHECKED chart soundness for flat core 363: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore363 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore363)) den one two three four
      = polyEval chartProduct363 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 364 (degree 2), denominators cleared. -/
def flatCore364 : FlatPoly :=
  [ftm 0 0 1 0 (2),
    ftm 0 0 1 1 (-2),
    ftm 0 0 2 0 (-2),
    ftm 0 1 1 0 (-2),
    ftm 1 0 0 0 (-1),
    ftm 1 0 0 1 (-2),
    ftm 1 0 1 0 (-1),
    ftm 1 1 0 0 (-2),
    ftm 2 0 0 0 (1)]

/-- The certificate-side product for flat core 364: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct364 : Poly :=
  polyMul ([tm 1 1 1 1 0 (-1)])
    (chartCore261)

/-- KERNEL-CHECKED chart soundness for flat core 364: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore364 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore364)) den one two three four
      = polyEval chartProduct364 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 365 (degree 4), denominators cleared. -/
def flatCore365 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 1 (-2),
    ftm 0 0 2 2 (1),
    ftm 0 0 3 1 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 1 (1),
    ftm 1 0 0 1 (-3),
    ftm 1 0 0 2 (3),
    ftm 1 0 1 0 (-3),
    ftm 1 0 1 1 (4),
    ftm 1 0 1 2 (-2),
    ftm 1 0 2 0 (3),
    ftm 1 0 2 1 (-1),
    ftm 1 1 0 0 (2),
    ftm 1 1 0 1 (1),
    ftm 1 1 1 0 (-1),
    ftm 1 1 2 0 (-1),
    ftm 1 2 0 0 (-2),
    ftm 1 2 1 0 (2),
    ftm 2 0 0 0 (-3),
    ftm 2 0 0 1 (6),
    ftm 2 0 0 2 (-3),
    ftm 2 0 1 0 (3),
    ftm 2 0 1 1 (-2),
    ftm 2 1 0 0 (-1),
    ftm 2 1 0 1 (-1),
    ftm 2 1 1 0 (1),
    ftm 2 2 0 0 (2),
    ftm 3 1 0 0 (2)]

/-- The certificate-side product for flat core 365: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct365 : Poly :=
  polyMul ([tm 2 2 1 1 0 (-1)])
    (chartCore262)

/-- KERNEL-CHECKED chart soundness for flat core 365: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore365 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore365)) den one two three four
      = polyEval chartProduct365 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 366 (degree 4), denominators cleared. -/
def flatCore366 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-2),
    ftm 0 0 1 3 (1),
    ftm 0 0 2 1 (-1),
    ftm 0 0 2 2 (1),
    ftm 0 1 0 1 (-3),
    ftm 0 1 0 2 (3),
    ftm 0 1 1 0 (-3),
    ftm 0 1 1 1 (4),
    ftm 0 1 1 2 (-1),
    ftm 0 1 2 0 (3),
    ftm 0 1 2 1 (-2),
    ftm 0 2 0 0 (-3),
    ftm 0 2 0 1 (3),
    ftm 0 2 1 0 (6),
    ftm 0 2 1 1 (-2),
    ftm 0 2 2 0 (-3),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 0 (2),
    ftm 1 1 0 1 (-1),
    ftm 1 1 0 2 (-1),
    ftm 1 1 1 0 (1),
    ftm 1 2 0 0 (-1),
    ftm 1 2 0 1 (1),
    ftm 1 2 1 0 (-1),
    ftm 1 3 0 0 (2),
    ftm 2 1 0 0 (-2),
    ftm 2 1 0 1 (2),
    ftm 2 2 0 0 (2)]

/-- The certificate-side product for flat core 366: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct366 : Poly :=
  polyMul ([tm 3 2 1 0 0 (-1)])
    (chartCore263)

/-- KERNEL-CHECKED chart soundness for flat core 366: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore366 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore366)) den one two three four
      = polyEval chartProduct366 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 367 (degree 4), denominators cleared. -/
def flatCore367 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 2 0 (-3),
    ftm 0 0 2 1 (1),
    ftm 0 0 2 2 (1),
    ftm 0 0 3 1 (1),
    ftm 0 1 1 0 (-3),
    ftm 0 1 1 1 (2),
    ftm 0 1 2 0 (6),
    ftm 0 1 2 1 (-2),
    ftm 0 2 1 0 (3),
    ftm 0 2 2 0 (-3),
    ftm 1 0 1 0 (-3),
    ftm 1 0 1 1 (1),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (3),
    ftm 1 0 2 1 (-1),
    ftm 1 1 0 0 (2),
    ftm 1 1 0 1 (-2),
    ftm 1 1 1 0 (2),
    ftm 1 1 2 0 (-1),
    ftm 1 2 0 0 (-2),
    ftm 1 2 1 0 (-1),
    ftm 2 0 1 0 (3),
    ftm 2 0 1 1 (-2),
    ftm 2 1 0 0 (-4),
    ftm 2 1 0 1 (2),
    ftm 2 1 1 0 (1),
    ftm 2 2 0 0 (2),
    ftm 3 1 0 0 (2)]

/-- The certificate-side product for flat core 367: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct367 : Poly :=
  polyMul ([tm 3 2 0 0 0 (1)])
    (chartCore264)

/-- KERNEL-CHECKED chart soundness for flat core 367: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore367 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore367)) den one two three four
      = polyEval chartProduct367 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 368 (degree 4), denominators cleared. -/
def flatCore368 : FlatPoly :=
  [ftm 0 0 0 2 (3),
    ftm 0 0 1 1 (-1),
    ftm 0 0 1 2 (-1),
    ftm 0 0 1 3 (-1),
    ftm 0 0 2 1 (1),
    ftm 0 0 2 2 (-1),
    ftm 0 1 0 1 (3),
    ftm 0 1 0 2 (-3),
    ftm 0 1 1 1 (-1),
    ftm 0 1 1 2 (1),
    ftm 0 1 2 1 (-1),
    ftm 0 2 0 1 (-3),
    ftm 0 2 1 1 (2),
    ftm 1 0 0 1 (3),
    ftm 1 0 0 2 (-6),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (2),
    ftm 1 1 0 0 (-2),
    ftm 1 1 0 1 (-2),
    ftm 1 1 0 2 (1),
    ftm 1 1 1 0 (2),
    ftm 1 2 0 0 (4),
    ftm 1 2 0 1 (-1),
    ftm 1 2 1 0 (-2),
    ftm 1 3 0 0 (-2),
    ftm 2 0 0 1 (-3),
    ftm 2 0 0 2 (3),
    ftm 2 1 0 0 (2),
    ftm 2 1 0 1 (1),
    ftm 2 2 0 0 (-2)]

/-- The certificate-side product for flat core 368: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct368 : Poly :=
  polyMul ([tm 3 0 0 0 0 (1)])
    (chartCore265)

/-- KERNEL-CHECKED chart soundness for flat core 368: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore368 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore368)) den one two three four
      = polyEval chartProduct368 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 369 (degree 3), denominators cleared. -/
def flatCore369 : FlatPoly :=
  [ftm 0 0 2 1 (1),
    ftm 1 0 1 0 (3),
    ftm 1 0 1 1 (-2),
    ftm 1 1 1 0 (-1),
    ftm 2 1 0 0 (2)]

/-- The certificate-side product for flat core 369: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct369 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    ([tm 6 0 0 0 0 (1),
      tm 4 0 1 1 0 (1),
      tm 3 1 1 1 0 (3),
      tm 2 1 2 1 0 (2),
      tm 1 1 2 2 0 (3),
      tm 0 1 2 2 1 (3),
      tm 0 1 3 2 0 (2)])

/-- KERNEL-CHECKED chart soundness for flat core 369: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore369 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore369)) den one two three four
      = polyEval chartProduct369 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 370 (degree 3), denominators cleared. -/
def flatCore370 : FlatPoly :=
  [ftm 0 0 1 2 (1),
    ftm 0 1 0 1 (3),
    ftm 0 1 1 1 (-2),
    ftm 1 1 0 1 (-1),
    ftm 1 2 0 0 (2)]

/-- The certificate-side product for flat core 370: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct370 : Poly :=
  polyMul ([tm 5 1 0 0 0 (1)])
    ([tm 6 0 0 0 0 (1),
      tm 5 0 1 0 0 (3),
      tm 4 1 1 0 0 (1),
      tm 3 1 2 0 0 (3),
      tm 2 1 2 1 0 (2),
      tm 1 1 2 1 1 (3),
      tm 0 2 3 1 0 (2)])

/-- KERNEL-CHECKED chart soundness for flat core 370: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore370 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore370)) den one two three four
      = polyEval chartProduct370 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 371 (degree 2), denominators cleared. -/
def flatCore371 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 1 0 0 1 (-3),
    ftm 1 1 0 0 (2)]

/-- The certificate-side product for flat core 371: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct371 : Poly :=
  polyMul ([tm 3 1 0 0 0 (1)])
    (chartCore266)

/-- KERNEL-CHECKED chart soundness for flat core 371: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore371 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore371)) den one two three four
      = polyEval chartProduct371 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 372 (degree 2), denominators cleared. -/
def flatCore372 : FlatPoly :=
  [ftm 0 0 1 1 (1),
    ftm 0 1 1 0 (-3),
    ftm 1 1 0 0 (2)]

/-- The certificate-side product for flat core 372: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct372 : Poly :=
  polyMul ([tm 3 1 0 0 0 (1)])
    (chartCore267)

/-- KERNEL-CHECKED chart soundness for flat core 372: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore372 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore372)) den one two three four
      = polyEval chartProduct372 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 373 (degree 2), denominators cleared. -/
def flatCore373 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (2),
    ftm 0 1 0 0 (-2),
    ftm 0 1 0 1 (1),
    ftm 0 1 1 0 (2),
    ftm 0 2 0 0 (2),
    ftm 1 0 0 1 (2),
    ftm 1 1 0 0 (2)]

/-- The certificate-side product for flat core 373: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct373 : Poly :=
  polyMul ([tm 2 1 0 0 0 (1)])
    (chartCore268)

/-- KERNEL-CHECKED chart soundness for flat core 373: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore373 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore373)) den one two three four
      = polyEval chartProduct373 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 374 (degree 2), denominators cleared. -/
def flatCore374 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (2),
    ftm 0 0 2 0 (-1),
    ftm 0 1 1 0 (2),
    ftm 1 0 0 0 (-2),
    ftm 1 0 0 1 (2),
    ftm 1 0 1 0 (1),
    ftm 1 1 0 0 (2),
    ftm 2 0 0 0 (2)]

/-- The certificate-side product for flat core 374: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct374 : Poly :=
  polyMul ([tm 1 1 0 0 0 (1)])
    (chartCore269)

/-- KERNEL-CHECKED chart soundness for flat core 374: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore374 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore374)) den one two three four
      = polyEval chartProduct374 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 375 (degree 2), denominators cleared. -/
def flatCore375 : FlatPoly :=
  [ftm 0 0 0 1 (1),
    ftm 0 0 0 2 (-1),
    ftm 0 0 1 1 (-1),
    ftm 0 1 0 0 (-2),
    ftm 0 1 0 1 (1),
    ftm 0 1 1 0 (-1),
    ftm 0 2 0 0 (2),
    ftm 1 0 0 1 (-1),
    ftm 1 1 0 0 (-1)]

/-- The certificate-side product for flat core 375: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct375 : Poly :=
  polyMul ([tm 2 1 1 0 0 (1)])
    (chartCore270)

/-- KERNEL-CHECKED chart soundness for flat core 375: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore375 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore375)) den one two three four
      = polyEval chartProduct375 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 376 (degree 2), denominators cleared. -/
def flatCore376 : FlatPoly :=
  [ftm 0 0 1 0 (1),
    ftm 0 0 1 1 (-1),
    ftm 0 0 2 0 (-1),
    ftm 0 1 1 0 (-1),
    ftm 1 0 0 0 (-2),
    ftm 1 0 0 1 (-1),
    ftm 1 0 1 0 (1),
    ftm 1 1 0 0 (-1),
    ftm 2 0 0 0 (2)]

/-- The certificate-side product for flat core 376: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct376 : Poly :=
  polyMul ([tm 1 1 1 1 0 (-1)])
    (chartCore271)

/-- KERNEL-CHECKED chart soundness for flat core 376: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore376 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore376)) den one two three four
      = polyEval chartProduct376 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 377 (degree 4), denominators cleared. -/
def flatCore377 : FlatPoly :=
  [ftm 0 1 1 0 (2),
    ftm 0 1 1 1 (-2),
    ftm 0 1 2 0 (-4),
    ftm 0 1 2 1 (2),
    ftm 0 1 3 0 (2),
    ftm 0 2 1 0 (-2),
    ftm 0 2 2 0 (2),
    ftm 1 0 0 1 (4),
    ftm 1 0 0 2 (-4),
    ftm 1 0 1 0 (3),
    ftm 1 0 1 1 (-8),
    ftm 1 0 1 2 (4),
    ftm 1 0 2 0 (-3),
    ftm 1 0 2 1 (4),
    ftm 1 1 0 1 (-4),
    ftm 1 1 1 0 (-7),
    ftm 1 1 1 1 (6),
    ftm 1 1 2 0 (7),
    ftm 1 2 1 0 (2),
    ftm 2 0 0 0 (3),
    ftm 2 0 0 1 (-8),
    ftm 2 0 0 2 (4),
    ftm 2 0 1 0 (-3),
    ftm 2 0 1 1 (5),
    ftm 2 1 0 0 (-3),
    ftm 2 1 0 1 (4),
    ftm 2 1 1 0 (5),
    ftm 3 0 0 1 (1)]

/-- The certificate-side product for flat core 377: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct377 : Poly :=
  polyMul ([tm 2 2 1 1 0 (1)])
    ([tm 10 0 0 0 0 (3),
      tm 8 0 1 1 0 (3),
      tm 7 0 1 1 1 (4),
      tm 9 1 0 0 0 (3),
      tm 8 1 1 0 0 (3),
      tm 7 1 1 0 1 (2),
      tm 7 1 1 1 0 (6),
      tm 6 1 1 1 1 (6),
      tm 6 1 2 1 0 (3),
      tm 5 1 2 1 1 (4),
      tm 5 1 2 2 0 (3),
      tm 4 1 2 2 1 (6),
      tm 3 1 2 2 2 (4),
      tm 7 2 1 0 0 (3),
      tm 6 2 1 1 0 (3),
      tm 5 2 1 1 1 (3),
      tm 5 2 2 0 1 (2),
      tm 5 2 2 1 0 (6),
      tm 4 2 2 1 1 (3),
      tm 3 2 2 1 2 (2),
      tm 4 2 2 2 0 (6),
      tm 3 2 2 2 1 (9),
      tm 2 2 2 2 2 (3),
      tm 3 2 3 2 0 (3),
      tm 2 2 3 2 1 (3),
      tm 2 2 3 3 0 (3),
      tm 1 2 3 3 1 (6),
      tm 0 2 3 3 2 (3)])

/-- KERNEL-CHECKED chart soundness for flat core 377: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore377 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore377)) den one two three four
      = polyEval chartProduct377 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 378 (degree 4), denominators cleared. -/
def flatCore378 : FlatPoly :=
  [ftm 0 1 0 1 (3),
    ftm 0 1 0 2 (-3),
    ftm 0 1 1 0 (5),
    ftm 0 1 1 1 (-10),
    ftm 0 1 1 2 (5),
    ftm 0 1 2 0 (-5),
    ftm 0 1 2 1 (5),
    ftm 0 2 0 0 (3),
    ftm 0 2 0 1 (-3),
    ftm 0 2 1 0 (-10),
    ftm 0 2 1 1 (7),
    ftm 0 2 2 0 (5),
    ftm 0 3 1 0 (2),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-2),
    ftm 1 0 0 3 (1),
    ftm 1 0 1 1 (-1),
    ftm 1 0 1 2 (1),
    ftm 1 1 0 1 (-5),
    ftm 1 1 0 2 (5),
    ftm 1 1 1 0 (-5),
    ftm 1 1 1 1 (6),
    ftm 1 2 0 0 (-3),
    ftm 1 2 0 1 (4),
    ftm 1 2 1 0 (5),
    ftm 2 0 0 1 (-1),
    ftm 2 0 0 2 (1),
    ftm 2 1 0 1 (1)]

/-- The certificate-side product for flat core 378: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct378 : Poly :=
  polyMul ([tm 4 2 1 0 0 (1)])
    ([tm 9 0 0 0 0 (3),
      tm 8 0 1 0 0 (3),
      tm 7 0 1 1 0 (3),
      tm 6 0 1 1 1 (3),
      tm 8 1 0 0 0 (3),
      tm 7 1 1 0 0 (6),
      tm 6 1 1 1 0 (3),
      tm 5 1 1 1 1 (6),
      tm 4 1 1 2 1 (1),
      tm 6 1 2 0 0 (6),
      tm 5 1 2 1 0 (6),
      tm 4 1 2 1 1 (9),
      tm 3 1 2 2 1 (3),
      tm 2 1 2 2 2 (3),
      tm 2 1 2 3 1 (1),
      tm 1 1 2 3 2 (1),
      tm 6 2 1 0 0 (3),
      tm 4 2 1 1 1 (5),
      tm 5 2 2 0 0 (3),
      tm 4 2 2 1 0 (3),
      tm 3 2 2 1 1 (6),
      tm 2 2 2 2 1 (5),
      tm 1 2 2 2 2 (5),
      tm 4 2 3 0 0 (3),
      tm 3 2 3 1 0 (3),
      tm 2 2 3 1 1 (6),
      tm 1 2 3 2 1 (3),
      tm 0 2 3 2 2 (3)])

/-- KERNEL-CHECKED chart soundness for flat core 378: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore378 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore378)) den one two three four
      = polyEval chartProduct378 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 379 (degree 4), denominators cleared. -/
def flatCore379 : FlatPoly :=
  [ftm 0 0 2 0 (3),
    ftm 0 0 2 1 (-3),
    ftm 0 1 1 0 (5),
    ftm 0 1 1 1 (-5),
    ftm 0 1 2 0 (-10),
    ftm 0 1 2 1 (5),
    ftm 0 1 3 0 (2),
    ftm 0 2 1 0 (-5),
    ftm 0 2 2 0 (5),
    ftm 1 0 0 1 (1),
    ftm 1 0 0 2 (-1),
    ftm 1 0 1 0 (3),
    ftm 1 0 1 1 (-5),
    ftm 1 0 1 2 (1),
    ftm 1 0 2 0 (-3),
    ftm 1 0 2 1 (4),
    ftm 1 1 0 1 (-1),
    ftm 1 1 1 0 (-10),
    ftm 1 1 1 1 (6),
    ftm 1 1 2 0 (7),
    ftm 1 2 1 0 (5),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (1),
    ftm 2 0 1 0 (-3),
    ftm 2 0 1 1 (5),
    ftm 2 1 0 1 (1),
    ftm 2 1 1 0 (5),
    ftm 3 0 0 1 (1)]

/-- The certificate-side product for flat core 379: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct379 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    ([tm 5 0 2 2 1 (1),
      tm 9 1 0 0 0 (3),
      tm 8 1 1 0 0 (3),
      tm 7 1 1 1 0 (6),
      tm 6 1 1 1 1 (3),
      tm 6 1 2 1 0 (3),
      tm 5 1 2 1 1 (5),
      tm 5 1 2 2 0 (3),
      tm 4 1 2 2 1 (3),
      tm 3 1 3 2 1 (1),
      tm 1 1 3 3 2 (1),
      tm 8 2 0 0 0 (3),
      tm 7 2 1 0 0 (3),
      tm 6 2 1 1 0 (6),
      tm 5 2 1 1 1 (6),
      tm 6 2 2 0 0 (3),
      tm 5 2 2 1 0 (6),
      tm 4 2 2 1 1 (6),
      tm 4 2 2 2 0 (3),
      tm 3 2 2 2 1 (9),
      tm 2 2 2 2 2 (3),
      tm 4 2 3 1 0 (3),
      tm 3 2 3 1 1 (5),
      tm 3 2 3 2 0 (3),
      tm 2 2 3 2 1 (6),
      tm 1 2 3 2 2 (5),
      tm 1 2 3 3 1 (3),
      tm 0 2 3 3 2 (3)])

/-- KERNEL-CHECKED chart soundness for flat core 379: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore379 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore379)) den one two three four
      = polyEval chartProduct379 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 380 (degree 4), denominators cleared. -/
def flatCore380 : FlatPoly :=
  [ftm 0 0 0 2 (3),
    ftm 0 0 1 2 (-3),
    ftm 0 1 0 1 (3),
    ftm 0 1 0 2 (-3),
    ftm 0 1 1 0 (2),
    ftm 0 1 1 1 (-7),
    ftm 0 1 1 2 (5),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (2),
    ftm 0 2 0 1 (-3),
    ftm 0 2 1 0 (-4),
    ftm 0 2 1 1 (7),
    ftm 0 2 2 0 (2),
    ftm 0 3 1 0 (2),
    ftm 1 0 0 1 (4),
    ftm 1 0 0 2 (-8),
    ftm 1 0 0 3 (1),
    ftm 1 0 1 1 (-4),
    ftm 1 0 1 2 (4),
    ftm 1 1 0 1 (-8),
    ftm 1 1 0 2 (5),
    ftm 1 1 1 0 (-2),
    ftm 1 1 1 1 (6),
    ftm 1 2 0 1 (4),
    ftm 1 2 1 0 (2),
    ftm 2 0 0 1 (-4),
    ftm 2 0 0 2 (4),
    ftm 2 1 0 1 (4)]

/-- The certificate-side product for flat core 380: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct380 : Poly :=
  polyMul ([tm 5 0 0 0 0 (1)])
    ([tm 11 0 0 0 0 (3),
      tm 10 1 0 0 0 (3),
      tm 9 1 1 0 0 (6),
      tm 8 1 1 1 0 (3),
      tm 7 1 1 1 1 (6),
      tm 8 2 1 0 0 (6),
      tm 7 2 1 1 0 (3),
      tm 6 2 1 1 1 (3),
      tm 7 2 2 0 0 (3),
      tm 6 2 2 1 0 (6),
      tm 5 2 2 1 1 (9),
      tm 5 2 2 2 0 (3),
      tm 4 2 2 2 1 (6),
      tm 3 2 2 2 2 (3),
      tm 6 3 2 0 0 (3),
      tm 5 3 2 1 0 (3),
      tm 4 3 2 1 1 (3),
      tm 3 3 2 2 1 (4),
      tm 4 3 3 1 0 (3),
      tm 3 3 3 1 1 (3),
      tm 3 3 3 2 0 (3),
      tm 2 3 3 2 1 (6),
      tm 1 3 3 2 2 (3),
      tm 1 3 3 3 1 (4),
      tm 0 3 3 3 2 (4),
      tm 3 4 2 1 1 (2),
      tm 1 4 3 2 1 (2),
      tm 0 4 3 2 2 (2)])

/-- KERNEL-CHECKED chart soundness for flat core 380: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore380 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore380)) den one two three four
      = polyEval chartProduct380 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 381 (degree 3), denominators cleared. -/
def flatCore381 : FlatPoly :=
  [ftm 0 1 2 0 (2),
    ftm 1 0 1 0 (-3),
    ftm 1 0 1 1 (4),
    ftm 1 1 1 0 (5),
    ftm 2 0 0 1 (1)]

/-- The certificate-side product for flat core 381: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct381 : Poly :=
  polyMul ([tm 4 2 1 0 0 (1)])
    (chartCore272)

/-- KERNEL-CHECKED chart soundness for flat core 381: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore381 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore381)) den one two three four
      = polyEval chartProduct381 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 382 (degree 3), denominators cleared. -/
def flatCore382 : FlatPoly :=
  [ftm 0 1 0 1 (3),
    ftm 0 1 1 1 (-5),
    ftm 0 2 1 0 (-2),
    ftm 1 0 0 2 (-1),
    ftm 1 1 0 1 (-4)]

/-- The certificate-side product for flat core 382: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct382 : Poly :=
  polyMul ([tm 6 1 1 0 0 (1)])
    (chartCore273)

/-- KERNEL-CHECKED chart soundness for flat core 382: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore382 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore382)) den one two three four
      = polyEval chartProduct382 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 383 (degree 2), denominators cleared. -/
def flatCore383 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 1 0 0 1 (2)]

/-- The certificate-side product for flat core 383: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct383 : Poly :=
  polyMul ([tm 5 1 1 0 0 (1)])
    ([tm 0 0 0 1 0 (2),
      tm 0 1 0 0 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 383: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore383 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore383)) den one two three four
      = polyEval chartProduct383 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 384 (degree 2), denominators cleared. -/
def flatCore384 : FlatPoly :=
  [ftm 0 1 1 0 (5),
    ftm 1 0 0 1 (1)]

/-- The certificate-side product for flat core 384: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct384 : Poly :=
  polyMul ([tm 5 1 1 0 0 (1)])
    ([tm 0 0 0 1 0 (1),
      tm 0 1 0 0 0 (5)])

/-- KERNEL-CHECKED chart soundness for flat core 384: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore384 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore384)) den one two three four
      = polyEval chartProduct384 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 385 (degree 4), denominators cleared. -/
def flatCore385 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-1),
    ftm 0 1 2 0 (-2),
    ftm 0 1 2 1 (1),
    ftm 0 1 3 0 (1),
    ftm 0 2 1 0 (-1),
    ftm 0 2 2 0 (1),
    ftm 1 0 0 1 (5),
    ftm 1 0 0 2 (-5),
    ftm 1 0 1 0 (3),
    ftm 1 0 1 1 (-10),
    ftm 1 0 1 2 (5),
    ftm 1 0 2 0 (-3),
    ftm 1 0 2 1 (5),
    ftm 1 1 0 1 (-5),
    ftm 1 1 1 0 (-5),
    ftm 1 1 1 1 (6),
    ftm 1 1 2 0 (5),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 0 (3),
    ftm 2 0 0 1 (-10),
    ftm 2 0 0 2 (5),
    ftm 2 0 1 0 (-3),
    ftm 2 0 1 1 (7),
    ftm 2 1 0 0 (-3),
    ftm 2 1 0 1 (5),
    ftm 2 1 1 0 (4),
    ftm 3 0 0 1 (2)]

/-- The certificate-side product for flat core 385: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct385 : Poly :=
  polyMul ([tm 2 2 1 1 0 (1)])
    ([tm 10 0 0 0 0 (3),
      tm 8 0 1 1 0 (3),
      tm 7 0 1 1 1 (5),
      tm 9 1 0 0 0 (3),
      tm 8 1 1 0 0 (3),
      tm 7 1 1 0 1 (1),
      tm 7 1 1 1 0 (6),
      tm 6 1 1 1 1 (6),
      tm 6 1 2 1 0 (3),
      tm 5 1 2 1 1 (5),
      tm 5 1 2 2 0 (3),
      tm 4 1 2 2 1 (6),
      tm 3 1 2 2 2 (5),
      tm 7 2 1 0 0 (3),
      tm 6 2 1 1 0 (3),
      tm 5 2 1 1 1 (3),
      tm 5 2 2 0 1 (1),
      tm 5 2 2 1 0 (6),
      tm 4 2 2 1 1 (3),
      tm 3 2 2 1 2 (1),
      tm 4 2 2 2 0 (6),
      tm 3 2 2 2 1 (9),
      tm 2 2 2 2 2 (3),
      tm 3 2 3 2 0 (3),
      tm 2 2 3 2 1 (3),
      tm 2 2 3 3 0 (3),
      tm 1 2 3 3 1 (6),
      tm 0 2 3 3 2 (3)])

/-- KERNEL-CHECKED chart soundness for flat core 385: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore385 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore385)) den one two three four
      = polyEval chartProduct385 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 386 (degree 4), denominators cleared. -/
def flatCore386 : FlatPoly :=
  [ftm 0 1 0 1 (3),
    ftm 0 1 0 2 (-3),
    ftm 0 1 1 0 (4),
    ftm 0 1 1 1 (-8),
    ftm 0 1 1 2 (4),
    ftm 0 1 2 0 (-4),
    ftm 0 1 2 1 (4),
    ftm 0 2 0 0 (3),
    ftm 0 2 0 1 (-3),
    ftm 0 2 1 0 (-8),
    ftm 0 2 1 1 (5),
    ftm 0 2 2 0 (4),
    ftm 0 3 1 0 (1),
    ftm 1 0 0 1 (2),
    ftm 1 0 0 2 (-4),
    ftm 1 0 0 3 (2),
    ftm 1 0 1 1 (-2),
    ftm 1 0 1 2 (2),
    ftm 1 1 0 1 (-7),
    ftm 1 1 0 2 (7),
    ftm 1 1 1 0 (-4),
    ftm 1 1 1 1 (6),
    ftm 1 2 0 0 (-3),
    ftm 1 2 0 1 (5),
    ftm 1 2 1 0 (4),
    ftm 2 0 0 1 (-2),
    ftm 2 0 0 2 (2),
    ftm 2 1 0 1 (2)]

/-- The certificate-side product for flat core 386: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct386 : Poly :=
  polyMul ([tm 4 2 1 0 0 (1)])
    ([tm 9 0 0 0 0 (3),
      tm 8 0 1 0 0 (3),
      tm 7 0 1 1 0 (3),
      tm 6 0 1 1 1 (3),
      tm 8 1 0 0 0 (3),
      tm 7 1 1 0 0 (6),
      tm 6 1 1 1 0 (3),
      tm 5 1 1 1 1 (6),
      tm 4 1 1 2 1 (2),
      tm 6 1 2 0 0 (6),
      tm 5 1 2 1 0 (6),
      tm 4 1 2 1 1 (9),
      tm 3 1 2 2 1 (3),
      tm 2 1 2 2 2 (3),
      tm 2 1 2 3 1 (2),
      tm 1 1 2 3 2 (2),
      tm 6 2 1 0 0 (3),
      tm 4 2 1 1 1 (4),
      tm 5 2 2 0 0 (3),
      tm 4 2 2 1 0 (3),
      tm 3 2 2 1 1 (6),
      tm 2 2 2 2 1 (4),
      tm 1 2 2 2 2 (4),
      tm 4 2 3 0 0 (3),
      tm 3 2 3 1 0 (3),
      tm 2 2 3 1 1 (6),
      tm 1 2 3 2 1 (3),
      tm 0 2 3 2 2 (3)])

/-- KERNEL-CHECKED chart soundness for flat core 386: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore386 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore386)) den one two three four
      = polyEval chartProduct386 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 387 (degree 4), denominators cleared. -/
def flatCore387 : FlatPoly :=
  [ftm 0 0 2 0 (3),
    ftm 0 0 2 1 (-3),
    ftm 0 1 1 0 (4),
    ftm 0 1 1 1 (-4),
    ftm 0 1 2 0 (-8),
    ftm 0 1 2 1 (4),
    ftm 0 1 3 0 (1),
    ftm 0 2 1 0 (-4),
    ftm 0 2 2 0 (4),
    ftm 1 0 0 1 (2),
    ftm 1 0 0 2 (-2),
    ftm 1 0 1 0 (3),
    ftm 1 0 1 1 (-7),
    ftm 1 0 1 2 (2),
    ftm 1 0 2 0 (-3),
    ftm 1 0 2 1 (5),
    ftm 1 1 0 1 (-2),
    ftm 1 1 1 0 (-8),
    ftm 1 1 1 1 (6),
    ftm 1 1 2 0 (5),
    ftm 1 2 1 0 (4),
    ftm 2 0 0 1 (-4),
    ftm 2 0 0 2 (2),
    ftm 2 0 1 0 (-3),
    ftm 2 0 1 1 (7),
    ftm 2 1 0 1 (2),
    ftm 2 1 1 0 (4),
    ftm 3 0 0 1 (2)]

/-- The certificate-side product for flat core 387: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct387 : Poly :=
  polyMul ([tm 4 2 0 0 0 (1)])
    ([tm 5 0 2 2 1 (2),
      tm 9 1 0 0 0 (3),
      tm 8 1 1 0 0 (3),
      tm 7 1 1 1 0 (6),
      tm 6 1 1 1 1 (3),
      tm 6 1 2 1 0 (3),
      tm 5 1 2 1 1 (4),
      tm 5 1 2 2 0 (3),
      tm 4 1 2 2 1 (3),
      tm 3 1 3 2 1 (2),
      tm 1 1 3 3 2 (2),
      tm 8 2 0 0 0 (3),
      tm 7 2 1 0 0 (3),
      tm 6 2 1 1 0 (6),
      tm 5 2 1 1 1 (6),
      tm 6 2 2 0 0 (3),
      tm 5 2 2 1 0 (6),
      tm 4 2 2 1 1 (6),
      tm 4 2 2 2 0 (3),
      tm 3 2 2 2 1 (9),
      tm 2 2 2 2 2 (3),
      tm 4 2 3 1 0 (3),
      tm 3 2 3 1 1 (4),
      tm 3 2 3 2 0 (3),
      tm 2 2 3 2 1 (6),
      tm 1 2 3 2 2 (4),
      tm 1 2 3 3 1 (3),
      tm 0 2 3 3 2 (3)])

/-- KERNEL-CHECKED chart soundness for flat core 387: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore387 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore387)) den one two three four
      = polyEval chartProduct387 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 388 (degree 4), denominators cleared. -/
def flatCore388 : FlatPoly :=
  [ftm 0 0 0 2 (3),
    ftm 0 0 1 2 (-3),
    ftm 0 1 0 1 (3),
    ftm 0 1 0 2 (-3),
    ftm 0 1 1 0 (1),
    ftm 0 1 1 1 (-5),
    ftm 0 1 1 2 (4),
    ftm 0 1 2 0 (-1),
    ftm 0 1 2 1 (1),
    ftm 0 2 0 1 (-3),
    ftm 0 2 1 0 (-2),
    ftm 0 2 1 1 (5),
    ftm 0 2 2 0 (1),
    ftm 0 3 1 0 (1),
    ftm 1 0 0 1 (5),
    ftm 1 0 0 2 (-10),
    ftm 1 0 0 3 (2),
    ftm 1 0 1 1 (-5),
    ftm 1 0 1 2 (5),
    ftm 1 1 0 1 (-10),
    ftm 1 1 0 2 (7),
    ftm 1 1 1 0 (-1),
    ftm 1 1 1 1 (6),
    ftm 1 2 0 1 (5),
    ftm 1 2 1 0 (1),
    ftm 2 0 0 1 (-5),
    ftm 2 0 0 2 (5),
    ftm 2 1 0 1 (5)]

/-- The certificate-side product for flat core 388: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct388 : Poly :=
  polyMul ([tm 5 0 0 0 0 (1)])
    ([tm 11 0 0 0 0 (3),
      tm 10 1 0 0 0 (3),
      tm 9 1 1 0 0 (6),
      tm 8 1 1 1 0 (3),
      tm 7 1 1 1 1 (6),
      tm 8 2 1 0 0 (6),
      tm 7 2 1 1 0 (3),
      tm 6 2 1 1 1 (3),
      tm 7 2 2 0 0 (3),
      tm 6 2 2 1 0 (6),
      tm 5 2 2 1 1 (9),
      tm 5 2 2 2 0 (3),
      tm 4 2 2 2 1 (6),
      tm 3 2 2 2 2 (3),
      tm 6 3 2 0 0 (3),
      tm 5 3 2 1 0 (3),
      tm 4 3 2 1 1 (3),
      tm 3 3 2 2 1 (5),
      tm 4 3 3 1 0 (3),
      tm 3 3 3 1 1 (3),
      tm 3 3 3 2 0 (3),
      tm 2 3 3 2 1 (6),
      tm 1 3 3 2 2 (3),
      tm 1 3 3 3 1 (5),
      tm 0 3 3 3 2 (5),
      tm 3 4 2 1 1 (1),
      tm 1 4 3 2 1 (1),
      tm 0 4 3 2 2 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 388: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore388 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 4 flatCore388)) den one two three four
      = polyEval chartProduct388 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 389 (degree 3), denominators cleared. -/
def flatCore389 : FlatPoly :=
  [ftm 0 1 2 0 (1),
    ftm 1 0 1 0 (-3),
    ftm 1 0 1 1 (5),
    ftm 1 1 1 0 (4),
    ftm 2 0 0 1 (2)]

/-- The certificate-side product for flat core 389: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct389 : Poly :=
  polyMul ([tm 4 2 1 0 0 (1)])
    (chartCore274)

/-- KERNEL-CHECKED chart soundness for flat core 389: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore389 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore389)) den one two three four
      = polyEval chartProduct389 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 390 (degree 3), denominators cleared. -/
def flatCore390 : FlatPoly :=
  [ftm 0 1 0 1 (3),
    ftm 0 1 1 1 (-4),
    ftm 0 2 1 0 (-1),
    ftm 1 0 0 2 (-2),
    ftm 1 1 0 1 (-5)]

/-- The certificate-side product for flat core 390: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct390 : Poly :=
  polyMul ([tm 6 1 1 0 0 (1)])
    (chartCore275)

/-- KERNEL-CHECKED chart soundness for flat core 390: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore390 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 3 flatCore390)) den one two three four
      = polyEval chartProduct390 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 391 (degree 2), denominators cleared. -/
def flatCore391 : FlatPoly :=
  [ftm 0 1 1 0 (1),
    ftm 1 0 0 1 (5)]

/-- The certificate-side product for flat core 391: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct391 : Poly :=
  polyMul ([tm 5 1 1 0 0 (1)])
    ([tm 0 0 0 1 0 (5),
      tm 0 1 0 0 0 (1)])

/-- KERNEL-CHECKED chart soundness for flat core 391: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore391 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore391)) den one two three four
      = polyEval chartProduct391 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

/-- Flat dictionary core 392 (degree 2), denominators cleared. -/
def flatCore392 : FlatPoly :=
  [ftm 0 1 1 0 (2),
    ftm 1 0 0 1 (1)]

/-- The certificate-side product for flat core 392: the sign-carrying
content and atoms times the chart cores. -/
def chartProduct392 : Poly :=
  polyMul ([tm 5 1 1 0 0 (1)])
    ([tm 0 0 0 1 0 (1),
      tm 0 1 0 0 0 (2)])

/-- KERNEL-CHECKED chart soundness for flat core 392: the emitted chart
polynomials ARE the flat core composed with the barycentric order-chart map. -/
theorem chartSoundnessCore392 (den one two three four : Int) :
    polyEval (polyMul [tm 0 0 0 0 0 (1)]
        (substituteFlatPoly orderChart43210 2 flatCore392)) den one two three four
      = polyEval chartProduct392 den one two three four :=
  polyEval_eq_of_canon_eq _ _ (by decide) den one two three four

end GtzCollarChartSoundnessChart43210
