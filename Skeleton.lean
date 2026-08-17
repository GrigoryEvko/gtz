import Skeleton.Report
import Skeleton.Assembly
import Skeleton.Structure

/-!
# `Skeleton` -- the GTZ obligation scaffold

Library root.  `Skeleton.Report` transitively imports everything else, and
elaborating it prints the current frontier and runs the anti-drift gate, so
building this target IS the frontier check.  `Skeleton.Assembly` carries the
endgame composition map and its own exact-frontier gates, so building this
target also checks that every banked composition still reaches exactly the
obligations it claims.

This library is deliberately NOT under module root `Gtz`.  `Gtz/Audit.lean` ends
with a sweep that enumerates every theorem whose module root is `Gtz` and fails
the build if any reaches an axiom outside `{propext, Classical.choice,
Quot.sound}`.  The scaffold's obligation axioms must never be laundered through
that guarantee.  Two independent things keep them out:

* the sweep filters its roots by module root, and `Skeleton` is not `Gtz`;
* the import graph runs one way only.  `Skeleton.Obligations` imports `Gtz`, so
  no `Gtz` module can import `Skeleton` without a cycle.  A `Gtz` theorem
  therefore cannot reach a `Skeleton` axiom at all, and if anyone ever wired one
  up, the sweep's closure walk -- which is NOT filtered by module root -- would
  catch it and fail the build.

So `Gtz` remains exactly as strong as it was: everything it proves outright it
still proves outright, and everything conditional is conditional on a named
axiom that prints on every build.
-/
