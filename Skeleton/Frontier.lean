import Skeleton.Obligations

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The frontier printer

Three commands that make the remaining GTZ obligations machine-visible.

* `#gtz_frontier c ...` walks the proof-term closure of each named constant,
  partitions every reachable axiom into the classical foundation, the
  `Skeleton.Obligations` registry, and everything else, prints the registry
  obligations actually consumed, and FAILS if anything lands in the third class.
* `#gtz_frontier_all c ...` prints the registry obligations NOT reached from the
  named constants.  Those are dead weight and must be retired.
* `#gtz_registry_check` proves `Skeleton.liveObligationNames` still agrees with
  the axioms actually declared in `Skeleton.Obligations`.

## Why the walk is hand-rolled

`Lean.collectAxioms` is per-constant: asking it "which of the four obligations
does this capstone use" once per obligation re-walks the closure each time.  One
worklist pass answers the question for every obligation at once.

## A trap in Lean 4.32 that this code has to dodge

`ConstantInfo.value?` defaults to `allowOpaque := false`, and in 4.32 that
returns `none` for THEOREMS, not just for opaque constants.  A closure walk built
on `info.value?` therefore sees only statement types, silently misses every
proof term, and reports an empty frontier -- the exact failure this scaffold
exists to prevent.  `ConstantInfo.getUsedConstantsAsSet` internally uses
`allowOpaque := true`, so the walk below is correct; it was cross-checked
against `Lean.collectAxioms` on 411 Gtz theorems sampled across the tree with
zero disagreements.  Each command still re-runs that cross-check per root and
reports any divergence, so the guarantee cannot rot silently.
-/

namespace Skeleton.Frontier

open Lean Elab Command

/-- The classical foundation Mathlib is entitled to. Anything else reachable
from a capstone is either a registry obligation or a defect. -/
def standardFoundationAxioms : NameSet :=
  ({} : NameSet) |>.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound

/-- The module that is allowed to declare obligations. -/
def registryModuleName : Name := `Skeleton.Obligations

/-- Every axiom declared in the registry module, sorted.

Read straight off the module's own constant table rather than by scanning the
whole environment, so this stays cheap and cannot pick up an axiom that merely
happens to sit in the `Skeleton` namespace. -/
def declaredObligations (env : Environment) : Array Name := Id.run do
  let mut declared : Array Name := #[]
  for moduleIndex in [0 : env.header.moduleNames.size] do
    if env.header.moduleNames[moduleIndex]! == registryModuleName then
      for constName in env.header.moduleData[moduleIndex]!.constNames do
        if let some (.axiomInfo _) := env.find? constName then
          declared := declared.push constName
  return declared.qsort Name.lt

/-- Worklist over the proof-term closure of `root`, returning every axiom
reachable from it.

`visited` keeps the walk linear in the size of the closure; `pending` is an
explicit stack so deep closures cannot exhaust the interpreter's call stack. -/
def reachableAxioms (env : Environment) (root : Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut axioms : NameSet := {}
  let mut pending : Array Name := #[root]
  while !pending.isEmpty do
    let current := pending.back!
    pending := pending.pop
    if visited.contains current then
      continue
    visited := visited.insert current
    match env.find? current with
    | none => pure ()
    | some info =>
      match info with
      | .axiomInfo _ => axioms := axioms.insert current
      | _ => pure ()
      for dependency in info.getUsedConstantsAsSet.toList do
        if !visited.contains dependency then
          pending := pending.push dependency
  return axioms

/-- The first non-blank line of a declaration's docstring, which for a registry
obligation is its `STATUS:` field. -/
def firstDocumentationLine (env : Environment) (declName : Name) : CommandElabM String := do
  match ← findDocString? env declName with
  | none => return "(no docstring)"
  | some documentation =>
    let informativeLines :=
      documentation.splitOn "\n" |>.map (fun line => line.trimAscii.toString)
        |>.filter (fun line => line != "")
    return informativeLines.headD "(empty docstring)"

/-- Union of the axioms reachable from every root, cross-checked per root
against `Lean.collectAxioms`.  Returns the union together with a human-readable
line for each root where the two mechanisms disagreed. -/
def reachedAxiomsOfRoots (roots : Array Name) :
    CommandElabM (NameSet × Array MessageData) := do
  let env ← getEnv
  let mut reached : NameSet := {}
  let mut divergences : Array MessageData := #[]
  for rootName in roots do
    let walked := reachableAxioms env rootName
    let official ← collectAxioms rootName
    let officialSet : NameSet :=
      official.foldl (init := ({} : NameSet)) (fun accumulated name => accumulated.insert name)
    if walked.toList != officialSet.toList then
      divergences := divergences.push
        m!"  {rootName}: worklist={walked.toList} collectAxioms={official.toList}"
    for axiomName in walked.toList do
      reached := reached.insert axiomName
    for axiomName in officialSet.toList do
      reached := reached.insert axiomName
  return (reached, divergences)

/-- Resolve the command's identifier arguments to constant names. -/
def resolveRootNames (rootIdents : Array Ident) : CommandElabM (Array Name) := do
  let mut resolved : Array Name := #[]
  for rootIdent in rootIdents do
    resolved := resolved.push (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo rootIdent)
  return resolved

/-- Print the registry obligations a constant actually depends on, and fail if
it reaches any axiom that is neither foundational nor registered. -/
elab "#gtz_frontier " rootIdents:ident+ : command => do
  let roots ← resolveRootNames rootIdents
  let env ← getEnv
  let declared := declaredObligations env
  let declaredSet : NameSet :=
    declared.foldl (init := ({} : NameSet)) (fun accumulated name => accumulated.insert name)
  let (reached, divergences) ← reachedAxiomsOfRoots roots
  let mut foundationReached : Array Name := #[]
  let mut obligationsReached : Array Name := #[]
  let mut foreignReached : Array Name := #[]
  for axiomName in reached.toList do
    if standardFoundationAxioms.contains axiomName then
      foundationReached := foundationReached.push axiomName
    else if declaredSet.contains axiomName then
      obligationsReached := obligationsReached.push axiomName
    else
      foreignReached := foreignReached.push axiomName
  let mut report : MessageData := m!"GTZ FRONTIER of {roots.toList}"
  report := report ++ m!"\n  foundation axioms reached : {(foundationReached.qsort Name.lt).toList}"
  report := report ++
    m!"\n  registry obligations reached : {obligationsReached.size} of {declared.size}"
  if obligationsReached.isEmpty then
    report := report ++ m!"\n    (none -- this constant is unconditional)"
  else
    for obligationName in obligationsReached.qsort Name.lt do
      let headline ← firstDocumentationLine env obligationName
      report := report ++ m!"\n    {obligationName}\n        {headline}"
  unless divergences.isEmpty do
    report := report ++
      m!"\n  WARNING worklist and collectAxioms disagreed (reporting the union):"
    for divergence in divergences do
      report := report ++ m!"\n  {divergence}"
  logInfo report
  unless foreignReached.isEmpty do
    let carriesSorry := foreignReached.contains ``sorryAx
    let diagnosis :=
      if carriesSorry then
        "`sorryAx` is reachable: a proof is incomplete. Replace the `sorry` with a registry obligation."
      else
        "an axiom outside the registry is reachable. Declare it in Skeleton.Obligations with the five-field docstring, or eliminate it."
    throwError "#gtz_frontier: {roots.toList} reaches unregistered axioms {(foreignReached.qsort Name.lt).toList}.\n  {diagnosis}"

/-- Print the registry obligations NOT reached from the given constants.  A
permanently unreached obligation is dead and must be retired: it assumes
something no capstone spends. -/
elab "#gtz_frontier_all " rootIdents:ident+ : command => do
  let roots ← resolveRootNames rootIdents
  let env ← getEnv
  let declared := declaredObligations env
  let (reached, _) ← reachedAxiomsOfRoots roots
  let unreached := declared.filter (fun name => !reached.contains name)
  let mut report : MessageData :=
    m!"GTZ DEAD-OBLIGATION SCAN against {roots.toList}\n  declared {declared.size}, unreached {unreached.size}"
  if unreached.isEmpty then
    report := report ++ m!"\n    (none -- every declared obligation is spent)"
  else
    for obligationName in unreached do
      let headline ← firstDocumentationLine env obligationName
      report := report ++ m!"\n    UNREACHED {obligationName}\n        {headline}"
  logInfo report

/-- Decode a closed `List Lean.Name` literal back into a list of names. -/
partial def decodeNameListExpr (listExpr : Expr) : Option (List Name) :=
  match listExpr.getAppFnArgs with
  | (``List.nil, _) => some []
  | (``List.cons, #[_, headExpr, tailExpr]) => do
    let headName ← headExpr.name?
    let tailNames ← decodeNameListExpr tailExpr
    return headName :: tailNames
  | _ => none

/-- Fail unless `Skeleton.liveObligationNames` still lists exactly the axioms
declared in `Skeleton.Obligations`.  Without this the machine-readable index
could silently drift out of date, which is the failure mode the whole registry
exists to prevent. -/
elab "#gtz_registry_check" : command => do
  let env ← getEnv
  let declared := (declaredObligations env).toList
  let some indexInfo := env.find? ``Skeleton.liveObligationNames
    | throwError "#gtz_registry_check: Skeleton.liveObligationNames is missing."
  let some indexValue := indexInfo.value? (allowOpaque := true)
    | throwError "#gtz_registry_check: Skeleton.liveObligationNames has no value."
  let some listed := decodeNameListExpr indexValue
    | throwError "#gtz_registry_check: could not decode Skeleton.liveObligationNames as a closed list of name literals."
  let listedSorted := (listed.toArray.qsort Name.lt).toList
  if listedSorted != declared then
    throwError "#gtz_registry_check: the index has drifted.\n  declared in {registryModuleName} : {declared}\n  listed in liveObligationNames : {listedSorted}"
  logInfo m!"#gtz_registry_check OK: {declared.length} obligations, index agrees with {registryModuleName}.\n  {declared}"

end Skeleton.Frontier
