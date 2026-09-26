import Complexitylib

/-!
# Blueprint consistency check

The blueprint sources under `blueprint/src` link their nodes to the library
with `\lean{...}` and mark formalized statements and proofs with `\leanok`.
This script checks that those links and markers are consistent with the
library, so the blueprint cannot silently claim more than is formalized:

* every `\lean{...}` reference names a declaration of the library;
* a node's statement carries `\leanok` exactly when the node has `\lean`
  references, and is not also marked `\notready`;
* a proof carries `\leanok` only when its statement does, and the proof of a
  linked theorem-like node carries it (the library has no `sorry`, so a
  linked theorem is proved);
* a theorem, lemma, proposition, or corollary cites at least one proof of a
  proposition, not only definitions, and a definition cites at least one
  declaration that is not a proof;
* every node has a label, labels are unique, and every `\uses{...}` and
  `\ref{...}` names an existing label.

Whether a node's prose says exactly what its Lean statement proves is not
checked mechanically; that is a matter of review.

Run from the repository root:

```bash
lake env lean scripts/BlueprintCheck.lean
```

This replaces `checkdecls` without adding a dependency; it parses the LaTeX
sources directly, so it does not need the Python blueprint toolchain.
-/

open Lean Elab Command Meta

namespace BlueprintCheck

/-- `source` with every LaTeX comment removed: an unescaped `%` starts a
comment that runs to the end of its line. -/
def stripComments (source : String) : String :=
  let rec strip : List Char → Bool → List Char
    | [], _ => []
    | c :: cs, escaped =>
      if c == '%' && !escaped then [] else c :: strip cs (c == '\\' && !escaped)
  "\n".intercalate <| (source.splitOn "\n").map fun line => String.ofList (strip line.toList false)

/-- Whether `pattern` occurs in `source`. -/
def occurs (source pattern : String) : Bool :=
  (source.splitOn pattern).length > 1

/-- The argument of every `\macroName{...}` in `source`. -/
def macroArgs (source macroName : String) : List String :=
  (source.splitOn ("\\" ++ macroName ++ "{")).drop 1 |>.map fun rest =>
    toString (rest.takeWhile (· ≠ '}'))

/-- The comma-separated entries of a macro argument. -/
def entries (argument : String) : List String :=
  argument.splitOn "," |>.map (fun entry => toString entry.trimAscii) |>.filter (· ≠ "")

/-- The environments that are blueprint nodes. -/
def nodeEnvironments : List String :=
  ["definition", "theorem", "lemma", "proposition", "corollary"]

/-- A blueprint node: its environment, labels, `\lean` references, markers,
and the body of the proof that immediately follows it, if any. -/
structure Node where
  /-- The source file. -/
  file : System.FilePath
  /-- The environment name, such as `theorem`. -/
  environment : String
  /-- The labels in the statement. -/
  labels : List String
  /-- The names in the statement's `\lean{...}` macros. -/
  references : List String
  /-- Whether the statement carries `\leanok`. -/
  statementOk : Bool
  /-- Whether the statement carries `\notready`. -/
  notReady : Bool
  /-- The body of the proof that follows the statement. -/
  proof : Option String

/-- Whether a node is theorem-like: it states a result rather than a definition. -/
def Node.isTheoremLike (node : Node) : Bool :=
  node.environment != "definition"

/-- A readable name for a node in error messages. -/
def Node.describe (node : Node) : String :=
  let label := node.labels.headD "(no label)"
  s!"{node.environment} {label} ({node.file})"

/-- Every node of one environment in a comment-free source. -/
def nodesOf (file : System.FilePath) (source environment : String) : List Node :=
  let opening := "\\begin{" ++ environment ++ "}"
  let closing := "\\end{" ++ environment ++ "}"
  (source.splitOn opening).drop 1 |>.map fun rest =>
    let pieces := rest.splitOn closing
    let body := pieces.headD ""
    let after := toString (closing.intercalate pieces.tail).trimAsciiStart
    let proof :=
      if after.startsWith "\\begin{proof}" then
        some (((after.drop "\\begin{proof}".length).toString.splitOn "\\end{proof}").headD "")
      else none
    { file, environment
      labels := macroArgs body "label" |>.map (fun label => toString label.trimAscii)
      references := (macroArgs body "lean").flatMap entries
      statementOk := occurs body "\\leanok"
      notReady := occurs body "\\notready"
      proof }

/-- Every `.tex` file under `root`. -/
def texFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let files ← root.walkDir
  return files.filter (·.extension == some "tex")

/-- Run every check over the blueprint sources. -/
def check : CommandElabM Unit := do
  let env ← getEnv
  let files := (← texFiles "blueprint/src").filter (fun file => !file.components.contains "macros")
    |>.qsort (·.toString < ·.toString)
  if files.isEmpty then
    throwError "blueprint check: no .tex files found under blueprint/src"
  let mut sources : Array (System.FilePath × String) := #[]
  for file in files do
    sources := sources.push (file, stripComments (← IO.FS.readFile file))
  let nodes := sources.toList.flatMap fun (file, source) =>
    nodeEnvironments.flatMap (nodesOf file source)
  let mut errors : Array String := #[]
  -- Labels are unique, and every `\uses` and `\ref` names one.
  let mut labels : Std.HashSet String := {}
  for (file, source) in sources do
    for label in macroArgs source "label" do
      let label := toString label.trimAscii
      if labels.contains label then
        errors := errors.push s!"duplicate label `{label}` ({file})"
      labels := labels.insert label
  for (file, source) in sources do
    for target in (macroArgs source "uses").flatMap entries ++
        (macroArgs source "ref").map (fun t => toString t.trimAscii) do
      unless labels.contains target do
        errors := errors.push s!"reference to missing label `{target}` ({file})"
  -- Markers agree with links, and cited declarations have the node's kind.
  let mut checked : Nat := 0
  for node in nodes do
    if node.labels.isEmpty then
      errors := errors.push s!"node without a label: {node.describe}"
    let proofOk := node.proof.any (occurs · "\\leanok")
    if !node.references.isEmpty && !node.statementOk then
      errors := errors.push s!"`\\lean` references without `\\leanok`: {node.describe}"
    if node.references.isEmpty && node.statementOk then
      errors := errors.push s!"`\\leanok` without `\\lean` references: {node.describe}"
    if node.notReady && node.statementOk then
      errors := errors.push s!"`\\notready` on a formalized node: {node.describe}"
    if proofOk && !node.statementOk then
      errors := errors.push s!"proof marked `\\leanok` but its statement is not: {node.describe}"
    if node.isTheoremLike && !node.references.isEmpty && node.proof.isSome && !proofOk then
      errors := errors.push s!"proof of a linked result lacks `\\leanok`: {node.describe}"
    let mut proofs : Nat := 0
    let mut others : Nat := 0
    for reference in node.references do
      checked := checked + 1
      match env.find? reference.toName with
      | none => errors := errors.push s!"missing declaration `{reference}`: {node.describe}"
      | some info =>
        if ← liftTermElabM (isProp info.type) then proofs := proofs + 1 else others := others + 1
    if node.isTheoremLike && others > 0 && proofs == 0 then
      errors := errors.push s!"result cites only definitions, no proof: {node.describe}"
    if !node.isTheoremLike && proofs > 0 && others == 0 then
      errors := errors.push s!"definition cites only proofs: {node.describe}"
  unless errors.isEmpty do
    throwError m!"blueprint check: {errors.size} problems:" ++
      m!"{String.join (errors.toList.map ("\n  " ++ ·))}"
  logInfo (m!"blueprint check: {nodes.length} nodes and {checked} `\\lean` references in " ++
    m!"{files.size} files are consistent")

end BlueprintCheck

run_cmd BlueprintCheck.check
