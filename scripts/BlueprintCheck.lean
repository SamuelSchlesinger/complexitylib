import Complexitylib

/-!
# Blueprint declaration check

Every `\lean{...}` reference in the blueprint sources under `blueprint/src`
must name a declaration of the library. This keeps the blueprint's
"formalized" markers tied to real Lean declarations: renaming or deleting a
referenced declaration fails CI instead of silently leaving a dangling link.

Run from the repository root:

```bash
lake env lean scripts/BlueprintCheck.lean
```

This replaces `checkdecls` without adding a dependency; it parses the LaTeX
sources directly, so it does not need the Python blueprint toolchain.
-/

open Lean Elab Command

/-- The comma-separated names inside every `\lean{...}` macro of `source`. -/
def leanReferences (source : String) : List String :=
  (source.splitOn "\\lean{").drop 1 |>.flatMap fun rest =>
    (toString (rest.takeWhile (· ≠ '}'))).splitOn "," |>.map (fun name => toString name.trimAscii)
      |>.filter (· ≠ "")

/-- Every `.tex` file under `root`. -/
def texFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let files ← root.walkDir
  return files.filter (·.extension == some "tex")

run_cmd do
  let env ← getEnv
  let files ← texFiles "blueprint/src"
  if files.isEmpty then
    throwError "blueprint check: no .tex files found under blueprint/src"
  let mut checked : Nat := 0
  let mut missing : Array String := #[]
  for file in files.qsort (·.toString < ·.toString) do
    let source ← IO.FS.readFile file
    for reference in leanReferences source do
      checked := checked + 1
      unless env.contains reference.toName do
        missing := missing.push s!"\n  `{reference}` ({file})"
  unless missing.isEmpty do
    throwError m!"blueprint check: {missing.size} referenced declarations do not exist:" ++
      m!"{String.join missing.toList}"
  logInfo m!"blueprint check: all {checked} `\\lean` references in {files.size} files exist"
