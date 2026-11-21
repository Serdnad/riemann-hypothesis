import Lean

/-!
Recheck a compiled theorem's dependency closure against Mathlib. Each declaration
outside that base is passed through the kernel, and the resulting theorem type
must match the input type. The optional output path saves the checked slice.

From the Lean package directory, run

  lake env lean --tstack=400000 --run ../tools/ReplayProofSlice.lean MODULE THEOREM

Use `--batch TARGETS.tsv` to check several module and declaration pairs. Put one
tab-separated pair on each line. Each replay runs in its own Lean process to
release the imported environment before starting the next target.

The source module must already be compiled. Nested inductives and axioms
outside Mathlib are reported as errors.
-/

open Lean

def findChecked (env : Environment) (name : Name) : IO ConstantInfo := do
  let some info := env.checked.get.find? name
    | throw (IO.userError s!"Unknown declaration {name}")
  return info

def inductiveDeclaration (env : Environment) (name : Name) : IO Declaration := do
  let .inductInfo info ← findChecked env name
    | throw (IO.userError s!"{name} is not an inductive type")
  if info.numNested != 0 then
    throw (IO.userError s!"Nested inductive replay is unsupported: {name}")
  let types ← info.all.mapM fun typeName => do
    let .inductInfo type ← findChecked env typeName
      | throw (IO.userError s!"Missing mutual inductive {typeName}")
    let ctors ← type.ctors.mapM fun ctorName => do
      let .ctorInfo ctor ← findChecked env ctorName
        | throw (IO.userError s!"Missing constructor {ctorName}")
      pure ({ name := ctor.name, type := ctor.type } : Constructor)
    pure ({ name := type.name, type := type.type, ctors } : InductiveType)
  return .inductDecl info.levelParams info.numParams types info.isUnsafe

def originalDeclaration (env : Environment) (name : Name) : IO Declaration := do
  match ← findChecked env name with
  | .thmInfo info => pure (.thmDecl info)
  | .opaqueInfo info => pure (.opaqueDecl info)
  | .axiomInfo _ => throw (IO.userError s!"New axiom outside the Mathlib base: {name}")
  | .inductInfo info => inductiveDeclaration env info.name
  | .ctorInfo info => inductiveDeclaration env info.induct
  | .recInfo info =>
    let some inductiveName := info.all.head?
      | throw (IO.userError s!"No inductive type for recursor {name}")
    inductiveDeclaration env inductiveName
  | .defnInfo info =>
    if info.all.length ≤ 1 then
      pure (.defnDecl info)
    else
      let group ← info.all.mapM fun defnName => do
        let .defnInfo item ← findChecked env defnName
          | throw (IO.userError s!"Missing mutual definition {defnName}")
        pure item
      pure (.mutualDefnDecl group)
  | .quotInfo _ => throw (IO.userError "Quotient primitives must come from the base environment")

def typeAndValueReferences (decl : Declaration) : IO NameSet := do
  let refs ← IO.mkRef ({} : NameSet)
  decl.forExprM fun expr =>
    expr.forEach fun e =>
      match e with
      | .const name _ | .proj name _ _ => refs.modify (·.insert name)
      | _ => pure ()
  refs.get

structure ReplayState where
  env : Kernel.Environment
  inProgress : NameSet := {}
  checked : Array Name := #[]
  owners : NameSet := {}

def kernelError : Kernel.Exception → String
  | .unknownConstant _ n => s!"unknown constant {n}"
  | .alreadyDeclared _ n => s!"duplicate declaration {n}"
  | .declTypeMismatch _ d _ => s!"type mismatch in {d.getTopLevelNames}"
  | .deterministicTimeout => "deterministic timeout"
  | .excessiveMemory => "excessive memory"
  | .deepRecursion => "deep recursion"
  | .other msg => msg
  | _ => "kernel type checking failed"

partial def replay (source : Environment) (target : Name) : StateT ReplayState IO Unit := do
  if (← get).env.find? target |>.isSome then return
  if (← get).inProgress.contains target then
    throw (IO.userError s!"Dependency cycle at {target}")
  let decl ← originalDeclaration source target
  let names := NameSet.ofList decl.getNames
  modify fun state => { state with inProgress := state.inProgress ++ names }
  for dependency in (← typeAndValueReferences decl).toArray do
    unless names.contains dependency do
      replay source dependency
  let state ← get
  match state.env.addDeclCore 0 8192 decl none with
  | .error e => throw (IO.userError s!"At {target}: {kernelError e}")
  | .ok env =>
    let mut owners := state.owners
    for name in decl.getTopLevelNames do
      if let some mod := source.getModuleIdxFor? name |>.bind (source.header.moduleNames[·.toNat]?) then
        owners := owners.insert mod
    set { state with
      env := env
      owners := owners
      checked := state.checked ++ decl.getNames.toArray
      inProgress := names.toArray.foldl (fun names name => names.erase name) state.inProgress }

def checkTarget (sourceModule theoremName : String)
    (output : Option System.FilePath := none) : IO Unit := do
  initSearchPath (← findSysroot)
  let source ← importModules #[{ module := sourceModule.toName }] {}
  let base ← importModules #[{ module := `Mathlib }] {}
  let (_, state) ← (replay source theoremName.toName).run { env := base.checked.get }
  let some result := state.env.find? theoremName.toName
    | throw (IO.userError "Target missing after replay")
  let original ← findChecked source theoremName.toName
  unless result.type == original.type do
    throw (IO.userError "The target type changed")
  let baseModules := NameSet.ofList base.header.moduleNames.toList
  let imported := source.header.moduleNames.filter fun name => !baseModules.contains name
  IO.println s!"Kernel replay passed for {theoremName} from {sourceModule}"
  IO.println s!"Original modules loaded outside Mathlib: {imported.size}"
  IO.println s!"Fresh declarations checked: {state.checked.size}"
  IO.println s!"Original project modules supplying declarations: {state.owners.size}"
  IO.println "Base imports: Mathlib. No additional axioms were introduced."
  for mod in state.owners.toArray.qsort Name.lt do
    IO.println s!"  {mod}"
  (← IO.getStdout).flush
  if let some output := output then
    let some stem := output.fileStem
      | throw (IO.userError "Missing output module name")
    let constants ← state.checked.mapM fun name => do
      let some info := state.env.find? name
        | throw (IO.userError s!"Missing replayed declaration {name}")
      return info
    saveModuleData output stem.toName {
      isModule := false
      imports := #[{ module := `Mathlib }]
      constNames := state.checked
      constants
      extraConstNames := #[]
      entries := #[]
    }

elab "replaySourceFile" : term => return mkStrLit (← getFileName)

def checkBatch (path : System.FilePath) : IO UInt32 := do
  let lean ← IO.appPath
  let mut exitCode := 0
  for line in (← IO.FS.readFile path).splitOn "\n" do
    let line := line.trimAscii.toString
    unless line.isEmpty || line.startsWith "#" do
      match line.splitOn "\t" with
      | [sourceModule, theoremName] =>
        let child ← IO.Process.spawn {
          cmd := lean.toString
          args := #["--tstack=400000", "--run", replaySourceFile, sourceModule, theoremName]
          stdin := .null
        }
        let status ← child.wait
        if status != 0 then
          IO.eprintln s!"Kernel replay failed for {theoremName} from {sourceModule} (exit {status})"
          exitCode := 1
      | _ =>
        IO.eprintln s!"Expected a tab-separated module and declaration: {line}"
        exitCode := 1
  return exitCode

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--batch", path] => checkBatch ⟨path⟩
  | [sourceModule, theoremName] =>
    checkTarget sourceModule theoremName
    return 0
  | [sourceModule, theoremName, output] =>
    checkTarget sourceModule theoremName (some ⟨output⟩)
    return 0
  | _ =>
    throw (IO.userError
      "usage: ReplayProofSlice.lean SOURCE_MODULE THEOREM [OUTPUT.olean] | --batch TARGETS.tsv")
