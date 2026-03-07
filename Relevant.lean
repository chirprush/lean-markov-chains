import Lean
import Lean.Data.Json.FromToJson
import Batteries.Data.List.Basic

open Lean

inductive AST where
| num (value : Nat)
| str (value : String)
| bruijn (idx : Nat)
| ident (name : String)
| sort
| apply (fn : AST) (args : List AST)
| proj (value : AST) (idx : Nat)
| letin (type : AST) (value : AST) (body : AST)
| lambda (type : AST) (body : AST)
| universal (type : AST) (body : AST)
| error
deriving Inhabited, ToJson

structure UserThmInfo where
  name : String
  conclusion : AST
  dependencies : List String
  deriving ToJson

structure ExtThmInfo where
  name : String
  conclusion : AST
  deriving ToJson

def exprToAST (e : Expr) : Option AST :=
  match e with
    | .bvar n => return AST.bruijn n
    | .fvar _ => none
    | .mvar _ => none
    | .mdata _ _ => none
    | .sort _ => return AST.sort
    | .const name _ => return AST.ident name.toString
    | .app fn arg => do
      let fn ← exprToAST fn
      let arg ← exprToAST arg
      match fn with
        | .apply inner args => return AST.apply inner (arg::args)
        | other => return AST.apply other [arg]
    | .lam _ type body _ => do
      let type ← exprToAST type
      let body ← exprToAST body
      return AST.lambda type body
    | .forallE _ type body _ => do
      let type ← exprToAST type
      let body ← exprToAST body
      return AST.universal type body
    | .letE _ type value body _ => do
      let type ← exprToAST type
      let value ← exprToAST value
      let body ← exprToAST body
      return AST.letin type value body
    | .lit (.natVal n) => return AST.num n
    | .lit (.strVal s) => return AST.str s
    | .proj _ idx value => do
      let value ← exprToAST value
      return AST.proj value idx

def debugAST (a : AST) (level := 0) : String :=
  match a with
    | .num value => value.repr
    | .str value => s!"\"{value}\""
    | .bruijn idx => s!"`{idx}"
    | .ident name => s!"{name}"
    | .sort => s!"sort"
    | .apply fn args =>
      let argStrings := List.map debugAST args
      s!"({debugAST fn} {" ".intercalate argStrings})"
    | .proj value idx => s!"{debugAST value}.{idx}"
    | .letin type value body => s!"(let `{level} : {debugAST type level} := {debugAST value level}; {debugAST body (level + 1)})"
    | .lambda type body => s!"(λ `{level} : {debugAST type level}, {debugAST body (level + 1)})"
    | .universal type body => s!"(∀ `{level} : {debugAST type level}, {debugAST body (level + 1)})"
    | .error => "error!"

-- This is hopefully reasonably efficient
def constantToThm (env : Environment) (c : ConstantInfo) : Option TheoremVal :=
  match c with
    | .thmInfo v => if (Name.isInternal v.name) then none else do
        let idx ← env.getModuleIdxFor? v.name
        let moduleName ← env.header.moduleNames[idx]?
        if "Init".isPrefixOf moduleName.toString then none else return v
    | _ => none

-- TODO: Maybe make this into a set first? We really shouldn't be having repeats
-- that don't make sense
def exprGetDependencies (env : Environment) (e : Expr) : Std.HashSet String :=
  match e with
    | .const name _ =>
      match (do constantToThm env (← env.constants.find? name)) with
        | some _ => Std.HashSet.ofList [name.toString]
        | none => Std.HashSet.ofList []
    | .app fn arg => (exprGetDependencies env fn).union (exprGetDependencies env arg)
    | .lam _ type body _ => (exprGetDependencies env type).union (exprGetDependencies env body)
    | .forallE _ type body _ => (exprGetDependencies env type).union (exprGetDependencies env body)
    | .letE _ type value body _ => ((exprGetDependencies env type).union (exprGetDependencies env value)).union (exprGetDependencies env body)
    | .proj _ _ value => (exprGetDependencies env value)
    | _ => Std.HashSet.ofList []

unsafe def main : IO Unit := do
  let leanPath ← match (← IO.getEnv "LEAN_PATH") with
    | some p => pure (System.SearchPath.parse p)
    | none => pure []

  initSearchPath (← findSysroot) leanPath

  let importNames := #[
    `LeanMarkovChains,
    `LeanMarkovChains.Basic,
    `LeanMarkovChains.Irreducible,
    `LeanMarkovChains.Lazy,
    `LeanMarkovChains.Period,
    `LeanMarkovChains.Reversible,
    `LeanMarkovChains.Spectral,
    `LeanMarkovChains.StationaryDistribution
  ]

  let imports : Array Import := Array.map (fun n => { module := n }) importNames

  withImportModules imports {} fun env => do
    let ctx : Core.Context := { fileName := "<relevant>", fileMap := default }
    let state : Core.State := { env := env }

    let coreAction := do
      let metaAction : MetaM (IO Unit) := pure do
        let userModules := importNames.toList
        let extModules := List.filter (fun name => not (userModules.contains name)) env.header.moduleNames.toList

        let userHandle ← IO.FS.Handle.mk ⟨"userInfo.json"⟩ IO.FS.Mode.write
        let extHandle ← IO.FS.Handle.mk ⟨"extInfo.json"⟩ IO.FS.Mode.write

        for uMod in userModules do
          let idx := Option.get! (env.getModuleIdx? uMod)

          for const in env.header.moduleData[idx]!.constants do
            match constantToThm env const with
              | some v =>
                let thmInfo : UserThmInfo := {
                  name := v.name.toString,
                  conclusion := Option.get! (exprToAST v.type)
                  dependencies := (exprGetDependencies env v.value).toList
                }

                userHandle.putStrLn (toJson thmInfo).compress
              | none => pure ()

        -- As of now, this is really not working well but that's because I
        -- import the entirety of Mathlib in my project, which definitely isn't
        -- normal I would hope.
        for eMod in extModules do
          let idx := Option.get! (env.getModuleIdx? eMod)

          for const in env.header.moduleData[idx]!.constants do
            match constantToThm env const with
              | some v =>
                let extInfo : ExtThmInfo := {
                  name := v.name.toString,
                  conclusion := (exprToAST v.type).getD AST.error
                }

                extHandle.putStrLn (toJson extInfo).compress
              | none => pure ()

        userHandle.flush
        extHandle.flush

        -- let userThms := extractThms env userModules
        -- let extThms := extractThms env extModules

        -- return extThms.length

        -- let userInfo : List UserThmInfo := List.map
        --   (fun info : TheoremVal => {
        --     name := info.name.toString,
        --     conclusion := Option.get! (exprToAST info.type),
        --     dependencies := (exprGetDependencies env info.value).toList
        --   })
        --   userThms

        -- let extInfo : List ExtThmInfo := List.map
        --   (fun info : TheoremVal => {
        --     name := info.name.toString,
        --     conclusion := (exprToAST info.type).getD (AST.str "error")
        --   })
        --   extThms

        -- return Json.mkObj [("userThms", userInfo.toJson), ("extThms", extInfo.toJson)]
        -- let modules ← extractModuleNames env
        -- return (env.constants.toList.length, modules.length)

      Meta.MetaM.run' metaAction

    try
      let (result, _) ← coreAction.toIO ctx state
      result
    catch e =>
      IO.println s!"Error: {e}"
