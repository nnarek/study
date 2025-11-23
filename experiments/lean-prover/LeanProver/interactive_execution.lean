import Lean.Elab.Frontend
import Lean.Replay

open Lean Elab


/-- copied from lean4/tests/pkg/frontend/Frontend/Compile.lean -/
unsafe def execCode (input : String) (intEnv: Option Environment := none) (initializers := false)  :
    IO (Environment × MessageLog) := do
  let fileName   := "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  if initializers then enableInitializersExecution
  
  let s ← match intEnv with
          | none => do
                      let (header, parserState, messages) ← Parser.parseHeader inputCtx
                      let (env, messages) ← processHeader header {} messages inputCtx
                      IO.processCommands inputCtx parserState (Command.mkState env messages {}) 
          | some env => IO.processCommands inputCtx default (Command.mkState env default {}) 

  pure ⟨s.commandState.env, s.commandState.messages⟩ 

def saveModule (env : Environment) (path : System.FilePath) (key : Name := by exact decl_name%)  : IO Unit :=
  saveModuleData path key (unsafe unsafeCast (env.header.imports, env.constants.map₂))

/-- from leanprover-community/repl/REPL/Lean/Environment.lean -/
unsafe def loadModule (path : System.FilePath) : IO Environment := do
  let (moduleData, region) ← readModuleData path
  
  let moduleData : Array Import × PHashMap Name ConstantInfo := unsafeCast moduleData

  let ((imports, map₂), region)  ← pure (moduleData, region)
  let env ← importModules imports {} 0 (loadExts := true)
  return (← env.replay (Std.HashMap.ofList map₂.toList), region).1

#eval show IO _ from do
  let r ← execCode "import Mathlib\ndef a := 1\n#check 1" 
  dbg_trace ← r.2.toList[0]!.toString

  let r ← execCode "#check a\n#check 5\n" r.1 
  dbg_trace ← r.2.toList.foldrM (fun s res => do return (← s.toString) ++ res) ""

  let filePath := System.FilePath.mk "" / "tmp" / "tmp_file" |>.withExtension "olean" -- same as /tmp/tmp_file.olean
  saveModule r.1 filePath
  let env ← loadModule filePath
  let r ← execCode "#print a\n" env
   dbg_trace ← r.2.toList[0]!.toString
