import UnifiedEJM
import Lean.Util.CollectAxioms

open Lean Elab Command

-- 按所属模块选择全部本地声明，同时包含私有辅助证明和自动生成声明。
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx]!
      if owner.toString.startsWith "UnifiedEJM" || owner.toString.startsWith "OddEJM" then
        names := names.push name
  names := names.qsort Name.lt
  let mut theorems : Nat := 0
  let mut nonstandard : Nat := 0
  for name in names do
    let info ← getConstInfo name
    if info.isTheorem then
      theorems := theorems + 1
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        nonstandard := nonstandard + 1
        logError m!"NONSTANDARD {name}: {axiomName}"
    logInfo m!"AUDIT {name}: {axioms.toList}"
  logInfo m!"TOTAL declarations={names.size} theorems={theorems} nonstandard={nonstandard}"
