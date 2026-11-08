import UnifiedEJM.PathCutScore

namespace UnifiedEJM.PathCutScore

/-- 分数、当前交替段奇偶、末位物理颜色。 -/
abbrev ScanState := Nat × Bool × Bool

def scanStep (s : ScanState) (next : Bool) : ScanState :=
  let step := scoreStep s.1 s.2.1 s.2.2 next
  (step.1, step.2, next)

def scanInitial (first : Bool) : ScanState := (0, false, first)

def scanFirstThree (first second third : Bool) : ScanState :=
  scanStep (scanStep (scanInitial first) second) third

/-- 三元元数据的fold与分类所用计分递推是同一个函数。 -/
theorem foldl_scanStep_score (word : List Bool) (s : ScanState) :
    (word.foldl scanStep s).1 = scoreRun s.1 s.2.1 s.2.2 word := by
  induction word generalizing s with
  | nil => rfl
  | cons next rest ih =>
      rw [List.foldl_cons, ih]
      rfl

theorem cutScore_cons_eq_fold (first : Bool) (rest : List Bool) :
    cutScore (first :: rest) = (rest.foldl scanStep (scanInitial first)).1 := by
  exact (foldl_scanStep_score rest (scanInitial first)).symm

/-- 对应初态固定前三位、任意长中央区、固定两尾位的证书布局。 -/
theorem cutScore_three_middle_two (first second third : Bool) (middle : List Bool)
    (penult last : Bool) :
    cutScore (first :: second :: third :: (middle ++ [penult, last])) =
      (scanStep
        (scanStep (middle.foldl scanStep (scanFirstThree first second third)) penult)
        last).1 := by
  rw [cutScore_cons_eq_fold]
  simp only [List.foldl_cons, List.foldl_append, List.foldl_nil, scanFirstThree]

/-- 将有限自动机的已核验末节点元数据接到整个物理颜色字。 -/
theorem cutScore_eq_terminal_score (first second third : Bool) (middle : List Bool)
    (penult last : Bool) (terminal : ScanState)
    (hterminal : terminal = middle.foldl scanStep (scanFirstThree first second third)) :
    cutScore (first :: second :: third :: (middle ++ [penult, last])) =
      (scanStep (scanStep terminal penult) last).1 := by
  rw [hterminal]
  exact cutScore_three_middle_two first second third middle penult last

/-- 完整颜色字分数二时，终止证书应选择分数二的那一分支。 -/
theorem terminal_score_two (first second third : Bool) (middle : List Bool)
    (penult last : Bool) (terminal : ScanState)
    (hterminal : terminal = middle.foldl scanStep (scanFirstThree first second third))
    (hscore : cutScore (first :: second :: third :: (middle ++ [penult, last])) = 2) :
    (scanStep (scanStep terminal penult) last).1 = 2 := by
  rw [← cutScore_eq_terminal_score first second third middle penult last terminal hterminal]
  exact hscore

end UnifiedEJM.PathCutScore
