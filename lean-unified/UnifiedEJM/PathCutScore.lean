import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Count
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

namespace UnifiedEJM.PathCutScore

/-- 与有限状态证书一致的截断跨边计分；同色边重置交替段奇偶。 -/
def scoreStep (score : Nat) (odd old next : Bool) : Nat × Bool :=
  if old = next then (min score 2, false)
  else (min (score + if odd then 0 else 1) 2, !odd)

/-- 从已处理末位开始读取剩余物理颜色。 -/
def scoreRun (score : Nat) (odd old : Bool) : List Bool → Nat
  | [] => score
  | next :: rest =>
      let step := scoreStep score odd old next
      scoreRun step.1 step.2 next rest

/-- 未截断的同一计分递推，方便自然数归纳。 -/
def tailScore (old odd : Bool) : List Bool → Nat
  | [] => 0
  | next :: rest =>
      if old = next then tailScore next false rest
      else (if odd then 0 else 1) + tailScore next (!odd) rest

def rawScore : List Bool → Nat
  | [] => 0
  | first :: rest => tailScore first false rest

def cutScore : List Bool → Nat
  | [] => 0
  | first :: rest => scoreRun 0 false first rest

theorem scoreRun_eq_min (word : List Bool) (score : Nat) (odd old : Bool)
    (hs : score ≤ 2) :
    scoreRun score odd old word = min (score + tailScore old odd word) 2 := by
  induction word generalizing score odd old with
  | nil => simp [scoreRun, tailScore, Nat.min_eq_left hs]
  | cons next rest ih =>
      by_cases h : old = next
      · simp only [scoreRun, scoreStep, h, ite_true, ite_false]
        rw [ih _ _ _ (Nat.min_le_right _ _)]
        simp [tailScore, Nat.min_eq_left hs]
      · simp only [scoreRun, scoreStep, h, ite_true, ite_false]
        rw [ih _ _ _ (Nat.min_le_right _ _)]
        cases odd <;> simp [tailScore, h] <;> omega

theorem cutScore_eq_min (word : List Bool) :
    cutScore word = min (rawScore word) 2 := by
  cases word with
  | nil => rfl
  | cons first rest =>
      simpa [cutScore, rawScore] using scoreRun_eq_min rest 0 false first (by omega)

theorem cutScore_le_one_iff (word : List Bool) :
    cutScore word ≤ 1 ↔ rawScore word ≤ 1 := by
  rw [cutScore_eq_min]
  omega

theorem cutScore_eq_zero_iff (word : List Bool) :
    cutScore word = 0 ↔ rawScore word = 0 := by
  rw [cutScore_eq_min]
  omega

private theorem ne_bool_eq_not {a b : Bool} (h : a ≠ b) : b = !a := by
  cases a <;> cases b <;> simp_all

/-- 交替段偶位置之后，零增量迫使剩余站点全同色。 -/
theorem tailScore_zero_uniform (word : List Bool) (a : Bool)
    (h : tailScore a false word = 0) : word = List.replicate word.length a := by
  induction word generalizing a with
  | nil => rfl
  | cons b rest ih =>
      by_cases hab : a = b
      · subst b
        have ht : tailScore a false rest = 0 := by simpa [tailScore] using h
        simpa [List.replicate_succ] using congrArg (List.cons a) (ih a ht)
      · simp [tailScore, hab] at h

/-- 交替段奇位置之后，零增量至多允许立即再跨一次。 -/
theorem tailScore_odd_zero (word : List Bool) (a : Bool)
    (h : tailScore a true word = 0) :
    (∃ k, word = List.replicate k a) ∨
      (∃ k, word = (!a) :: List.replicate k (!a)) := by
  cases word with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons b rest =>
      by_cases hab : a = b
      · subst b
        have ht : tailScore a false rest = 0 := by simpa [tailScore] using h
        have hu := tailScore_zero_uniform rest a ht
        refine Or.inl ⟨rest.length + 1, ?_⟩
        simpa [List.replicate_succ] using congrArg (List.cons a) hu
      · have hb : b = !a := ne_bool_eq_not hab
        have ht : tailScore b false rest = 0 := by simpa [tailScore, hab] using h
        have hu := tailScore_zero_uniform rest b ht
        exact Or.inr ⟨rest.length, by rw [hb] at hu ⊢; rw [hu]; simp⟩

/-- 第一次跨边前为常色前缀；其后只有常色尾段或立即返回原色。 -/
theorem low_tail_forms (word : List Bool) (a : Bool)
    (h : tailScore a false word ≤ 1) :
    (∃ k l, a :: word = List.replicate (k + 1) a ++ List.replicate l (!a)) ∨
      (∃ k l, a :: word =
        List.replicate (k + 1) a ++ [!a] ++ List.replicate l a) := by
  induction word generalizing a with
  | nil => exact Or.inl ⟨0, 0, by simp⟩
  | cons b rest ih =>
      by_cases hab : a = b
      · subst b
        have ht : tailScore a false rest ≤ 1 := by simpa [tailScore] using h
        rcases ih a ht with ⟨k, l, heq⟩ | ⟨k, l, heq⟩
        · exact Or.inl ⟨k + 1, l, by
            simpa [List.replicate_succ, List.cons_append] using
              congrArg (List.cons a) heq⟩
        · exact Or.inr ⟨k + 1, l, by
            simpa [List.replicate_succ, List.cons_append] using
              congrArg (List.cons a) heq⟩
      · have hb : b = !a := ne_bool_eq_not hab
        have ht : tailScore b true rest = 0 := by
          simp only [tailScore, hab, Bool.false_eq_true, ite_false,
            Bool.not_false] at h
          omega
        rcases tailScore_odd_zero rest b ht with ⟨l, heq⟩ | ⟨l, heq⟩
        · exact Or.inl ⟨0, l + 1, by simp [heq, hb, List.replicate_succ]⟩
        · exact Or.inr ⟨0, l + 1, by simp [heq, hb, List.replicate_succ]⟩

def PrefixOrSuffix (word : List Bool) : Prop :=
  ∃ a : Bool, ∃ k l : Nat, word = List.replicate k a ++ List.replicate l (!a)

def SingletonOrComplement (word : List Bool) : Prop :=
  ∃ a : Bool, ∃ k l : Nat,
    word = List.replicate k a ++ [!a] ++ List.replicate l a

/-- 两种颜色均至少出现两次，即实际割的两侧均不是单比特。 -/
def NonSingleton (word : List Bool) : Prop :=
  2 ≤ word.count true ∧ 2 ≤ word.count false

theorem low_score_classification (word : List Bool) (h : cutScore word ≤ 1) :
    PrefixOrSuffix word ∨ SingletonOrComplement word := by
  have hr := (cutScore_le_one_iff word).mp h
  cases word with
  | nil => exact Or.inl ⟨false, 0, 0, rfl⟩
  | cons a rest =>
      rcases low_tail_forms rest a hr with ⟨k, l, heq⟩ | ⟨k, l, heq⟩
      · exact Or.inl ⟨a, k + 1, l, heq⟩
      · exact Or.inr ⟨a, k + 1, l, heq⟩

theorem score_zero_uniform (word : List Bool) (h : cutScore word = 0) :
    ∃ a : Bool, word = List.replicate word.length a := by
  have hr := (cutScore_eq_zero_iff word).mp h
  cases word with
  | nil => exact ⟨false, rfl⟩
  | cons a rest =>
      have hu := tailScore_zero_uniform rest a hr
      exact ⟨a, by simpa [List.replicate_succ] using congrArg (List.cons a) hu⟩

theorem singleton_not_nonsingleton (word : List Bool)
    (h : SingletonOrComplement word) : ¬NonSingleton word := by
  rcases h with ⟨a, k, l, rfl⟩
  cases a <;> simp [NonSingleton, List.count_replicate]

/-- 低分数的每一个非单体物理割都是一个前缀与一个后缀。 -/
theorem nonsingleton_low_score_prefix (word : List Bool)
    (hn : NonSingleton word) (hs : cutScore word ≤ 1) : PrefixOrSuffix word := by
  rcases low_score_classification word hs with hp | hsng
  · exact hp
  · exact False.elim (singleton_not_nonsingleton word hsng hn)

/-- 同时给出前缀、后缀长度均至少二的接口。 -/
theorem nonsingleton_low_score_prefix_lengths (word : List Bool)
    (hn : NonSingleton word) (hs : cutScore word ≤ 1) :
    ∃ a : Bool, ∃ k l : Nat, 2 ≤ k ∧ 2 ≤ l ∧
      word = List.replicate k a ++ List.replicate l (!a) := by
  rcases nonsingleton_low_score_prefix word hn hs with ⟨a, k, l, heq⟩
  refine ⟨a, k, l, ?_, ?_, heq⟩
  all_goals
    rw [heq] at hn
    cases a <;> simp [NonSingleton, List.count_replicate] at hn <;> omega

/-- 直接可用的三分支覆盖：非单体割要么分数二，要么具有前后缀形式。 -/
theorem nonsingleton_cases (word : List Bool) (hn : NonSingleton word) :
    cutScore word = 2 ∨
      ∃ a : Bool, ∃ k l : Nat, 2 ≤ k ∧ 2 ≤ l ∧
        word = List.replicate k a ++ List.replicate l (!a) := by
  by_cases hs : cutScore word ≤ 1
  · exact Or.inr (nonsingleton_low_score_prefix_lengths word hn hs)
  · left
    have hc := cutScore_eq_min word
    omega

/-- 将列表中的两色计数直接识别为实际物理站点集合的基数。 -/
theorem count_ofFn_eq_card {n : Nat} (color : Fin n → Bool) (a : Bool) :
    (List.ofFn color).count a = (Finset.univ.filter fun i => color i = a).card := by
  symm
  simpa only [List.Vector.get_ofFn, List.Vector.toList_ofFn] using
    Fin.card_filter_univ_eq_vector_get_eq_count a (List.Vector.ofFn color)

/-- 用物理位置阈值表述前缀／后缀，避免列表表示成为额外前提。 -/
theorem fin_nonsingleton_low_score_prefix {n : Nat} (color : Fin n → Bool)
    (ht : 2 ≤ (Finset.univ.filter fun i => color i = true).card)
    (hf : 2 ≤ (Finset.univ.filter fun i => color i = false).card)
    (hs : cutScore (List.ofFn color) ≤ 1) :
    ∃ a : Bool, ∃ k : Nat, 2 ≤ k ∧ k + 2 ≤ n ∧
      ∀ i : Fin n, color i = if i.val < k then a else !a := by
  have hn : NonSingleton (List.ofFn color) := by
    exact ⟨(count_ofFn_eq_card color true).symm ▸ ht,
      (count_ofFn_eq_card color false).symm ▸ hf⟩
  rcases nonsingleton_low_score_prefix_lengths (List.ofFn color) hn hs with
    ⟨a, k, l, hk, hl, heq⟩
  have hlen : n = k + l := by simpa using congrArg List.length heq
  refine ⟨a, k, hk, by omega, ?_⟩
  intro i
  have hi := congrArg (fun w : List Bool => w[i.val]?) heq
  by_cases hik : i.val < k
  · simpa [List.getElem?_append, List.getElem?_replicate, hik, i.isLt] using hi
  · have hil : i.val - k < l := by omega
    simpa [List.getElem?_append, List.getElem?_replicate, hik, hil, i.isLt] using hi

def cutWord {n : Nat} (S : Finset (Fin n)) : List Bool :=
  List.ofFn fun i => decide (i ∈ S)

/-- 对原始物理割集合给出前缀／后缀结论；无需任何矩阵秩假设。 -/
theorem physical_cut_low_score_prefix {n : Nat} (S : Finset (Fin n))
    (hS : 2 ≤ S.card) (hSc : 2 ≤ Sᶜ.card)
    (hs : cutScore (cutWord S) ≤ 1) :
    ∃ k : Nat, 2 ≤ k ∧ k + 2 ≤ n ∧
      (S = Finset.univ.filter (fun i => i.val < k) ∨
        S = Finset.univ.filter (fun i => k ≤ i.val)) := by
  have htrue : (Finset.univ.filter fun i : Fin n => decide (i ∈ S) = true) = S := by
    ext i
    simp
  have hfalse : (Finset.univ.filter fun i : Fin n => decide (i ∈ S) = false) = Sᶜ := by
    ext i
    simp
  have ht : 2 ≤ (Finset.univ.filter fun i : Fin n => decide (i ∈ S) = true).card :=
    by simpa only [htrue] using hS
  have hf : 2 ≤ (Finset.univ.filter fun i : Fin n => decide (i ∈ S) = false).card :=
    by simpa only [hfalse] using hSc
  rcases fin_nonsingleton_low_score_prefix (fun i => decide (i ∈ S)) ht hf hs with
    ⟨a, k, hk, hkn, hcolor⟩
  refine ⟨k, hk, hkn, ?_⟩
  cases a with
  | false =>
      right
      ext i
      have hi := hcolor i
      by_cases hik : i.val < k
      · simp [hik] at hi
        simp [hi, Nat.not_le_of_gt hik]
      · simp [hik] at hi
        simp [hi, Nat.le_of_not_gt hik]
  | true =>
      left
      ext i
      have hi := hcolor i
      by_cases hik : i.val < k
      · simp [hik] at hi
        simp [hi, hik]
      · simp [hik] at hi
        simp [hi, hik]

/-- 前缀纯度定理可直接使用本接口，并以补集纯度相等处理另一方向。 -/
theorem physical_cut_low_score_prefix_or_compl {n : Nat} (S : Finset (Fin n))
    (hS : 2 ≤ S.card) (hSc : 2 ≤ Sᶜ.card)
    (hs : cutScore (cutWord S) ≤ 1) :
    ∃ k : Nat, 2 ≤ k ∧ 2 ≤ n - k ∧
      (S = Finset.univ.filter (fun i => i.val < k) ∨
        Sᶜ = Finset.univ.filter (fun i => i.val < k)) := by
  rcases physical_cut_low_score_prefix S hS hSc hs with ⟨k, hk, hkn, hp | hsuf⟩
  · exact ⟨k, hk, by omega, Or.inl hp⟩
  · refine ⟨k, hk, by omega, Or.inr ?_⟩
    ext i
    simp [hsuf]

/-- 任意非单体物理割完整落入闭包分支或前缀分支。 -/
theorem physical_cut_cases {n : Nat} (S : Finset (Fin n))
    (hS : 2 ≤ S.card) (hSc : 2 ≤ Sᶜ.card) :
    cutScore (cutWord S) = 2 ∨
      ∃ k : Nat, 2 ≤ k ∧ 2 ≤ n - k ∧
        (S = Finset.univ.filter (fun i => i.val < k) ∨
          Sᶜ = Finset.univ.filter (fun i => i.val < k)) := by
  by_cases hs : cutScore (cutWord S) ≤ 1
  · exact Or.inr (physical_cut_low_score_prefix_or_compl S hS hSc hs)
  · left
    have hc := cutScore_eq_min (cutWord S)
    omega

end UnifiedEJM.PathCutScore
