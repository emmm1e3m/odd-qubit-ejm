import UnifiedEJM.PhysicsWeightedOrder

open scoped BigOperators

namespace UnifiedEJM.WeightedTransfer

namespace FiniteClosure

variable {σ α : Type*}

/-- none只表示已经进入有解析界保证的吸收区，不表示计算失败。 -/
def run (next : σ → α → Option σ) : σ → List α → Option σ
  | s, [] => some s
  | s, c :: cs => match next s c with
      | none => none
      | some s' => run next s' cs

/-- 同时传递score、交替段奇偶、末色与长度奇偶等任意元数据。 -/
theorem run_some_metadata {β : Type*} (next : σ → α → Option σ)
    (metadata : σ → β) (update : β → α → β)
    (hupdate : ∀ s c s', next s c = some s' →
      metadata s' = update (metadata s) c)
    (s : σ) (cs : List α) (s' : σ) (h : run next s cs = some s') :
    metadata s' = cs.foldl update (metadata s) := by
  induction cs generalizing s with
  | nil =>
      have heq : s = s' := Option.some.inj h
      subst s
      rfl
  | cons c cs ih =>
      cases hn : next s c with
      | none => simp [run, hn] at h
      | some t =>
          have ht : run next t cs = some s' := by simpa [run, hn] using h
          rw [ih t ht, hupdate s c t hn]
          rfl

/-- 未吸收的任意长输入，其值等于最终有限状态的终端值。 -/
theorem run_some_eval_eq (next : σ → α → Option σ) (eval : σ → List α → ℝ)
    (hstep : ∀ s c s' cs, next s c = some s' → eval s (c :: cs) = eval s' cs)
    (s : σ) (cs : List α) (s' : σ) (h : run next s cs = some s') :
    eval s cs = eval s' [] := by
  induction cs generalizing s with
  | nil =>
      have heq : s = s' := Option.some.inj h
      subst s
      rfl
  | cons c cs ih =>
      cases hn : next s c with
      | none => simp [run, hn] at h
      | some t =>
          have ht : run next t cs = some s' := by simpa [run, hn] using h
          rw [hstep s c t cs hn]
          exact ih t ht

/-- 归纳明确保留首次吸收后的全部后缀，任意长度不需要枚举。 -/
theorem run_none_eval_le (next : σ → α → Option σ) (eval : σ → List α → ℝ)
    (bound : ℝ)
    (hstep : ∀ s c s' cs, next s c = some s' → eval s (c :: cs) = eval s' cs)
    (habsorb : ∀ s c cs, next s c = none → eval s (c :: cs) ≤ bound)
    (s : σ) (cs : List α) (h : run next s cs = none) : eval s cs ≤ bound := by
  induction cs generalizing s with
  | nil => simp [run] at h
  | cons c cs ih =>
      cases hn : next s c with
      | none => exact habsorb s c cs hn
      | some t =>
          have ht : run next t cs = none := by simpa [run, hn] using h
          rw [hstep s c t cs hn]
          exact ih t ht

/-- 有限终端证书与吸收解析界共同覆盖全部有限颜色词。 -/
theorem bound_of_certificate (next : σ → α → Option σ) (eval : σ → List α → ℝ)
    (accept : σ → Prop) (safeBound finalBound : ℝ)
    (hstep : ∀ s c s' cs, next s c = some s' → eval s (c :: cs) = eval s' cs)
    (habsorb : ∀ s c cs, next s c = none → eval s (c :: cs) ≤ safeBound)
    (hterminal : ∀ s, accept s → eval s [] ≤ finalBound)
    (hsafe : safeBound ≤ finalBound) (s : σ) (cs : List α)
    (haccept : ∀ t, run next s cs = some t → accept t) : eval s cs ≤ finalBound := by
  cases hrun : run next s cs with
  | none =>
      exact le_trans (run_none_eval_le next eval safeBound hstep habsorb s cs hrun) hsafe
  | some t =>
      rw [run_some_eval_eq next eval hstep s cs t hrun]
      exact hterminal t (haccept t hrun)

/-- 观察值是实际加权转移、两个固定尾站与真实终端score的求和。 -/
def observationScore (decode : σ → Logical → Distribution) (current : σ → Site)
    (site : α → Site) (tail : List Site) (last : Site)
    (score : Logical → Logical → ℝ) (s : σ) (cs : List α) : ℝ :=
  ∑ d, ∑ k,
    (finish d last (evolve d (current s) (cs.map site ++ tail) (decode s d)) k : ℝ) *
      score d k

theorem observationScore_step (decode : σ → Logical → Distribution) (current : σ → Site)
    (site : α → Site) (tail : List Site) (last : Site)
    (score : Logical → Logical → ℝ) (s s' : σ) (c : α) (cs : List α)
    (hcurrent : current s' = site c)
    (hstep : ∀ d, advance d (current s) (site c) (decode s d) = decode s' d) :
    observationScore decode current site tail last score s (c :: cs) =
      observationScore decode current site tail last score s' cs := by
  unfold observationScore
  simp only [List.map_cons, List.cons_append, evolve, hcurrent]
  simp_rw [hstep]

/-- 吸收检查只需原有理权重的真实总和，无需外部GF(2)秩或支撑维数假设。 -/
theorem observationScore_absorb (decode : σ → Logical → Distribution) (current : σ → Site)
    (site : α → Site) (tail : List Site) (last : Site)
    (score : Logical → Logical → ℝ) (s : σ) (c : α) (cs : List α)
    (hnonneg : ∀ d m, 0 ≤ decode s d m)
    (hmass : (∑ d, mass (advance d (current s) (site c) (decode s d))) ≤ 1 / 4)
    (hscore : ∀ d k, score d k ≤ 1) :
    observationScore decode current site tail last score s (c :: cs) ≤ 1 / 4 := by
  unfold observationScore
  simp only [List.map_cons, List.cons_append, evolve]
  exact suffix_realScore_le_quarter_of_mass
    (fun d => advance d (current s) (site c) (decode s d))
    (fun d => advance_nonneg d (current s) (site c) (decode s d) (hnonneg d))
    hmass (site c) last (cs.map site ++ tail) score hscore

/-- 3/8的任意长度背景界只剩有限表内的等式、吸收质量和终端Fourier证书。 -/
theorem observationScore_le_three_eighths
    (decode : σ → Logical → Distribution) (current : σ → Site) (site : α → Site)
    (next : σ → α → Option σ) (tail : List Site) (last : Site)
    (score : Logical → Logical → ℝ) (accept : σ → Prop)
    (hnonneg : ∀ s d m, 0 ≤ decode s d m)
    (hstep : ∀ s c s', next s c = some s' →
      current s' = site c ∧
      ∀ d, advance d (current s) (site c) (decode s d) = decode s' d)
    (hmass : ∀ s c, next s c = none →
      (∑ d, mass (advance d (current s) (site c) (decode s d))) ≤ 1 / 4)
    (hscore : ∀ d k, score d k ≤ 1)
    (hterminal : ∀ s, accept s →
      observationScore decode current site tail last score s [] ≤ 3 / 8)
    (s : σ) (cs : List α)
    (haccept : ∀ t, run next s cs = some t → accept t) :
    observationScore decode current site tail last score s cs ≤ 3 / 8 := by
  apply bound_of_certificate next
    (observationScore decode current site tail last score) accept (1 / 4) (3 / 8)
    ?_ ?_ hterminal (by norm_num) s cs haccept
  · intro s c s' cs hnext
    obtain ⟨hc, he⟩ := hstep s c s' hnext
    exact observationScore_step decode current site tail last score s s' c cs hc he
  · intro s c cs hnext
    exact observationScore_absorb decode current site tail last score s c cs
      (hnonneg s) (hmass s c hnext) hscore

end FiniteClosure
end UnifiedEJM.WeightedTransfer
