import UnifiedEJM.PrefixCodedKernel

open OddEJM UnifiedEJM.PhysicsFinite

namespace UnifiedEJM.PrefixKernel

def encodeEndpointFlags (v : Fin 4 → Bool) : ℕ :=
  (if v 0 then 1 else 0) + (if v 1 then 2 else 0) +
    (if v 2 then 4 else 0) + (if v 3 then 8 else 0)

def decodeEndpointFlags (code : ℕ) : Fin 4 → Bool :=
  fun r => code.testBit r.val

theorem decode_encodeEndpointFlags (v : Fin 4 → Bool) :
    decodeEndpointFlags (encodeEndpointFlags v) = v := by
  revert v
  decide +kernel

/-- 固定首位对后，其他三个端点只通过这四个常量匹配标志进入状态。 -/
def endpointFlags (f s p l : Fin 4) : Fin 4 → Bool :=
  fun r => decide (rep true s r = rep true f r ∧
    rep false p r = rep true f r ∧ rep false l r = rep true f r)

def endpointMask (f s p l : Fin 4) : ℕ :=
  encodeEndpointFlags (endpointFlags f s p l)

def longStateWithEndpoint (la lb : Option Bit)
    (f a b ca da cb db : Fin 4) (context : ℕ) : LongState :=
  let rf := rep true f
  let ra := rep true a
  let rb := rep false b
  let pa := replica true (runParity la ca) (runParity la da)
  let pb := replica false (runParity lb cb) (runParity lb db)
  let ac := catRep true ca da
  let bc := catRep false cb db
  (fun r => ra r + rb r + pa r + pb r,
   fun r => decodeEndpointFlags context r && decide (ra r = rf r ∧ rb r = rf r) &&
     runMatches la (ac r) (rf r) && runMatches lb (bc r) (rf r))

theorem longState_eq_context (la lb : Option Bit)
    (f s a b p l ca da cb db : Fin 4) :
    longState la lb f s a b p l ca da cb db =
      longStateWithEndpoint la lb f a b ca da cb db (endpointMask f s p l) := by
  apply Prod.ext
  · rfl
  · funext r
    simp only [longState, longStateWithEndpoint, endpointMask, decode_encodeEndpointFlags,
      endpointFlags, Bool.decide_and, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem longState_eq_of_endpointMask (la lb : Option Bit)
    (f s p l s' p' l' a b ca da cb db : Fin 4)
    (h : endpointMask f s p l = endpointMask f s' p' l') :
    longState la lb f s a b p l ca da cb db =
      longState la lb f s' a b p' l' ca da cb db := by
  rw [longState_eq_context, longState_eq_context, h]

/-- 原函数状态列表也只依赖同一端点上下文，不涉及系数表。 -/
theorem longBlockClassList_eq_of_endpointMask (la lb : Option Bit)
    (f s p l s' p' l' : Fin 4)
    (h : endpointMask f s p l = endpointMask f s' p' l') :
    longBlockClassList la lb f s p l = longBlockClassList la lb f s' p' l' := by
  unfold longBlockClassList
  simp only [longState_eq_context, h]

/-- 每个固定la/lb/f/context只需核验一次整数权重表。 -/
def longBlockContextList (la lb : Option Bit) (f : Fin 4) (context : ℕ) :
    List (ℕ × WeightData) :=
  bindFin 4 fun a => bindFin 4 fun b =>
    bindFin 4 fun ca => bindFin 4 fun da => bindFin 4 fun cb => bindFin 4 fun db =>
      [(encodeLongState (longStateWithEndpoint la lb f a b ca da cb db context),
        crossSign a b • outerWeights (runPairWeight la ca da) (runPairWeight lb cb db))]

theorem longBlockCodeClassList_eq_context (la lb : Option Bit) (f s p l : Fin 4) :
    longBlockCodeClassList la lb f s p l =
      longBlockContextList la lb f (endpointMask f s p l) := by
  unfold longBlockCodeClassList longBlockContextList
  simp only [longState_eq_context]

theorem longBlockCodeClassList_eq_of_endpointMask (la lb : Option Bit)
    (f s p l s' p' l' : Fin 4)
    (h : endpointMask f s p l = endpointMask f s' p' l') :
    longBlockCodeClassList la lb f s p l = longBlockCodeClassList la lb f s' p' l' := by
  rw [longBlockCodeClassList_eq_context, longBlockCodeClassList_eq_context, h]

end UnifiedEJM.PrefixKernel
