import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0307Input0 : List ℕ := [0, 8, 128, 136, 578, 586, 706, 714]
private def finish0307Raw0 : List ℕ := [0, 8, 128, 136, 66, 74, 194, 202]
private theorem finish0307Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0307Input0) = fromList finish0307Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0307 : finishSupport ⟨true, bits4 4⟩ support1036 = 1 • support1037 := by
  have hs : support1036 = fromList finish0307Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0307Chunk0]
  have hn : (finish0307Raw0 : Multiset ℕ) = 1 • (supportNumbers1037 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1037] using hm

private def finish0308Input0 : List ℕ := [0, 9]
private def finish0308Raw0 : List ℕ := [0, 9]
private theorem finish0308Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0308Input0) = fromList finish0308Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0308 : finishSupport ⟨false, bits4 4⟩ support1039 = 1 • support1039 := by
  have hs : support1039 = fromList finish0308Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0308Chunk0]
  have hn : (finish0308Raw0 : Multiset ℕ) = 1 • (supportNumbers1039 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1039] using hm

private def finish0309Input0 : List ℕ := [0, 9, 578, 587]
private def finish0309Raw0 : List ℕ := [0, 9, 66, 75]
private theorem finish0309Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0309Input0) = fromList finish0309Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0309 : finishSupport ⟨true, bits4 4⟩ support1040 = 1 • support1041 := by
  have hs : support1040 = fromList finish0309Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0309Chunk0]
  have hn : (finish0309Raw0 : Multiset ℕ) = 1 • (supportNumbers1041 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1041] using hm

private def finish0310Input0 : List ℕ := [0, 2, 9, 11]
private def finish0310Raw0 : List ℕ := [0, 2, 9, 11]
private theorem finish0310Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0310Input0) = fromList finish0310Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0310 : finishSupport ⟨false, bits4 4⟩ support0175 = 1 • support0175 := by
  have hs : support0175 = fromList finish0310Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0310Chunk0]
  have hn : (finish0310Raw0 : Multiset ℕ) = 1 • (supportNumbers0175 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0175] using hm

private def finish0311Input0 : List ℕ := [0, 2, 9, 11, 576, 578, 585, 587]
private def finish0311Raw0 : List ℕ := [0, 2, 9, 11, 64, 66, 73, 75]
private theorem finish0311Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0311Input0) = fromList finish0311Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0311 : finishSupport ⟨true, bits4 4⟩ support1042 = 1 • support1043 := by
  have hs : support1042 = fromList finish0311Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0311Chunk0]
  have hn : (finish0311Raw0 : Multiset ℕ) = 1 • (supportNumbers1043 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1043] using hm

private def finish0312Input0 : List ℕ := [0, 9, 130, 139]
private def finish0312Raw0 : List ℕ := [0, 9, 130, 139]
private theorem finish0312Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0312Input0) = fromList finish0312Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0312 : finishSupport ⟨false, bits4 4⟩ support1044 = 1 • support1044 := by
  have hs : support1044 = fromList finish0312Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0312Chunk0]
  have hn : (finish0312Raw0 : Multiset ℕ) = 1 • (supportNumbers1044 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1044] using hm

private def finish0313Input0 : List ℕ := [0, 9, 130, 139, 578, 587, 704, 713]
private def finish0313Raw0 : List ℕ := [0, 9, 130, 139, 66, 75, 192, 201]
private theorem finish0313Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0313Input0) = fromList finish0313Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0313 : finishSupport ⟨true, bits4 4⟩ support1045 = 1 • support1046 := by
  have hs : support1045 = fromList finish0313Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0313Chunk0]
  have hn : (finish0313Raw0 : Multiset ℕ) = 1 • (supportNumbers1046 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1046] using hm

private def finish0314Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 288, 290, 297, 299, 416, 418, 425, 427]
private def finish0314Raw0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139]
private theorem finish0314Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0314Input0) = fromList finish0314Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0314 : finishSupport ⟨false, bits4 4⟩ support1048 = 1 • support0351 := by
  have hs : support1048 = fromList finish0314Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0314Chunk0]
  have hn : (finish0314Raw0 : Multiset ℕ) = 1 • (supportNumbers0351 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0351] using hm

private def finish0315Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 288, 290, 297, 299, 416, 418, 425, 427, 576, 578, 585, 587, 704, 706, 713, 715, 864, 866, 873, 875, 992, 994, 1001, 1003]
private def finish0315Raw0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 32, 34, 41, 43, 160, 162, 169, 171, 64, 66, 73, 75, 192, 194, 201, 203, 96, 98, 105, 107, 224, 226, 233, 235]
private theorem finish0315Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0315Input0) = fromList finish0315Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0315 : finishSupport ⟨true, bits4 4⟩ support1049 = 1 • support1050 := by
  have hs : support1049 = fromList finish0315Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0315Chunk0]
  have hn : (finish0315Raw0 : Multiset ℕ) = 1 • (supportNumbers1050 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1050] using hm

private def finish0316Input0 : List ℕ := [0, 11, 131, 136]
private def finish0316Raw0 : List ℕ := [0, 11, 131, 136]
private theorem finish0316Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0316Input0) = fromList finish0316Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0316 : finishSupport ⟨false, bits4 4⟩ support1051 = 1 • support1051 := by
  have hs : support1051 = fromList finish0316Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0316Chunk0]
  have hn : (finish0316Raw0 : Multiset ℕ) = 1 • (supportNumbers1051 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1051] using hm

private def finish0317Input0 : List ℕ := [0, 11, 131, 136, 578, 585, 705, 714]
private def finish0317Raw0 : List ℕ := [0, 11, 131, 136, 66, 73, 193, 202]
private theorem finish0317Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0317Input0) = fromList finish0317Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0317 : finishSupport ⟨true, bits4 4⟩ support1052 = 1 • support1053 := by
  have hs : support1052 = fromList finish0317Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0317Chunk0]
  have hn : (finish0317Raw0 : Multiset ℕ) = 1 • (supportNumbers1053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1053] using hm

private def finish0318Input0 : List ℕ := [0, 1, 8, 9]
private def finish0318Raw0 : List ℕ := [0, 1, 8, 9]
private theorem finish0318Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0318Input0) = fromList finish0318Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0318 : finishSupport ⟨false, bits4 4⟩ support0874 = 1 • support0874 := by
  have hs : support0874 = fromList finish0318Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0318Chunk0]
  have hn : (finish0318Raw0 : Multiset ℕ) = 1 • (supportNumbers0874 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0874] using hm

private def finish0319Input0 : List ℕ := [0, 1, 8, 9, 578, 579, 586, 587]
private def finish0319Raw0 : List ℕ := [0, 1, 8, 9, 66, 67, 74, 75]
private theorem finish0319Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0319Input0) = fromList finish0319Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0319 : finishSupport ⟨true, bits4 4⟩ support1055 = 1 • support1056 := by
  have hs : support1055 = fromList finish0319Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0319Chunk0]
  have hn : (finish0319Raw0 : Multiset ℕ) = 1 • (supportNumbers1056 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1056] using hm

private def finish0320Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 416, 417, 418, 419, 424, 425, 426, 427]
private def finish0320Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem finish0320Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0320Input0) = fromList finish0320Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0320 : finishSupport ⟨false, bits4 4⟩ support1058 = 1 • support0180 := by
  have hs : support1058 = fromList finish0320Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0320Chunk0]
  have hn : (finish0320Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def finish0321Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 416, 417, 418, 419, 424, 425, 426, 427, 576, 577, 578, 579, 584, 585, 586, 587, 992, 993, 994, 995, 1000, 1001, 1002, 1003]
private def finish0321Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 160, 161, 162, 163, 168, 169, 170, 171, 64, 65, 66, 67, 72, 73, 74, 75, 224, 225, 226, 227, 232, 233, 234, 235]
private theorem finish0321Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0321Input0) = fromList finish0321Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0321 : finishSupport ⟨true, bits4 4⟩ support1059 = 1 • support1060 := by
  have hs : support1059 = fromList finish0321Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0321Chunk0]
  have hn : (finish0321Raw0 : Multiset ℕ) = 1 • (supportNumbers1060 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1060] using hm

private def finish0322Input0 : List ℕ := [0, 2, 129, 131]
private def finish0322Raw0 : List ℕ := [0, 2, 129, 131]
private theorem finish0322Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0322Input0) = fromList finish0322Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0322 : finishSupport ⟨false, bits4 4⟩ support0110 = 1 • support0110 := by
  have hs : support0110 = fromList finish0322Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0322Chunk0]
  have hn : (finish0322Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm

private def finish0323Input0 : List ℕ := [0, 2, 129, 131, 576, 578, 705, 707]
private def finish0323Raw0 : List ℕ := [0, 2, 129, 131, 64, 66, 193, 195]
private theorem finish0323Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0323Input0) = fromList finish0323Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0323 : finishSupport ⟨true, bits4 4⟩ support1061 = 1 • support1062 := by
  have hs : support1061 = fromList finish0323Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0323Chunk0]
  have hn : (finish0323Raw0 : Multiset ℕ) = 1 • (supportNumbers1062 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1062] using hm

private def finish0324Input0 : List ℕ := [0, 10, 129, 139]
private def finish0324Raw0 : List ℕ := [0, 10, 129, 139]
private theorem finish0324Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0324Input0) = fromList finish0324Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0324 : finishSupport ⟨false, bits4 4⟩ support1063 = 1 • support1063 := by
  have hs : support1063 = fromList finish0324Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0324Chunk0]
  have hn : (finish0324Raw0 : Multiset ℕ) = 1 • (supportNumbers1063 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1063] using hm

private def finish0325Input0 : List ℕ := [0, 10, 129, 139, 578, 584, 707, 713]
private def finish0325Raw0 : List ℕ := [0, 10, 129, 139, 66, 72, 195, 201]
private theorem finish0325Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0325Input0) = fromList finish0325Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0325 : finishSupport ⟨true, bits4 4⟩ support1064 = 1 • support1065 := by
  have hs : support1064 = fromList finish0325Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0325Chunk0]
  have hn : (finish0325Raw0 : Multiset ℕ) = 1 • (supportNumbers1065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1065] using hm

private def finish0326Input0 : List ℕ := [0, 3, 9, 10, 129, 130, 136, 139]
private def finish0326Raw0 : List ℕ := [0, 3, 9, 10, 129, 130, 136, 139]
private theorem finish0326Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0326Input0) = fromList finish0326Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0326 : finishSupport ⟨false, bits4 4⟩ support1068 = 1 • support1068 := by
  have hs : support1068 = fromList finish0326Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0326Chunk0]
  have hn : (finish0326Raw0 : Multiset ℕ) = 1 • (supportNumbers1068 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1068] using hm

private def finish0327Input0 : List ℕ := [0, 3, 9, 10, 129, 130, 136, 139, 577, 578, 584, 587, 704, 707, 713, 714]
private def finish0327Raw0 : List ℕ := [0, 3, 9, 10, 129, 130, 136, 139, 65, 66, 72, 75, 192, 195, 201, 202]
private theorem finish0327Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0327Input0) = fromList finish0327Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0327 : finishSupport ⟨true, bits4 4⟩ support1069 = 1 • support1070 := by
  have hs : support1069 = fromList finish0327Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0327Chunk0]
  have hn : (finish0327Raw0 : Multiset ℕ) = 1 • (supportNumbers1070 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1070] using hm

private def finish0328Input0 : List ℕ := [0, 1, 128, 129]
private def finish0328Raw0 : List ℕ := [0, 1, 128, 129]
private theorem finish0328Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0328Input0) = fromList finish0328Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0328 : finishSupport ⟨false, bits4 4⟩ support0898 = 1 • support0898 := by
  have hs : support0898 = fromList finish0328Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0328Chunk0]
  have hn : (finish0328Raw0 : Multiset ℕ) = 1 • (supportNumbers0898 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0898] using hm

private def finish0329Input0 : List ℕ := [0, 1, 128, 129, 578, 579, 706, 707]
private def finish0329Raw0 : List ℕ := [0, 1, 128, 129, 66, 67, 194, 195]
private theorem finish0329Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0329Input0) = fromList finish0329Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0329 : finishSupport ⟨true, bits4 4⟩ support1072 = 1 • support1073 := by
  have hs : support1072 = fromList finish0329Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0329Chunk0]
  have hn : (finish0329Raw0 : Multiset ℕ) = 1 • (supportNumbers1073 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1073] using hm

private def finish0330Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 296, 297, 298, 299, 424, 425, 426, 427]
private def finish0330Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem finish0330Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0330Input0) = fromList finish0330Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0330 : finishSupport ⟨false, bits4 4⟩ support1075 = 1 • support0187 := by
  have hs : support1075 = fromList finish0330Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0330Chunk0]
  have hn : (finish0330Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def finish0331Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 296, 297, 298, 299, 424, 425, 426, 427, 576, 577, 578, 579, 704, 705, 706, 707, 872, 873, 874, 875, 1000, 1001, 1002, 1003]
private def finish0331Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 40, 41, 42, 43, 168, 169, 170, 171, 64, 65, 66, 67, 192, 193, 194, 195, 104, 105, 106, 107, 232, 233, 234, 235]
private theorem finish0331Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0331Input0) = fromList finish0331Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0331 : finishSupport ⟨true, bits4 4⟩ support1076 = 1 • support1077 := by
  have hs : support1076 = fromList finish0331Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0331Chunk0]
  have hn : (finish0331Raw0 : Multiset ℕ) = 1 • (supportNumbers1077 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1077] using hm

private def finish0332Input0 : List ℕ := [0, 1, 130, 131]
private def finish0332Raw0 : List ℕ := [0, 1, 130, 131]
private theorem finish0332Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0332Input0) = fromList finish0332Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0332 : finishSupport ⟨false, bits4 4⟩ support0857 = 1 • support0857 := by
  have hs : support0857 = fromList finish0332Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0332Chunk0]
  have hn : (finish0332Raw0 : Multiset ℕ) = 1 • (supportNumbers0857 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0857] using hm

private def finish0333Input0 : List ℕ := [0, 1, 130, 131, 578, 579, 704, 705]
private def finish0333Raw0 : List ℕ := [0, 1, 130, 131, 66, 67, 192, 193]
private theorem finish0333Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0333Input0) = fromList finish0333Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0333 : finishSupport ⟨true, bits4 4⟩ support1078 = 1 • support1079 := by
  have hs : support1078 = fromList finish0333Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0333Chunk0]
  have hn : (finish0333Raw0 : Multiset ℕ) = 1 • (supportNumbers1079 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1079] using hm

private def finish0334Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 288, 289, 290, 291, 416, 417, 418, 419]
private def finish0334Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem finish0334Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0334Input0) = fromList finish0334Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0334 : finishSupport ⟨false, bits4 4⟩ support1081 = 1 • support0187 := by
  have hs : support1081 = fromList finish0334Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0334Chunk0]
  have hn : (finish0334Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def finish0335Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 288, 289, 290, 291, 416, 417, 418, 419, 576, 577, 578, 579, 704, 705, 706, 707, 864, 865, 866, 867, 992, 993, 994, 995]
private def finish0335Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 32, 33, 34, 35, 160, 161, 162, 163, 64, 65, 66, 67, 192, 193, 194, 195, 96, 97, 98, 99, 224, 225, 226, 227]
private theorem finish0335Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0335Input0) = fromList finish0335Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0335 : finishSupport ⟨true, bits4 4⟩ support1082 = 1 • support1083 := by
  have hs : support1082 = fromList finish0335Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0335Chunk0]
  have hn : (finish0335Raw0 : Multiset ℕ) = 1 • (supportNumbers1083 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1083] using hm

private def finish0336Input0 : List ℕ := [0, 1, 2, 3, 444, 445, 446, 447]
private def finish0336Raw0 : List ℕ := [0, 1, 2, 3, 188, 189, 190, 191]
private theorem finish0336Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0336Input0) = fromList finish0336Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0336 : finishSupport ⟨false, bits4 4⟩ support1085 = 1 • support0688 := by
  have hs : support1085 = fromList finish0336Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0336Chunk0]
  have hn : (finish0336Raw0 : Multiset ℕ) = 1 • (supportNumbers0688 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0688] using hm

private def finish0337Input0 : List ℕ := [0, 1, 2, 3, 444, 445, 446, 447, 576, 577, 578, 579, 1020, 1021, 1022, 1023]
private def finish0337Raw0 : List ℕ := [0, 1, 2, 3, 188, 189, 190, 191, 64, 65, 66, 67, 252, 253, 254, 255]
private theorem finish0337Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0337Input0) = fromList finish0337Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0337 : finishSupport ⟨true, bits4 4⟩ support1086 = 1 • support1087 := by
  have hs : support1086 = fromList finish0337Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0337Chunk0]
  have hn : (finish0337Raw0 : Multiset ℕ) = 1 • (supportNumbers1087 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1087] using hm

private def finish0338Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 416, 417, 418, 419, 444, 445, 446, 447]
private def finish0338Raw0 : List ℕ := [0, 1, 2, 3, 188, 189, 190, 191]
private theorem finish0338Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0338Input0) = fromList finish0338Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0338 : finishSupport ⟨false, bits4 4⟩ support1090 = 1 • support0688 := by
  have hs : support1090 = fromList finish0338Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0338Chunk0]
  have hn : (finish0338Raw0 : Multiset ℕ) = 1 • (supportNumbers0688 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0688] using hm

private def finish0339Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 416, 417, 418, 419, 444, 445, 446, 447, 576, 577, 578, 579, 604, 605, 606, 607, 992, 993, 994, 995, 1020, 1021, 1022, 1023]
private def finish0339Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 160, 161, 162, 163, 188, 189, 190, 191, 64, 65, 66, 67, 92, 93, 94, 95, 224, 225, 226, 227, 252, 253, 254, 255]
private theorem finish0339Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0339Input0) = fromList finish0339Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0339 : finishSupport ⟨true, bits4 4⟩ support1091 = 1 • support1092 := by
  have hs : support1091 = fromList finish0339Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0339Chunk0]
  have hn : (finish0339Raw0 : Multiset ℕ) = 1 • (supportNumbers1092 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1092] using hm

private def finish0340Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159]
private def finish0340Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem finish0340Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0340Input0) = fromList finish0340Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0340 : finishSupport ⟨false, bits4 4⟩ support0279 = 1 • support0187 := by
  have hs : support0279 = fromList finish0340Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0340Chunk0]
  have hn : (finish0340Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def finish0341Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 576, 577, 578, 579, 604, 605, 606, 607, 704, 705, 706, 707, 732, 733, 734, 735]
private def finish0341Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 64, 65, 66, 67, 92, 93, 94, 95, 192, 193, 194, 195, 220, 221, 222, 223]
private theorem finish0341Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0341Input0) = fromList finish0341Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0341 : finishSupport ⟨true, bits4 4⟩ support1093 = 1 • support1094 := by
  have hs : support1093 = fromList finish0341Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0341Chunk0]
  have hn : (finish0341Raw0 : Multiset ℕ) = 1 • (supportNumbers1094 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1094] using hm

private def finish0342Input0 : List ℕ := [0, 1, 10, 11]
private def finish0342Raw0 : List ℕ := [0, 1, 10, 11]
private theorem finish0342Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0342Input0) = fromList finish0342Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0342 : finishSupport ⟨false, bits4 4⟩ support0885 = 1 • support0885 := by
  have hs : support0885 = fromList finish0342Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0342Chunk0]
  have hn : (finish0342Raw0 : Multiset ℕ) = 1 • (supportNumbers0885 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0885] using hm

private def finish0343Input0 : List ℕ := [0, 1, 10, 11, 578, 579, 584, 585]
private def finish0343Raw0 : List ℕ := [0, 1, 10, 11, 66, 67, 72, 73]
private theorem finish0343Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0343Input0) = fromList finish0343Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0343 : finishSupport ⟨true, bits4 4⟩ support1096 = 1 • support1097 := by
  have hs : support1096 = fromList finish0343Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0343Chunk0]
  have hn : (finish0343Raw0 : Multiset ℕ) = 1 • (supportNumbers1097 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1097] using hm

private def finish0344Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 288, 289, 290, 291, 296, 297, 298, 299]
private def finish0344Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem finish0344Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0344Input0) = fromList finish0344Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0344 : finishSupport ⟨false, bits4 4⟩ support1099 = 1 • support0180 := by
  have hs : support1099 = fromList finish0344Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0344Chunk0]
  have hn : (finish0344Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def finish0345Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 288, 289, 290, 291, 296, 297, 298, 299, 576, 577, 578, 579, 584, 585, 586, 587, 864, 865, 866, 867, 872, 873, 874, 875]
private def finish0345Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 32, 33, 34, 35, 40, 41, 42, 43, 64, 65, 66, 67, 72, 73, 74, 75, 96, 97, 98, 99, 104, 105, 106, 107]
private theorem finish0345Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0345Input0) = fromList finish0345Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0345 : finishSupport ⟨true, bits4 4⟩ support1100 = 1 • support1101 := by
  have hs : support1100 = fromList finish0345Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0345Chunk0]
  have hn : (finish0345Raw0 : Multiset ℕ) = 1 • (supportNumbers1101 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1101] using hm

private def finish0346Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 308, 309, 310, 311, 424, 425, 426, 427]
private def finish0346Raw0 : List ℕ := [0, 1, 2, 3, 52, 53, 54, 55]
private theorem finish0346Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0346Input0) = fromList finish0346Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0346 : finishSupport ⟨false, bits4 4⟩ support1103 = 1 • support0498 := by
  have hs : support1103 = fromList finish0346Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0346Chunk0]
  have hn : (finish0346Raw0 : Multiset ℕ) = 1 • (supportNumbers0498 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0498] using hm

private def finish0347Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 308, 309, 310, 311, 424, 425, 426, 427, 576, 577, 578, 579, 732, 733, 734, 735, 884, 885, 886, 887, 1000, 1001, 1002, 1003]
private def finish0347Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 52, 53, 54, 55, 168, 169, 170, 171, 64, 65, 66, 67, 220, 221, 222, 223, 116, 117, 118, 119, 232, 233, 234, 235]
private theorem finish0347Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0347Input0) = fromList finish0347Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0347 : finishSupport ⟨true, bits4 4⟩ support1104 = 1 • support1105 := by
  have hs : support1104 = fromList finish0347Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0347Chunk0]
  have hn : (finish0347Raw0 : Multiset ℕ) = 1 • (supportNumbers1105 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1105] using hm

private def finish0348Input0 : List ℕ := [0, 1, 148, 149]
private def finish0348Raw0 : List ℕ := [0, 1]
private theorem finish0348Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0348Input0) = fromList finish0348Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0348 : finishSupport ⟨false, bits4 4⟩ support1106 = 1 • support0493 := by
  have hs : support1106 = fromList finish0348Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0348Chunk0]
  have hn : (finish0348Raw0 : Multiset ℕ) = 1 • (supportNumbers0493 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0493] using hm

private def finish0349Input0 : List ℕ := [0, 1, 148, 149, 578, 579, 726, 727]
private def finish0349Raw0 : List ℕ := [0, 1, 148, 149, 66, 67, 214, 215]
private theorem finish0349Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0349Input0) = fromList finish0349Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0349 : finishSupport ⟨true, bits4 4⟩ support1107 = 1 • support1108 := by
  have hs : support1107 = fromList finish0349Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0349Chunk0]
  have hn : (finish0349Raw0 : Multiset ℕ) = 1 • (supportNumbers1108 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1108] using hm

private def finish0350Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 296, 297, 298, 299, 444, 445, 446, 447]
private def finish0350Raw0 : List ℕ := [0, 1, 2, 3, 188, 189, 190, 191]
private theorem finish0350Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0350Input0) = fromList finish0350Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0350 : finishSupport ⟨false, bits4 4⟩ support1110 = 1 • support0688 := by
  have hs : support1110 = fromList finish0350Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0350Chunk0]
  have hn : (finish0350Raw0 : Multiset ℕ) = 1 • (supportNumbers0688 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0688] using hm

private def finish0351Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 296, 297, 298, 299, 444, 445, 446, 447, 576, 577, 578, 579, 724, 725, 726, 727, 872, 873, 874, 875, 1020, 1021, 1022, 1023]
private def finish0351Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 40, 41, 42, 43, 188, 189, 190, 191, 64, 65, 66, 67, 212, 213, 214, 215, 104, 105, 106, 107, 252, 253, 254, 255]
private theorem finish0351Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0351Input0) = fromList finish0351Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0351 : finishSupport ⟨true, bits4 4⟩ support1111 = 1 • support1112 := by
  have hs : support1111 = fromList finish0351Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0351Chunk0]
  have hn : (finish0351Raw0 : Multiset ℕ) = 1 • (supportNumbers1112 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1112] using hm

private def finish0352Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159]
private def finish0352Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem finish0352Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0352Input0) = fromList finish0352Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0352 : finishSupport ⟨false, bits4 4⟩ support0123 = 1 • support0180 := by
  have hs : support0123 = fromList finish0352Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0352Chunk0]
  have hn : (finish0352Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def finish0353Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 576, 577, 578, 579, 584, 585, 586, 587, 724, 725, 726, 727, 732, 733, 734, 735]
private def finish0353Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 64, 65, 66, 67, 72, 73, 74, 75, 212, 213, 214, 215, 220, 221, 222, 223]
private theorem finish0353Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0353Input0) = fromList finish0353Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0353 : finishSupport ⟨true, bits4 4⟩ support1113 = 1 • support1114 := by
  have hs : support1113 = fromList finish0353Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0353Chunk0]
  have hn : (finish0353Raw0 : Multiset ℕ) = 1 • (supportNumbers1114 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1114] using hm

private def finish0354Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 288, 289, 290, 291, 296, 297, 298, 299, 436, 437, 438, 439, 444, 445, 446, 447]
private def finish0354Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 180, 181, 182, 183, 188, 189, 190, 191]
private theorem finish0354Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0354Input0) = fromList finish0354Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0354 : finishSupport ⟨false, bits4 4⟩ support1116 = 1 • support1117 := by
  have hs : support1116 = fromList finish0354Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0354Chunk0]
  have hn : (finish0354Raw0 : Multiset ℕ) = 1 • (supportNumbers1117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1117] using hm

private def finish0355Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 288, 289, 290, 291, 296, 297, 298, 299, 436, 437, 438, 439, 444, 445, 446, 447, 576, 577, 578, 579, 584, 585, 586, 587, 724, 725, 726, 727, 732, 733, 734, 735, 864, 865, 866, 867, 872, 873, 874, 875, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]
private def finish0355Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 32, 33, 34, 35, 40, 41, 42, 43, 180, 181, 182, 183, 188, 189, 190, 191, 64, 65, 66, 67, 72, 73, 74, 75, 212, 213, 214, 215, 220, 221, 222, 223, 96, 97, 98, 99, 104, 105, 106, 107, 244, 245, 246, 247, 252, 253, 254, 255]
private theorem finish0355Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0355Input0) = fromList finish0355Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0355 : finishSupport ⟨true, bits4 4⟩ support1118 = 1 • support1119 := by
  have hs : support1118 = fromList finish0355Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0355Chunk0]
  have hn : (finish0355Raw0 : Multiset ℕ) = 1 • (supportNumbers1119 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1119] using hm

private def finish0356Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 288, 289, 290, 291, 308, 309, 310, 311]
private def finish0356Raw0 : List ℕ := [0, 1, 2, 3, 52, 53, 54, 55]
private theorem finish0356Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0356Input0) = fromList finish0356Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0356 : finishSupport ⟨false, bits4 4⟩ support1121 = 1 • support0498 := by
  have hs : support1121 = fromList finish0356Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0356Chunk0]
  have hn : (finish0356Raw0 : Multiset ℕ) = 1 • (supportNumbers0498 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0498] using hm

private def finish0357Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 288, 289, 290, 291, 308, 309, 310, 311, 576, 577, 578, 579, 596, 597, 598, 599, 864, 865, 866, 867, 884, 885, 886, 887]
private def finish0357Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 32, 33, 34, 35, 52, 53, 54, 55, 64, 65, 66, 67, 84, 85, 86, 87, 96, 97, 98, 99, 116, 117, 118, 119]
private theorem finish0357Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0357Input0) = fromList finish0357Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0357 : finishSupport ⟨true, bits4 4⟩ support1122 = 1 • support1123 := by
  have hs : support1122 = fromList finish0357Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0357Chunk0]
  have hn : (finish0357Raw0 : Multiset ℕ) = 1 • (supportNumbers1123 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1123] using hm

private def finish0358Input0 : List ℕ := [0, 1, 8, 9, 20, 21, 28, 29]
private def finish0358Raw0 : List ℕ := [0, 1, 8, 9]
private theorem finish0358Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0358Input0) = fromList finish0358Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0358 : finishSupport ⟨false, bits4 4⟩ support1124 = 1 • support0874 := by
  have hs : support1124 = fromList finish0358Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0358Chunk0]
  have hn : (finish0358Raw0 : Multiset ℕ) = 1 • (supportNumbers0874 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0874] using hm

private def finish0359Input0 : List ℕ := [0, 1, 8, 9, 20, 21, 28, 29, 578, 579, 586, 587, 598, 599, 606, 607]
private def finish0359Raw0 : List ℕ := [0, 1, 8, 9, 20, 21, 28, 29, 66, 67, 74, 75, 86, 87, 94, 95]
private theorem finish0359Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0359Input0) = fromList finish0359Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0359 : finishSupport ⟨true, bits4 4⟩ support1125 = 1 • support1126 := by
  have hs : support1125 = fromList finish0359Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0359Chunk0]
  have hn : (finish0359Raw0 : Multiset ℕ) = 1 • (supportNumbers1126 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1126] using hm

private def finish0360Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31]
private def finish0360Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem finish0360Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0360Input0) = fromList finish0360Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0360 : finishSupport ⟨false, bits4 4⟩ support0204 = 1 • support0180 := by
  have hs : support0204 = fromList finish0360Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0360Chunk0]
  have hn : (finish0360Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def finish0361Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 576, 577, 578, 579, 584, 585, 586, 587, 596, 597, 598, 599, 604, 605, 606, 607]
private def finish0361Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 64, 65, 66, 67, 72, 73, 74, 75, 84, 85, 86, 87, 92, 93, 94, 95]
private theorem finish0361Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0361Input0) = fromList finish0361Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0361 : finishSupport ⟨true, bits4 4⟩ support1127 = 1 • support1128 := by
  have hs : support1127 = fromList finish0361Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0361Chunk0]
  have hn : (finish0361Raw0 : Multiset ℕ) = 1 • (supportNumbers1128 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1128] using hm

private def finish0362Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 416, 417, 418, 419, 424, 425, 426, 427, 436, 437, 438, 439, 444, 445, 446, 447]
private def finish0362Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 180, 181, 182, 183, 188, 189, 190, 191]
private theorem finish0362Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0362Input0) = fromList finish0362Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0362 : finishSupport ⟨false, bits4 4⟩ support1130 = 1 • support1117 := by
  have hs : support1130 = fromList finish0362Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0362Chunk0]
  have hn : (finish0362Raw0 : Multiset ℕ) = 1 • (supportNumbers1117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1117] using hm

private def finish0363Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 416, 417, 418, 419, 424, 425, 426, 427, 436, 437, 438, 439, 444, 445, 446, 447, 576, 577, 578, 579, 584, 585, 586, 587, 596, 597, 598, 599, 604, 605, 606, 607, 992, 993, 994, 995, 1000, 1001, 1002, 1003, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]
private def finish0363Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 160, 161, 162, 163, 168, 169, 170, 171, 180, 181, 182, 183, 188, 189, 190, 191, 64, 65, 66, 67, 72, 73, 74, 75, 84, 85, 86, 87, 92, 93, 94, 95, 224, 225, 226, 227, 232, 233, 234, 235, 244, 245, 246, 247, 252, 253, 254, 255]
private theorem finish0363Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0363Input0) = fromList finish0363Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0363 : finishSupport ⟨true, bits4 4⟩ support1131 = 1 • support1132 := by
  have hs : support1131 = fromList finish0363Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0363Chunk0]
  have hn : (finish0363Raw0 : Multiset ℕ) = 1 • (supportNumbers1132 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1132] using hm

private def finish0364Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private def finish0364Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem finish0364Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0364Input0) = fromList finish0364Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0364 : finishSupport ⟨false, bits4 4⟩ support0130 = 1 • support0187 := by
  have hs : support0130 = fromList finish0364Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0364Chunk0]
  have hn : (finish0364Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
