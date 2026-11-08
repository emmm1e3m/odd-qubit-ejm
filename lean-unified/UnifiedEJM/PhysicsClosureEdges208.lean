import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0463Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 576, 578, 584, 586, 705, 707, 713, 715]
private def finish0463Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 64, 66, 72, 74, 193, 195, 201, 203]
private theorem finish0463Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0463Input0) = fromList finish0463Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0463 : finishSupport ⟨true, bits4 4⟩ support1308 = 1 • support1309 := by
  have hs : support1308 = fromList finish0463Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0463Chunk0]
  have hn : (finish0463Raw0 : Multiset ℕ) = 1 • (supportNumbers1309 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1309] using hm

private def finish0464Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 289, 291, 297, 299, 416, 418, 424, 426]
private def finish0464Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private theorem finish0464Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0464Input0) = fromList finish0464Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0464 : finishSupport ⟨false, bits4 4⟩ support1311 = 1 • support0268 := by
  have hs : support1311 = fromList finish0464Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0464Chunk0]
  have hn : (finish0464Raw0 : Multiset ℕ) = 1 • (supportNumbers0268 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0268] using hm

private def finish0465Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 289, 291, 297, 299, 416, 418, 424, 426, 576, 578, 584, 586, 705, 707, 713, 715, 865, 867, 873, 875, 992, 994, 1000, 1002]
private def finish0465Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 33, 35, 41, 43, 160, 162, 168, 170, 64, 66, 72, 74, 193, 195, 201, 203, 97, 99, 105, 107, 224, 226, 232, 234]
private theorem finish0465Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0465Input0) = fromList finish0465Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0465 : finishSupport ⟨true, bits4 4⟩ support1312 = 1 • support1313 := by
  have hs : support1312 = fromList finish0465Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0465Chunk0]
  have hn : (finish0465Raw0 : Multiset ℕ) = 1 • (supportNumbers1313 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1313] using hm

private def finish0466Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private def finish0466Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem finish0466Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0466Input0) = fromList finish0466Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0466 : finishSupport ⟨false, bits4 4⟩ support0187 = 1 • support0187 := by
  have hs : support0187 = fromList finish0466Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0466Chunk0]
  have hn : (finish0466Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def finish0467Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 576, 577, 578, 579, 704, 705, 706, 707]
private def finish0467Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 64, 65, 66, 67, 192, 193, 194, 195]
private theorem finish0467Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0467Input0) = fromList finish0467Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0467 : finishSupport ⟨true, bits4 4⟩ support1314 = 1 • support1315 := by
  have hs : support1314 = fromList finish0467Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0467Chunk0]
  have hn : (finish0467Raw0 : Multiset ℕ) = 1 • (supportNumbers1315 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1315] using hm

private def finish0468Input0 : List ℕ := [0, 1, 10, 11, 128, 129, 138, 139]
private def finish0468Raw0 : List ℕ := [0, 1, 10, 11, 128, 129, 138, 139]
private theorem finish0468Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0468Input0) = fromList finish0468Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0468 : finishSupport ⟨false, bits4 4⟩ support1136 = 1 • support1136 := by
  have hs : support1136 = fromList finish0468Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0468Chunk0]
  have hn : (finish0468Raw0 : Multiset ℕ) = 1 • (supportNumbers1136 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1136] using hm

private def finish0469Input0 : List ℕ := [0, 1, 10, 11, 128, 129, 138, 139, 578, 579, 584, 585, 706, 707, 712, 713]
private def finish0469Raw0 : List ℕ := [0, 1, 10, 11, 128, 129, 138, 139, 66, 67, 72, 73, 194, 195, 200, 201]
private theorem finish0469Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0469Input0) = fromList finish0469Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0469 : finishSupport ⟨true, bits4 4⟩ support1316 = 1 • support1317 := by
  have hs : support1316 = fromList finish0469Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0469Chunk0]
  have hn : (finish0469Raw0 : Multiset ℕ) = 1 • (supportNumbers1317 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1317] using hm

private def finish0470Input0 : List ℕ := [0, 1, 2, 3, 416, 417, 418, 419]
private def finish0470Raw0 : List ℕ := [0, 1, 2, 3]
private theorem finish0470Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0470Input0) = fromList finish0470Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0470 : finishSupport ⟨false, bits4 4⟩ support1320 = 1 • support0030 := by
  have hs : support1320 = fromList finish0470Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0470Chunk0]
  have hn : (finish0470Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def finish0471Input0 : List ℕ := [0, 1, 2, 3, 416, 417, 418, 419, 576, 577, 578, 579, 992, 993, 994, 995]
private def finish0471Raw0 : List ℕ := [0, 1, 2, 3, 160, 161, 162, 163, 64, 65, 66, 67, 224, 225, 226, 227]
private theorem finish0471Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0471Input0) = fromList finish0471Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0471 : finishSupport ⟨true, bits4 4⟩ support1321 = 1 • support1322 := by
  have hs : support1321 = fromList finish0471Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0471Chunk0]
  have hn : (finish0471Raw0 : Multiset ℕ) = 1 • (supportNumbers1322 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1322] using hm

private def finish0472Input0 : List ℕ := [0, 1, 30, 31]
private def finish0472Raw0 : List ℕ := [0, 1]
private theorem finish0472Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0472Input0) = fromList finish0472Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0472 : finishSupport ⟨false, bits4 4⟩ support1324 = 1 • support0493 := by
  have hs : support1324 = fromList finish0472Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0472Chunk0]
  have hn : (finish0472Raw0 : Multiset ℕ) = 1 • (supportNumbers0493 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0493] using hm

private def finish0473Input0 : List ℕ := [0, 1, 30, 31, 578, 579, 604, 605]
private def finish0473Raw0 : List ℕ := [0, 1, 30, 31, 66, 67, 92, 93]
private theorem finish0473Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0473Input0) = fromList finish0473Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0473 : finishSupport ⟨true, bits4 4⟩ support1325 = 1 • support1326 := by
  have hs : support1325 = fromList finish0473Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0473Chunk0]
  have hn : (finish0473Raw0 : Multiset ℕ) = 1 • (supportNumbers1326 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1326] using hm

private def finish0474Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 288, 289, 290, 291, 316, 317, 318, 319]
private def finish0474Raw0 : List ℕ := [0, 1, 2, 3, 60, 61, 62, 63]
private theorem finish0474Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0474Input0) = fromList finish0474Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0474 : finishSupport ⟨false, bits4 4⟩ support1328 = 1 • support0571 := by
  have hs : support1328 = fromList finish0474Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0474Chunk0]
  have hn : (finish0474Raw0 : Multiset ℕ) = 1 • (supportNumbers0571 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0571] using hm

private def finish0475Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 288, 289, 290, 291, 316, 317, 318, 319, 576, 577, 578, 579, 604, 605, 606, 607, 864, 865, 866, 867, 892, 893, 894, 895]
private def finish0475Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 32, 33, 34, 35, 60, 61, 62, 63, 64, 65, 66, 67, 92, 93, 94, 95, 96, 97, 98, 99, 124, 125, 126, 127]
private theorem finish0475Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0475Input0) = fromList finish0475Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0475 : finishSupport ⟨true, bits4 4⟩ support1329 = 1 • support1330 := by
  have hs : support1329 = fromList finish0475Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0475Chunk0]
  have hn : (finish0475Raw0 : Multiset ℕ) = 1 • (supportNumbers1330 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1330] using hm

private def finish0476Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private def finish0476Raw0 : List ℕ := [0, 1, 2, 3]
private theorem finish0476Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0476Input0) = fromList finish0476Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0476 : finishSupport ⟨false, bits4 4⟩ support0012 = 1 • support0030 := by
  have hs : support0012 = fromList finish0476Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0476Chunk0]
  have hn : (finish0476Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def finish0477Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 576, 577, 578, 579, 604, 605, 606, 607]
private def finish0477Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 64, 65, 66, 67, 92, 93, 94, 95]
private theorem finish0477Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0477Input0) = fromList finish0477Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0477 : finishSupport ⟨true, bits4 4⟩ support1331 = 1 • support1332 := by
  have hs : support1331 = fromList finish0477Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0477Chunk0]
  have hn : (finish0477Raw0 : Multiset ℕ) = 1 • (supportNumbers1332 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1332] using hm

private def finish0478Input0 : List ℕ := [0, 1, 28, 29, 128, 129, 156, 157]
private def finish0478Raw0 : List ℕ := [0, 1, 128, 129]
private theorem finish0478Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0478Input0) = fromList finish0478Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0478 : finishSupport ⟨false, bits4 4⟩ support1334 = 1 • support0898 := by
  have hs : support1334 = fromList finish0478Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0478Chunk0]
  have hn : (finish0478Raw0 : Multiset ℕ) = 1 • (supportNumbers0898 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0898] using hm

private def finish0479Input0 : List ℕ := [0, 1, 28, 29, 128, 129, 156, 157, 578, 579, 606, 607, 706, 707, 734, 735]
private def finish0479Raw0 : List ℕ := [0, 1, 28, 29, 128, 129, 156, 157, 66, 67, 94, 95, 194, 195, 222, 223]
private theorem finish0479Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0479Input0) = fromList finish0479Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0479 : finishSupport ⟨true, bits4 4⟩ support1335 = 1 • support1336 := by
  have hs : support1335 = fromList finish0479Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0479Chunk0]
  have hn : (finish0479Raw0 : Multiset ℕ) = 1 • (supportNumbers1336 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1336] using hm

private def finish0480Input0 : List ℕ := [0, 1, 8, 9, 130, 131, 138, 139]
private def finish0480Raw0 : List ℕ := [0, 1, 8, 9, 130, 131, 138, 139]
private theorem finish0480Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0480Input0) = fromList finish0480Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0480 : finishSupport ⟨false, bits4 4⟩ support0502 = 1 • support0502 := by
  have hs : support0502 = fromList finish0480Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0480Chunk0]
  have hn : (finish0480Raw0 : Multiset ℕ) = 1 • (supportNumbers0502 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0502] using hm

private def finish0481Input0 : List ℕ := [0, 1, 8, 9, 130, 131, 138, 139, 578, 579, 586, 587, 704, 705, 712, 713]
private def finish0481Raw0 : List ℕ := [0, 1, 8, 9, 130, 131, 138, 139, 66, 67, 74, 75, 192, 193, 200, 201]
private theorem finish0481Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0481Input0) = fromList finish0481Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0481 : finishSupport ⟨true, bits4 4⟩ support1338 = 1 • support1339 := by
  have hs : support1338 = fromList finish0481Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0481Chunk0]
  have hn : (finish0481Raw0 : Multiset ℕ) = 1 • (supportNumbers1339 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1339] using hm

private def finish0482Input0 : List ℕ := [0, 1, 10, 11, 150, 151, 156, 157]
private def finish0482Raw0 : List ℕ := [0, 1, 10, 11]
private theorem finish0482Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0482Input0) = fromList finish0482Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0482 : finishSupport ⟨false, bits4 4⟩ support1341 = 1 • support0885 := by
  have hs : support1341 = fromList finish0482Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0482Chunk0]
  have hn : (finish0482Raw0 : Multiset ℕ) = 1 • (supportNumbers0885 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0885] using hm

private def finish0483Input0 : List ℕ := [0, 1, 10, 11, 150, 151, 156, 157, 578, 579, 584, 585, 724, 725, 734, 735]
private def finish0483Raw0 : List ℕ := [0, 1, 10, 11, 150, 151, 156, 157, 66, 67, 72, 73, 212, 213, 222, 223]
private theorem finish0483Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0483Input0) = fromList finish0483Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0483 : finishSupport ⟨true, bits4 4⟩ support1342 = 1 • support1343 := by
  have hs : support1342 = fromList finish0483Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0483Chunk0]
  have hn : (finish0483Raw0 : Multiset ℕ) = 1 • (supportNumbers1343 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1343] using hm

private def finish0484Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private def finish0484Raw0 : List ℕ := [0, 1, 2, 3]
private theorem finish0484Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0484Input0) = fromList finish0484Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0484 : finishSupport ⟨false, bits4 4⟩ support0199 = 1 • support0030 := by
  have hs : support0199 = fromList finish0484Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0484Chunk0]
  have hn : (finish0484Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def finish0485Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 576, 577, 578, 579, 724, 725, 726, 727]
private def finish0485Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 64, 65, 66, 67, 212, 213, 214, 215]
private theorem finish0485Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0485Input0) = fromList finish0485Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0485 : finishSupport ⟨true, bits4 4⟩ support1345 = 1 • support1346 := by
  have hs : support1345 = fromList finish0485Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0485Chunk0]
  have hn : (finish0485Raw0 : Multiset ℕ) = 1 • (supportNumbers1346 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1346] using hm

private def finish0486Input0 : List ℕ := [0, 1, 30, 31, 138, 139, 148, 149]
private def finish0486Raw0 : List ℕ := [0, 1, 138, 139]
private theorem finish0486Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0486Input0) = fromList finish0486Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0486 : finishSupport ⟨false, bits4 4⟩ support1347 = 1 • support0575 := by
  have hs : support1347 = fromList finish0486Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0486Chunk0]
  have hn : (finish0486Raw0 : Multiset ℕ) = 1 • (supportNumbers0575 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0575] using hm

private def finish0487Input0 : List ℕ := [0, 1, 30, 31, 138, 139, 148, 149, 578, 579, 604, 605, 712, 713, 726, 727]
private def finish0487Raw0 : List ℕ := [0, 1, 30, 31, 138, 139, 148, 149, 66, 67, 92, 93, 200, 201, 214, 215]
private theorem finish0487Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0487Input0) = fromList finish0487Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0487 : finishSupport ⟨true, bits4 4⟩ support1348 = 1 • support1349 := by
  have hs : support1348 = fromList finish0487Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0487Chunk0]
  have hn : (finish0487Raw0 : Multiset ℕ) = 1 • (supportNumbers1349 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1349] using hm

private def finish0488Input0 : List ℕ := [0, 1, 8, 9, 22, 23, 30, 31, 130, 131, 138, 139, 148, 149, 156, 157]
private def finish0488Raw0 : List ℕ := [0, 1, 8, 9, 130, 131, 138, 139]
private theorem finish0488Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0488Input0) = fromList finish0488Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0488 : finishSupport ⟨false, bits4 4⟩ support1352 = 1 • support0502 := by
  have hs : support1352 = fromList finish0488Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0488Chunk0]
  have hn : (finish0488Raw0 : Multiset ℕ) = 1 • (supportNumbers0502 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0502] using hm

private def finish0489Input0 : List ℕ := [0, 1, 8, 9, 22, 23, 30, 31, 130, 131, 138, 139, 148, 149, 156, 157, 578, 579, 586, 587, 596, 597, 604, 605, 704, 705, 712, 713, 726, 727, 734, 735]
private def finish0489Raw0 : List ℕ := [0, 1, 8, 9, 22, 23, 30, 31, 130, 131, 138, 139, 148, 149, 156, 157, 66, 67, 74, 75, 84, 85, 92, 93, 192, 193, 200, 201, 214, 215, 222, 223]
private theorem finish0489Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0489Input0) = fromList finish0489Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0489 : finishSupport ⟨true, bits4 4⟩ support1353 = 1 • support1354 := by
  have hs : support1353 = fromList finish0489Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0489Chunk0]
  have hn : (finish0489Raw0 : Multiset ℕ) = 1 • (supportNumbers1354 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1354] using hm

private def finish0490Input0 : List ℕ := [0, 1, 20, 21, 130, 131, 150, 151]
private def finish0490Raw0 : List ℕ := [0, 1, 130, 131]
private theorem finish0490Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0490Input0) = fromList finish0490Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0490 : finishSupport ⟨false, bits4 4⟩ support1356 = 1 • support0857 := by
  have hs : support1356 = fromList finish0490Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0490Chunk0]
  have hn : (finish0490Raw0 : Multiset ℕ) = 1 • (supportNumbers0857 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0857] using hm

private def finish0491Input0 : List ℕ := [0, 1, 20, 21, 130, 131, 150, 151, 578, 579, 598, 599, 704, 705, 724, 725]
private def finish0491Raw0 : List ℕ := [0, 1, 20, 21, 130, 131, 150, 151, 66, 67, 86, 87, 192, 193, 212, 213]
private theorem finish0491Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0491Input0) = fromList finish0491Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0491 : finishSupport ⟨true, bits4 4⟩ support1357 = 1 • support1358 := by
  have hs : support1357 = fromList finish0491Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0491Chunk0]
  have hn : (finish0491Raw0 : Multiset ℕ) = 1 • (supportNumbers1358 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1358] using hm

private def finish0492Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 288, 289, 290, 291, 308, 309, 310, 311, 416, 417, 418, 419, 436, 437, 438, 439]
private def finish0492Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 52, 53, 54, 55, 180, 181, 182, 183]
private theorem finish0492Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0492Input0) = fromList finish0492Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0492 : finishSupport ⟨false, bits4 4⟩ support1360 = 1 • support1361 := by
  have hs : support1360 = fromList finish0492Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0492Chunk0]
  have hn : (finish0492Raw0 : Multiset ℕ) = 1 • (supportNumbers1361 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1361] using hm

private def finish0493Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 288, 289, 290, 291, 308, 309, 310, 311, 416, 417, 418, 419, 436, 437, 438, 439, 576, 577, 578, 579, 596, 597, 598, 599, 704, 705, 706, 707, 724, 725, 726, 727, 864, 865, 866, 867, 884, 885, 886, 887, 992, 993, 994, 995, 1012, 1013, 1014, 1015]
private def finish0493Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 32, 33, 34, 35, 52, 53, 54, 55, 160, 161, 162, 163, 180, 181, 182, 183, 64, 65, 66, 67, 84, 85, 86, 87, 192, 193, 194, 195, 212, 213, 214, 215, 96, 97, 98, 99, 116, 117, 118, 119, 224, 225, 226, 227, 244, 245, 246, 247]
private theorem finish0493Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0493Input0) = fromList finish0493Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0493 : finishSupport ⟨true, bits4 4⟩ support1362 = 1 • support1363 := by
  have hs : support1362 = fromList finish0493Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0493Chunk0]
  have hn : (finish0493Raw0 : Multiset ℕ) = 1 • (supportNumbers1363 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1363] using hm

private def finish0494Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 296, 297, 298, 299, 316, 317, 318, 319]
private def finish0494Raw0 : List ℕ := [0, 1, 2, 3, 60, 61, 62, 63]
private theorem finish0494Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0494Input0) = fromList finish0494Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0494 : finishSupport ⟨false, bits4 4⟩ support1365 = 1 • support0571 := by
  have hs : support1365 = fromList finish0494Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0494Chunk0]
  have hn : (finish0494Raw0 : Multiset ℕ) = 1 • (supportNumbers0571 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0571] using hm

private def finish0495Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 296, 297, 298, 299, 316, 317, 318, 319, 576, 577, 578, 579, 596, 597, 598, 599, 872, 873, 874, 875, 892, 893, 894, 895]
private def finish0495Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 40, 41, 42, 43, 60, 61, 62, 63, 64, 65, 66, 67, 84, 85, 86, 87, 104, 105, 106, 107, 124, 125, 126, 127]
private theorem finish0495Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0495Input0) = fromList finish0495Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0495 : finishSupport ⟨true, bits4 4⟩ support1366 = 1 • support1367 := by
  have hs : support1366 = fromList finish0495Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0495Chunk0]
  have hn : (finish0495Raw0 : Multiset ℕ) = 1 • (supportNumbers1367 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1367] using hm

private def finish0496Input0 : List ℕ := [0, 4, 65, 69, 128, 132, 193, 197]
private def finish0496Raw0 : List ℕ := [0, 65, 128, 193]
private theorem finish0496Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0496Input0) = fromList finish0496Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0496 : finishSupport ⟨false, bits4 4⟩ support1372 = 1 • support1373 := by
  have hs : support1372 = fromList finish0496Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0496Chunk0]
  have hn : (finish0496Raw0 : Multiset ℕ) = 1 • (supportNumbers1373 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1373] using hm

private def finish0497Input0 : List ℕ := [0, 4, 65, 69, 128, 132, 193, 197, 515, 519, 578, 582, 643, 647, 706, 710]
private def finish0497Raw0 : List ℕ := [0, 4, 65, 69, 128, 132, 193, 197, 3, 7, 66, 70, 131, 135, 194, 198]
private theorem finish0497Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0497Input0) = fromList finish0497Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0497 : finishSupport ⟨true, bits4 4⟩ support1374 = 1 • support1375 := by
  have hs : support1374 = fromList finish0497Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0497Chunk0]
  have hn : (finish0497Raw0 : Multiset ℕ) = 1 • (supportNumbers1375 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1375] using hm

private def finish0498Input0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 130, 134, 138, 142, 195, 199, 203, 207]
private def finish0498Raw0 : List ℕ := [0, 8, 65, 73, 130, 138, 195, 203]
private theorem finish0498Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0498Input0) = fromList finish0498Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0498 : finishSupport ⟨false, bits4 4⟩ support1377 = 1 • support1378 := by
  have hs : support1377 = fromList finish0498Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0498Chunk0]
  have hn : (finish0498Raw0 : Multiset ℕ) = 1 • (supportNumbers1378 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1378] using hm

private def finish0499Input0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 130, 134, 138, 142, 195, 199, 203, 207, 515, 519, 523, 527, 578, 582, 586, 590, 641, 645, 649, 653, 704, 708, 712, 716]
private def finish0499Raw0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 130, 134, 138, 142, 195, 199, 203, 207, 3, 7, 11, 15, 66, 70, 74, 78, 129, 133, 137, 141, 192, 196, 200, 204]
private theorem finish0499Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0499Input0) = fromList finish0499Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0499 : finishSupport ⟨true, bits4 4⟩ support1379 = 1 • support0613 := by
  have hs : support1379 = fromList finish0499Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0499Chunk0]
  have hn : (finish0499Raw0 : Multiset ℕ) = 1 • (supportNumbers0613 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0613] using hm

private def finish0500Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 296, 298, 300, 302, 361, 363, 365, 367, 424, 426, 428, 430, 489, 491, 493, 495]
private def finish0500Raw0 : List ℕ := [0, 2, 65, 67, 128, 130, 193, 195, 44, 46, 109, 111, 172, 174, 237, 239]
private theorem finish0500Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0500Input0) = fromList finish0500Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0500 : finishSupport ⟨false, bits4 4⟩ support1383 = 1 • support1384 := by
  have hs : support1383 = fromList finish0500Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0500Chunk0]
  have hn : (finish0500Raw0 : Multiset ℕ) = 1 • (supportNumbers1384 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1384] using hm

private def finish0501Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 296, 298, 300, 302, 361, 363, 365, 367, 424, 426, 428, 430, 489, 491, 493, 495, 513, 515, 517, 519, 576, 578, 580, 582, 641, 643, 645, 647, 704, 706, 708, 710, 809, 811, 813, 815, 872, 874, 876, 878, 937, 939, 941, 943, 1000, 1002, 1004, 1006]
private def finish0501Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 40, 42, 44, 46, 105, 107, 109, 111, 168, 170, 172, 174, 233, 235, 237, 239, 1, 3, 5, 7, 64, 66, 68, 70, 129, 131, 133, 135, 192, 194, 196, 198, 41, 43, 45, 47, 104, 106, 108, 110, 169, 171, 173, 175, 232, 234, 236, 238]
private theorem finish0501Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0501Input0) = fromList finish0501Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0501 : finishSupport ⟨true, bits4 4⟩ support1385 = 1 • support0954 := by
  have hs : support1385 = fromList finish0501Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0501Chunk0]
  have hn : (finish0501Raw0 : Multiset ℕ) = 1 • (supportNumbers0954 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0954] using hm

private def finish0502Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 297, 299, 301, 303, 360, 362, 364, 366]
private def finish0502Raw0 : List ℕ := [0, 2, 65, 67, 45, 47, 108, 110]
private theorem finish0502Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0502Input0) = fromList finish0502Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0502 : finishSupport ⟨false, bits4 4⟩ support1387 = 1 • support1388 := by
  have hs : support1387 = fromList finish0502Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0502Chunk0]
  have hn : (finish0502Raw0 : Multiset ℕ) = 1 • (supportNumbers1388 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1388] using hm

private def finish0503Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 297, 299, 301, 303, 360, 362, 364, 366, 513, 515, 517, 519, 576, 578, 580, 582, 808, 810, 812, 814, 873, 875, 877, 879]
private def finish0503Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 41, 43, 45, 47, 104, 106, 108, 110, 1, 3, 5, 7, 64, 66, 68, 70, 40, 42, 44, 46, 105, 107, 109, 111]
private theorem finish0503Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0503Input0) = fromList finish0503Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0503 : finishSupport ⟨true, bits4 4⟩ support1389 = 1 • support0518 := by
  have hs : support1389 = fromList finish0503Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0503Chunk0]
  have hn : (finish0503Raw0 : Multiset ℕ) = 1 • (supportNumbers0518 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0518] using hm

private def finish0504Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 297, 299, 301, 303, 360, 362, 364, 366, 416, 418, 420, 422, 481, 483, 485, 487]
private def finish0504Raw0 : List ℕ := [0, 2, 65, 67, 137, 139, 200, 202, 45, 47, 108, 110, 164, 166, 229, 231]
private theorem finish0504Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0504Input0) = fromList finish0504Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0504 : finishSupport ⟨false, bits4 4⟩ support1392 = 1 • support1393 := by
  have hs : support1392 = fromList finish0504Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0504Chunk0]
  have hn : (finish0504Raw0 : Multiset ℕ) = 1 • (supportNumbers1393 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1393] using hm

private def finish0505Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 297, 299, 301, 303, 360, 362, 364, 366, 416, 418, 420, 422, 481, 483, 485, 487, 513, 515, 517, 519, 576, 578, 580, 582, 648, 650, 652, 654, 713, 715, 717, 719, 808, 810, 812, 814, 873, 875, 877, 879, 929, 931, 933, 935, 992, 994, 996, 998]
private def finish0505Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 41, 43, 45, 47, 104, 106, 108, 110, 160, 162, 164, 166, 225, 227, 229, 231, 1, 3, 5, 7, 64, 66, 68, 70, 136, 138, 140, 142, 201, 203, 205, 207, 40, 42, 44, 46, 105, 107, 109, 111, 161, 163, 165, 167, 224, 226, 228, 230]
private theorem finish0505Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0505Input0) = fromList finish0505Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0505 : finishSupport ⟨true, bits4 4⟩ support1394 = 1 • support0612 := by
  have hs : support1394 = fromList finish0505Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0505Chunk0]
  have hn : (finish0505Raw0 : Multiset ℕ) = 1 • (supportNumbers0612 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0612] using hm

private def finish0506Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private def finish0506Raw0 : List ℕ := [0, 2, 9, 11, 65, 67, 72, 74, 128, 130, 137, 139, 193, 195, 200, 202]
private theorem finish0506Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0506Input0) = fromList finish0506Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0506 : finishSupport ⟨false, bits4 4⟩ support0388 = 1 • support1395 := by
  have hs : support0388 = fromList finish0506Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0506Chunk0]
  have hn : (finish0506Raw0 : Multiset ℕ) = 1 • (supportNumbers1395 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1395] using hm

private def finish0507Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 641, 643, 645, 647, 648, 650, 652, 654, 704, 706, 708, 710, 713, 715, 717, 719]
private def finish0507Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 1, 3, 5, 7, 8, 10, 12, 14, 64, 66, 68, 70, 73, 75, 77, 79, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private theorem finish0507Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0507Input0) = fromList finish0507Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0507 : finishSupport ⟨true, bits4 4⟩ support1396 = 1 • support0148 := by
  have hs : support1396 = fromList finish0507Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0507Chunk0]
  have hn : (finish0507Raw0 : Multiset ℕ) = 1 • (supportNumbers0148 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0148] using hm

private def finish0508Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 417, 419, 421, 423, 424, 426, 428, 430, 480, 482, 484, 486, 489, 491, 493, 495]
private def finish0508Raw0 : List ℕ := [0, 2, 9, 11, 65, 67, 72, 74, 165, 167, 172, 174, 228, 230, 237, 239]
private theorem finish0508Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0508Input0) = fromList finish0508Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0508 : finishSupport ⟨false, bits4 4⟩ support1399 = 1 • support1400 := by
  have hs : support1399 = fromList finish0508Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0508Chunk0]
  have hn : (finish0508Raw0 : Multiset ℕ) = 1 • (supportNumbers1400 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1400] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
