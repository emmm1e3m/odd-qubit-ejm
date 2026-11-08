import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1353Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 513, 515, 520, 522, 640, 642, 649, 651]
private def transition1353Raw0 : List ℕ := [0, 544, 2, 546, 9, 553, 11, 555, 129, 673, 131, 675, 136, 680, 138, 682, 257, 801, 259, 803, 264, 808, 266, 810, 384, 928, 386, 930, 393, 937, 395, 939]
private theorem transition1353Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1353Input0) = fromList transition1353Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1353 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0184 = 1 • support1071 := by
  have hs : support0184 = fromList transition1353Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1353Chunk0]
  have hn : (transition1353Raw0 : Multiset ℕ) = 1 • (supportNumbers1071 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1071] using hm

private def transition1354Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 257, 259, 264, 266, 384, 386, 393, 395]
private def transition1354Raw0 : List ℕ := [0, 2, 129, 131, 8, 10, 137, 139]
private theorem transition1354Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1354Input0) = fromList transition1354Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1354 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0185 = 1 • support0268 := by
  have hs : support0185 = fromList transition1354Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1354Chunk0]
  have hn : (transition1354Raw0 : Multiset ℕ) = 1 • (supportNumbers0268 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0268] using hm

private def transition1355Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 257, 259, 264, 266, 384, 386, 393, 395]
private def transition1355Raw0 : List ℕ := [0, 2, 649, 651, 129, 131, 520, 522, 641, 643, 8, 10, 512, 514, 137, 139]
private theorem transition1355Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1355Input0) = fromList transition1355Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1355 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0185 = 1 • support0269 := by
  have hs : support0185 = fromList transition1355Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1355Chunk0]
  have hn : (transition1355Raw0 : Multiset ℕ) = 1 • (supportNumbers0269 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0269] using hm

private def transition1356Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 257, 259, 264, 266, 384, 386, 393, 395]
private def transition1356Raw0 : List ℕ := [0, 2, 129, 131, 8, 10, 137, 139]
private theorem transition1356Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1356Input0) = fromList transition1356Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1356 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0185 = 1 • support0268 := by
  have hs : support0185 = fromList transition1356Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1356Chunk0]
  have hn : (transition1356Raw0 : Multiset ℕ) = 1 • (supportNumbers0268 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0268] using hm

private def transition1357Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 257, 259, 264, 266, 384, 386, 393, 395]
private def transition1357Raw0 : List ℕ := [0, 2, 553, 555, 129, 131, 680, 682, 545, 547, 8, 10, 672, 674, 137, 139]
private theorem transition1357Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1357Input0) = fromList transition1357Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1357 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0185 = 1 • support1310 := by
  have hs : support0185 = fromList transition1357Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1357Chunk0]
  have hn : (transition1357Raw0 : Multiset ℕ) = 1 • (supportNumbers1310 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1310] using hm

private def transition1358Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 545, 547, 553, 555, 672, 674, 680, 682]
private def transition1358Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 289, 291, 297, 299, 416, 418, 424, 426]
private theorem transition1358Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1358Input0) = fromList transition1358Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1358 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1310 = 1 • support1311 := by
  have hs : support1310 = fromList transition1358Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1358Chunk0]
  have hn : (transition1358Raw0 : Multiset ℕ) = 1 • (supportNumbers1311 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1311] using hm

private def transition1359Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 545, 547, 553, 555, 672, 674, 680, 682]
private def transition1359Raw0 : List ℕ := [0, 576, 2, 578, 8, 584, 10, 586, 129, 705, 131, 707, 137, 713, 139, 715, 289, 865, 291, 867, 297, 873, 299, 875, 416, 992, 418, 994, 424, 1000, 426, 1002]
private theorem transition1359Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1359Input0) = fromList transition1359Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1359 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1310 = 1 • support1312 := by
  have hs : support1310 = fromList transition1359Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1359Chunk0]
  have hn : (transition1359Raw0 : Multiset ℕ) = 1 • (supportNumbers1312 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1312] using hm

private def transition1360Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 257, 259, 264, 266, 384, 386, 393, 395, 513, 515, 520, 522, 640, 642, 649, 651, 768, 770, 777, 779, 897, 899, 904, 906]
private def transition1360Raw0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 1, 3, 8, 10, 128, 130, 137, 139, 257, 259, 264, 266, 384, 386, 393, 395, 256, 258, 265, 267, 385, 387, 392, 394]
private theorem transition1360Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1360Input0) = fromList transition1360Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1360 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0186 = 1 • support0061 := by
  have hs : support0186 = fromList transition1360Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1360Chunk0]
  have hn : (transition1360Raw0 : Multiset ℕ) = 1 • (supportNumbers0061 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0061] using hm

private def transition1361Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 257, 259, 264, 266, 384, 386, 393, 395, 513, 515, 520, 522, 640, 642, 649, 651, 768, 770, 777, 779, 897, 899, 904, 906]
private def transition1361Raw0 : List ℕ := [0, 640, 2, 642, 9, 649, 11, 651, 129, 513, 131, 515, 136, 520, 138, 522, 1, 641, 3, 643, 8, 648, 10, 650, 128, 512, 130, 514, 137, 521, 139, 523, 257, 897, 259, 899, 264, 904, 266, 906, 384, 768, 386, 770, 393, 777, 395, 779, 256, 896, 258, 898, 265, 905, 267, 907, 385, 769, 387, 771, 392, 776, 394, 778]
private theorem transition1361Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1361Input0) = fromList transition1361Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1361 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0186 = 1 • support0062 := by
  have hs : support0186 = fromList transition1361Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1361Chunk0]
  have hn : (transition1361Raw0 : Multiset ℕ) = 1 • (supportNumbers0062 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0062] using hm

private def transition1362Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 257, 259, 264, 266, 384, 386, 393, 395, 513, 515, 520, 522, 640, 642, 649, 651, 768, 770, 777, 779, 897, 899, 904, 906]
private def transition1362Raw0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 1, 3, 8, 10, 128, 130, 137, 139, 257, 259, 264, 266, 384, 386, 393, 395, 256, 258, 265, 267, 385, 387, 392, 394]
private theorem transition1362Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1362Input0) = fromList transition1362Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1362 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0186 = 1 • support0061 := by
  have hs : support0186 = fromList transition1362Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1362Chunk0]
  have hn : (transition1362Raw0 : Multiset ℕ) = 1 • (supportNumbers0061 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0061] using hm

private def transition1363Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 257, 259, 264, 266, 384, 386, 393, 395, 513, 515, 520, 522, 640, 642, 649, 651, 768, 770, 777, 779, 897, 899, 904, 906]
private def transition1363Raw0 : List ℕ := [0, 544, 2, 546, 9, 553, 11, 555, 129, 673, 131, 675, 136, 680, 138, 682, 1, 545, 3, 547, 8, 552, 10, 554, 128, 672, 130, 674, 137, 681, 139, 683, 257, 801, 259, 803, 264, 808, 266, 810, 384, 928, 386, 930, 393, 937, 395, 939, 256, 800, 258, 802, 265, 809, 267, 811, 385, 929, 387, 931, 392, 936, 394, 938]
private theorem transition1363Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1363Input0) = fromList transition1363Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1363 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0186 = 1 • support0680 := by
  have hs : support0186 = fromList transition1363Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1363Chunk0]
  have hn : (transition1363Raw0 : Multiset ℕ) = 1 • (supportNumbers0680 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0680] using hm

private def transition1364Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private def transition1364Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem transition1364Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1364Input0) = fromList transition1364Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1364 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0187 = 1 • support0187 := by
  have hs : support0187 = fromList transition1364Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1364Chunk0]
  have hn : (transition1364Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def transition1365Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private def transition1365Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem transition1365Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1365Input0) = fromList transition1365Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1365 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0187 = 1 • support0187 := by
  have hs : support0187 = fromList transition1365Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1365Chunk0]
  have hn : (transition1365Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def transition1366Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private def transition1366Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem transition1366Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1366Input0) = fromList transition1366Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1366 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0187 = 1 • support0187 := by
  have hs : support0187 = fromList transition1366Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1366Chunk0]
  have hn : (transition1366Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def transition1367Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private def transition1367Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem transition1367Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1367Input0) = fromList transition1367Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1367 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0187 = 1 • support0187 := by
  have hs : support0187 = fromList transition1367Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1367Chunk0]
  have hn : (transition1367Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def transition1368Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private def transition1368Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem transition1368Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1368Input0) = fromList transition1368Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1368 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0187 = 1 • support0187 := by
  have hs : support0187 = fromList transition1368Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1368Chunk0]
  have hn : (transition1368Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def transition1369Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private def transition1369Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 128, 704, 129, 705, 130, 706, 131, 707]
private theorem transition1369Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1369Input0) = fromList transition1369Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1369 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0187 = 1 • support1314 := by
  have hs : support0187 = fromList transition1369Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1369Chunk0]
  have hn : (transition1369Raw0 : Multiset ℕ) = 1 • (supportNumbers1314 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1314] using hm

private def transition1370Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 520, 521, 522, 523, 648, 649, 650, 651]
private def transition1370Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 264, 265, 266, 267, 392, 393, 394, 395]
private theorem transition1370Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1370Input0) = fromList transition1370Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1370 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0188 = 1 • support0270 := by
  have hs : support0188 = fromList transition1370Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1370Chunk0]
  have hn : (transition1370Raw0 : Multiset ℕ) = 1 • (supportNumbers0270 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0270] using hm

private def transition1371Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 520, 521, 522, 523, 648, 649, 650, 651]
private def transition1371Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 128, 512, 129, 513, 130, 514, 131, 515, 264, 904, 265, 905, 266, 906, 267, 907, 392, 776, 393, 777, 394, 778, 395, 779]
private theorem transition1371Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1371Input0) = fromList transition1371Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1371 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0188 = 1 • support0271 := by
  have hs : support0188 = fromList transition1371Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1371Chunk0]
  have hn : (transition1371Raw0 : Multiset ℕ) = 1 • (supportNumbers0271 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0271] using hm

private def transition1372Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 520, 521, 522, 523, 648, 649, 650, 651]
private def transition1372Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 264, 265, 266, 267, 392, 393, 394, 395]
private theorem transition1372Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1372Input0) = fromList transition1372Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1372 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0188 = 1 • support0270 := by
  have hs : support0188 = fromList transition1372Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1372Chunk0]
  have hn : (transition1372Raw0 : Multiset ℕ) = 1 • (supportNumbers0270 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0270] using hm

private def transition1373Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 264, 265, 266, 267, 392, 393, 394, 395]
private def transition1373Raw0 : List ℕ := [0, 1, 128, 129, 10, 11, 138, 139]
private theorem transition1373Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1373Input0) = fromList transition1373Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1373 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0270 = 1 • support1136 := by
  have hs : support0270 = fromList transition1373Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1373Chunk0]
  have hn : (transition1373Raw0 : Multiset ℕ) = 1 • (supportNumbers1136 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1136] using hm

private def transition1374Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 264, 265, 266, 267, 392, 393, 394, 395]
private def transition1374Raw0 : List ℕ := [0, 1, 578, 579, 128, 129, 706, 707, 584, 585, 10, 11, 712, 713, 138, 139]
private theorem transition1374Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1374Input0) = fromList transition1374Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1374 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0270 = 1 • support1316 := by
  have hs : support0270 = fromList transition1374Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1374Chunk0]
  have hn : (transition1374Raw0 : Multiset ℕ) = 1 • (supportNumbers1316 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1316] using hm

private def transition1375Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 520, 521, 522, 523, 648, 649, 650, 651]
private def transition1375Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 128, 672, 129, 673, 130, 674, 131, 675, 264, 808, 265, 809, 266, 810, 267, 811, 392, 936, 393, 937, 394, 938, 395, 939]
private theorem transition1375Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1375Input0) = fromList transition1375Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1375 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0188 = 1 • support1318 := by
  have hs : support0188 = fromList transition1375Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1375Chunk0]
  have hn : (transition1375Raw0 : Multiset ℕ) = 1 • (supportNumbers1318 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1318] using hm

private def transition1376Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 264, 265, 266, 267, 392, 393, 394, 395, 544, 545, 546, 547, 672, 673, 674, 675, 808, 809, 810, 811, 936, 937, 938, 939]
private def transition1376Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 8, 9, 10, 11, 136, 137, 138, 139, 288, 289, 290, 291, 416, 417, 418, 419, 296, 297, 298, 299, 424, 425, 426, 427]
private theorem transition1376Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1376Input0) = fromList transition1376Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1376 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1318 = 1 • support0564 := by
  have hs : support1318 = fromList transition1376Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1376Chunk0]
  have hn : (transition1376Raw0 : Multiset ℕ) = 1 • (supportNumbers0564 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0564] using hm

private def transition1377Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 264, 265, 266, 267, 392, 393, 394, 395, 544, 545, 546, 547, 672, 673, 674, 675, 808, 809, 810, 811, 936, 937, 938, 939]
private def transition1377Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 128, 704, 129, 705, 130, 706, 131, 707, 8, 584, 9, 585, 10, 586, 11, 587, 136, 712, 137, 713, 138, 714, 139, 715, 288, 864, 289, 865, 290, 866, 291, 867, 416, 992, 417, 993, 418, 994, 419, 995, 296, 872, 297, 873, 298, 874, 299, 875, 424, 1000, 425, 1001, 426, 1002, 427, 1003]
private theorem transition1377Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1377Input0) = fromList transition1377Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1377 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1318 = 1 • support0565 := by
  have hs : support1318 = fromList transition1377Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1377Chunk0]
  have hn : (transition1377Raw0 : Multiset ℕ) = 1 • (supportNumbers0565 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0565] using hm

private def transition1378Input0 : List ℕ := [0, 1, 2, 3, 384, 385, 386, 387]
private def transition1378Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition1378Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1378Input0) = fromList transition1378Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1378 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0189 = 1 • support0030 := by
  have hs : support0189 = fromList transition1378Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1378Chunk0]
  have hn : (transition1378Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition1379Input0 : List ℕ := [0, 1, 2, 3, 384, 385, 386, 387]
private def transition1379Raw0 : List ℕ := [0, 1, 2, 3, 512, 513, 514, 515]
private theorem transition1379Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1379Input0) = fromList transition1379Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1379 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0189 = 1 • support0272 := by
  have hs : support0189 = fromList transition1379Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1379Chunk0]
  have hn : (transition1379Raw0 : Multiset ℕ) = 1 • (supportNumbers0272 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0272] using hm

private def transition1380Input0 : List ℕ := [0, 1, 2, 3, 384, 385, 386, 387]
private def transition1380Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition1380Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1380Input0) = fromList transition1380Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1380 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0189 = 1 • support0030 := by
  have hs : support0189 = fromList transition1380Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1380Chunk0]
  have hn : (transition1380Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition1381Input0 : List ℕ := [0, 1, 2, 3, 384, 385, 386, 387]
private def transition1381Raw0 : List ℕ := [0, 1, 2, 3, 672, 673, 674, 675]
private theorem transition1381Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1381Input0) = fromList transition1381Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1381 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0189 = 1 • support1319 := by
  have hs : support0189 = fromList transition1381Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1381Chunk0]
  have hn : (transition1381Raw0 : Multiset ℕ) = 1 • (supportNumbers1319 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1319] using hm

private def transition1382Input0 : List ℕ := [0, 1, 2, 3, 672, 673, 674, 675]
private def transition1382Raw0 : List ℕ := [0, 1, 2, 3, 416, 417, 418, 419]
private theorem transition1382Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1382Input0) = fromList transition1382Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1382 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1319 = 1 • support1320 := by
  have hs : support1319 = fromList transition1382Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1382Chunk0]
  have hn : (transition1382Raw0 : Multiset ℕ) = 1 • (supportNumbers1320 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1320] using hm

private def transition1383Input0 : List ℕ := [0, 1, 2, 3, 672, 673, 674, 675]
private def transition1383Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 416, 992, 417, 993, 418, 994, 419, 995]
private theorem transition1383Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1383Input0) = fromList transition1383Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1383 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1319 = 1 • support1321 := by
  have hs : support1319 = fromList transition1383Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1383Chunk0]
  have hn : (transition1383Raw0 : Multiset ℕ) = 1 • (supportNumbers1321 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1321] using hm

private def transition1384Input0 : List ℕ := [0, 1, 2, 3, 384, 385, 386, 387, 640, 641, 642, 643, 768, 769, 770, 771]
private def transition1384Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 384, 385, 386, 387, 256, 257, 258, 259]
private theorem transition1384Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1384Input0) = fromList transition1384Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1384 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0190 = 1 • support0273 := by
  have hs : support0190 = fromList transition1384Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1384Chunk0]
  have hn : (transition1384Raw0 : Multiset ℕ) = 1 • (supportNumbers0273 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0273] using hm

private def transition1385Input0 : List ℕ := [0, 1, 2, 3, 384, 385, 386, 387, 640, 641, 642, 643, 768, 769, 770, 771]
private def transition1385Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 128, 512, 129, 513, 130, 514, 131, 515, 384, 768, 385, 769, 386, 770, 387, 771, 256, 896, 257, 897, 258, 898, 259, 899]
private theorem transition1385Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1385Input0) = fromList transition1385Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1385 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0190 = 1 • support0274 := by
  have hs : support0190 = fromList transition1385Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1385Chunk0]
  have hn : (transition1385Raw0 : Multiset ℕ) = 1 • (supportNumbers0274 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0274] using hm

private def transition1386Input0 : List ℕ := [0, 1, 2, 3, 384, 385, 386, 387, 640, 641, 642, 643, 768, 769, 770, 771]
private def transition1386Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 384, 385, 386, 387, 256, 257, 258, 259]
private theorem transition1386Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1386Input0) = fromList transition1386Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1386 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0190 = 1 • support0273 := by
  have hs : support0190 = fromList transition1386Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1386Chunk0]
  have hn : (transition1386Raw0 : Multiset ℕ) = 1 • (supportNumbers0273 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0273] using hm

private def transition1387Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 256, 257, 258, 259, 384, 385, 386, 387]
private def transition1387Raw0 : List ℕ := [0, 1, 128, 129, 2, 3, 130, 131]
private theorem transition1387Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1387Input0) = fromList transition1387Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1387 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0273 = 1 • support0187 := by
  have hs : support0273 = fromList transition1387Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1387Chunk0]
  have hn : (transition1387Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def transition1388Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 256, 257, 258, 259, 384, 385, 386, 387]
private def transition1388Raw0 : List ℕ := [0, 1, 578, 579, 128, 129, 706, 707, 576, 577, 2, 3, 704, 705, 130, 131]
private theorem transition1388Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1388Input0) = fromList transition1388Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1388 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0273 = 1 • support1314 := by
  have hs : support0273 = fromList transition1388Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1388Chunk0]
  have hn : (transition1388Raw0 : Multiset ℕ) = 1 • (supportNumbers1314 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1314] using hm

private def transition1389Input0 : List ℕ := [0, 1, 2, 3, 384, 385, 386, 387, 640, 641, 642, 643, 768, 769, 770, 771]
private def transition1389Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 128, 672, 129, 673, 130, 674, 131, 675, 384, 928, 385, 929, 386, 930, 387, 931, 256, 800, 257, 801, 258, 802, 259, 803]
private theorem transition1389Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1389Input0) = fromList transition1389Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1389 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0190 = 1 • support1323 := by
  have hs : support0190 = fromList transition1389Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1389Chunk0]
  have hn : (transition1389Raw0 : Multiset ℕ) = 1 • (supportNumbers1323 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1323] using hm

private def transition1390Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 256, 257, 258, 259, 384, 385, 386, 387, 544, 545, 546, 547, 672, 673, 674, 675, 800, 801, 802, 803, 928, 929, 930, 931]
private def transition1390Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 0, 1, 2, 3, 128, 129, 130, 131, 288, 289, 290, 291, 416, 417, 418, 419, 288, 289, 290, 291, 416, 417, 418, 419]
private theorem transition1390Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1390Input0) = fromList transition1390Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1390 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1323 = 2 • support1081 := by
  have hs : support1323 = fromList transition1390Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1390Chunk0]
  have hn : (transition1390Raw0 : Multiset ℕ) = 2 • (supportNumbers1081 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1081] using hm

private def transition1391Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 256, 257, 258, 259, 384, 385, 386, 387, 544, 545, 546, 547, 672, 673, 674, 675, 800, 801, 802, 803, 928, 929, 930, 931]
private def transition1391Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 128, 704, 129, 705, 130, 706, 131, 707, 0, 576, 1, 577, 2, 578, 3, 579, 128, 704, 129, 705, 130, 706, 131, 707, 288, 864, 289, 865, 290, 866, 291, 867, 416, 992, 417, 993, 418, 994, 419, 995, 288, 864, 289, 865, 290, 866, 291, 867, 416, 992, 417, 993, 418, 994, 419, 995]
private theorem transition1391Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1391Input0) = fromList transition1391Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1391 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1323 = 2 • support1082 := by
  have hs : support1323 = fromList transition1391Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1391Chunk0]
  have hn : (transition1391Raw0 : Multiset ℕ) = 2 • (supportNumbers1082 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1082] using hm

private def transition1392Input0 : List ℕ := [0, 1, 2, 3, 540, 541, 542, 543]
private def transition1392Raw0 : List ℕ := [0, 1, 2, 3, 284, 285, 286, 287]
private theorem transition1392Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1392Input0) = fromList transition1392Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1392 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0191 = 1 • support0275 := by
  have hs : support0191 = fromList transition1392Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1392Chunk0]
  have hn : (transition1392Raw0 : Multiset ℕ) = 1 • (supportNumbers0275 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0275] using hm

private def transition1393Input0 : List ℕ := [0, 1, 2, 3, 540, 541, 542, 543]
private def transition1393Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 284, 924, 285, 925, 286, 926, 287, 927]
private theorem transition1393Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1393Input0) = fromList transition1393Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1393 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0191 = 1 • support0276 := by
  have hs : support0191 = fromList transition1393Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1393Chunk0]
  have hn : (transition1393Raw0 : Multiset ℕ) = 1 • (supportNumbers0276 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0276] using hm

private def transition1394Input0 : List ℕ := [0, 1, 2, 3, 540, 541, 542, 543]
private def transition1394Raw0 : List ℕ := [0, 1, 2, 3, 284, 285, 286, 287]
private theorem transition1394Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1394Input0) = fromList transition1394Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1394 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0191 = 1 • support0275 := by
  have hs : support0191 = fromList transition1394Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1394Chunk0]
  have hn : (transition1394Raw0 : Multiset ℕ) = 1 • (supportNumbers0275 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0275] using hm

private def transition1395Input0 : List ℕ := [0, 1, 2, 3, 284, 285, 286, 287]
private def transition1395Raw0 : List ℕ := [0, 1, 30, 31]
private theorem transition1395Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1395Input0) = fromList transition1395Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1395 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0275 = 1 • support1324 := by
  have hs : support0275 = fromList transition1395Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1395Chunk0]
  have hn : (transition1395Raw0 : Multiset ℕ) = 1 • (supportNumbers1324 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1324] using hm

private def transition1396Input0 : List ℕ := [0, 1, 2, 3, 284, 285, 286, 287]
private def transition1396Raw0 : List ℕ := [0, 1, 578, 579, 604, 605, 30, 31]
private theorem transition1396Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1396Input0) = fromList transition1396Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1396 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0275 = 1 • support1325 := by
  have hs : support0275 = fromList transition1396Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1396Chunk0]
  have hn : (transition1396Raw0 : Multiset ℕ) = 1 • (supportNumbers1325 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1325] using hm

private def transition1397Input0 : List ℕ := [0, 1, 2, 3, 540, 541, 542, 543]
private def transition1397Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 284, 828, 285, 829, 286, 830, 287, 831]
private theorem transition1397Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1397Input0) = fromList transition1397Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1397 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0191 = 1 • support1327 := by
  have hs : support0191 = fromList transition1397Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1397Chunk0]
  have hn : (transition1397Raw0 : Multiset ℕ) = 1 • (supportNumbers1327 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1327] using hm

private def transition1398Input0 : List ℕ := [0, 1, 2, 3, 284, 285, 286, 287, 544, 545, 546, 547, 828, 829, 830, 831]
private def transition1398Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 288, 289, 290, 291, 316, 317, 318, 319]
private theorem transition1398Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1398Input0) = fromList transition1398Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1398 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1327 = 1 • support1328 := by
  have hs : support1327 = fromList transition1398Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1398Chunk0]
  have hn : (transition1398Raw0 : Multiset ℕ) = 1 • (supportNumbers1328 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1328] using hm

private def transition1399Input0 : List ℕ := [0, 1, 2, 3, 284, 285, 286, 287, 544, 545, 546, 547, 828, 829, 830, 831]
private def transition1399Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 288, 864, 289, 865, 290, 866, 291, 867, 316, 892, 317, 893, 318, 894, 319, 895]
private theorem transition1399Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1399Input0) = fromList transition1399Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1399 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1327 = 1 • support1329 := by
  have hs : support1327 = fromList transition1399Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1399Chunk0]
  have hn : (transition1399Raw0 : Multiset ℕ) = 1 • (supportNumbers1329 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1329] using hm

private def transition1400Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 540, 541, 542, 543, 640, 641, 642, 643]
private def transition1400Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 284, 285, 286, 287, 384, 385, 386, 387]
private theorem transition1400Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1400Input0) = fromList transition1400Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1400 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0192 = 1 • support0118 := by
  have hs : support0192 = fromList transition1400Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1400Chunk0]
  have hn : (transition1400Raw0 : Multiset ℕ) = 1 • (supportNumbers0118 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0118] using hm

private def transition1401Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 540, 541, 542, 543, 640, 641, 642, 643]
private def transition1401Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 156, 540, 157, 541, 158, 542, 159, 543, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771]
private theorem transition1401Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1401Input0) = fromList transition1401Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1401 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0192 = 1 • support0119 := by
  have hs : support0192 = fromList transition1401Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1401Chunk0]
  have hn : (transition1401Raw0 : Multiset ℕ) = 1 • (supportNumbers0119 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0119] using hm

private def transition1402Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 540, 541, 542, 543, 640, 641, 642, 643]
private def transition1402Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 284, 285, 286, 287, 384, 385, 386, 387]
private theorem transition1402Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1402Input0) = fromList transition1402Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1402 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0192 = 1 • support0118 := by
  have hs : support0192 = fromList transition1402Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1402Chunk0]
  have hn : (transition1402Raw0 : Multiset ℕ) = 1 • (supportNumbers0118 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0118] using hm

private def transition1403Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 540, 541, 542, 543, 640, 641, 642, 643]
private def transition1403Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 156, 700, 157, 701, 158, 702, 159, 703, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931]
private theorem transition1403Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1403Input0) = fromList transition1403Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1403 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0192 = 1 • support0860 := by
  have hs : support0192 = fromList transition1403Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1403Chunk0]
  have hn : (transition1403Raw0 : Multiset ℕ) = 1 • (supportNumbers0860 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0860] using hm

private def transition1404Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 512, 513, 514, 515, 540, 541, 542, 543]
private def transition1404Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 256, 257, 258, 259, 284, 285, 286, 287]
private theorem transition1404Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1404Input0) = fromList transition1404Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1404 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0193 = 1 • support0277 := by
  have hs : support0193 = fromList transition1404Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1404Chunk0]
  have hn : (transition1404Raw0 : Multiset ℕ) = 1 • (supportNumbers0277 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0277] using hm

private def transition1405Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 512, 513, 514, 515, 540, 541, 542, 543]
private def transition1405Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 256, 896, 257, 897, 258, 898, 259, 899, 284, 924, 285, 925, 286, 926, 287, 927]
private theorem transition1405Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1405Input0) = fromList transition1405Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1405 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0193 = 1 • support0278 := by
  have hs : support0193 = fromList transition1405Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1405Chunk0]
  have hn : (transition1405Raw0 : Multiset ℕ) = 1 • (supportNumbers0278 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0278] using hm

private def transition1406Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 512, 513, 514, 515, 540, 541, 542, 543]
private def transition1406Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 256, 257, 258, 259, 284, 285, 286, 287]
private theorem transition1406Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1406Input0) = fromList transition1406Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1406 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0193 = 1 • support0277 := by
  have hs : support0193 = fromList transition1406Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1406Chunk0]
  have hn : (transition1406Raw0 : Multiset ℕ) = 1 • (supportNumbers0277 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0277] using hm

private def transition1407Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 256, 257, 258, 259, 284, 285, 286, 287]
private def transition1407Raw0 : List ℕ := [0, 1, 28, 29, 2, 3, 30, 31]
private theorem transition1407Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1407Input0) = fromList transition1407Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1407 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0277 = 1 • support0012 := by
  have hs : support0277 = fromList transition1407Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1407Chunk0]
  have hn : (transition1407Raw0 : Multiset ℕ) = 1 • (supportNumbers0012 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0012] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
