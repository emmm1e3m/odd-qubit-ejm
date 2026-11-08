import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1289Input0 : List ℕ := [0, 2, 9, 11]
private def transition1289Raw0 : List ℕ := [0, 640, 2, 642, 9, 649, 11, 651]
private theorem transition1289Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1289Input0) = fromList transition1289Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1289 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0175 = 1 • support0259 := by
  have hs : support0175 = fromList transition1289Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1289Chunk0]
  have hn : (transition1289Raw0 : Multiset ℕ) = 1 • (supportNumbers0259 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0259] using hm

private def transition1290Input0 : List ℕ := [0, 2, 9, 11]
private def transition1290Raw0 : List ℕ := [0, 2, 9, 11]
private theorem transition1290Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1290Input0) = fromList transition1290Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1290 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0175 = 1 • support0175 := by
  have hs : support0175 = fromList transition1290Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1290Chunk0]
  have hn : (transition1290Raw0 : Multiset ℕ) = 1 • (supportNumbers0175 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0175] using hm

private def transition1291Input0 : List ℕ := [0, 2, 9, 11]
private def transition1291Raw0 : List ℕ := [0, 544, 2, 546, 9, 553, 11, 555]
private theorem transition1291Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1291Input0) = fromList transition1291Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1291 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0175 = 1 • support1282 := by
  have hs : support0175 = fromList transition1291Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1291Chunk0]
  have hn : (transition1291Raw0 : Multiset ℕ) = 1 • (supportNumbers1282 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1282] using hm

private def transition1292Input0 : List ℕ := [0, 2, 9, 11, 544, 546, 553, 555]
private def transition1292Raw0 : List ℕ := [0, 2, 9, 11, 288, 290, 297, 299]
private theorem transition1292Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1292Input0) = fromList transition1292Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1292 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1282 = 1 • support0821 := by
  have hs : support1282 = fromList transition1292Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1292Chunk0]
  have hn : (transition1292Raw0 : Multiset ℕ) = 1 • (supportNumbers0821 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0821] using hm

private def transition1293Input0 : List ℕ := [0, 2, 9, 11, 544, 546, 553, 555]
private def transition1293Raw0 : List ℕ := [0, 576, 2, 578, 9, 585, 11, 587, 288, 864, 290, 866, 297, 873, 299, 875]
private theorem transition1293Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1293Input0) = fromList transition1293Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1293 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1282 = 1 • support0822 := by
  have hs : support1282 = fromList transition1293Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1293Chunk0]
  have hn : (transition1293Raw0 : Multiset ℕ) = 1 • (supportNumbers0822 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0822] using hm

private def transition1294Input0 : List ℕ := [0, 2, 9, 11, 384, 386, 393, 395]
private def transition1294Raw0 : List ℕ := [0, 2, 137, 139]
private theorem transition1294Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1294Input0) = fromList transition1294Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1294 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0176 = 1 • support0026 := by
  have hs : support0176 = fromList transition1294Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1294Chunk0]
  have hn : (transition1294Raw0 : Multiset ℕ) = 1 • (supportNumbers0026 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0026] using hm

private def transition1295Input0 : List ℕ := [0, 2, 9, 11, 384, 386, 393, 395]
private def transition1295Raw0 : List ℕ := [0, 2, 649, 651, 512, 514, 137, 139]
private theorem transition1295Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1295Input0) = fromList transition1295Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1295 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0176 = 1 • support0260 := by
  have hs : support0176 = fromList transition1295Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1295Chunk0]
  have hn : (transition1295Raw0 : Multiset ℕ) = 1 • (supportNumbers0260 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0260] using hm

private def transition1296Input0 : List ℕ := [0, 2, 9, 11, 384, 386, 393, 395]
private def transition1296Raw0 : List ℕ := [0, 2, 137, 139]
private theorem transition1296Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1296Input0) = fromList transition1296Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1296 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0176 = 1 • support0026 := by
  have hs : support0176 = fromList transition1296Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1296Chunk0]
  have hn : (transition1296Raw0 : Multiset ℕ) = 1 • (supportNumbers0026 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0026] using hm

private def transition1297Input0 : List ℕ := [0, 2, 9, 11, 384, 386, 393, 395]
private def transition1297Raw0 : List ℕ := [0, 2, 553, 555, 672, 674, 137, 139]
private theorem transition1297Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1297Input0) = fromList transition1297Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1297 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0176 = 1 • support1283 := by
  have hs : support0176 = fromList transition1297Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1297Chunk0]
  have hn : (transition1297Raw0 : Multiset ℕ) = 1 • (supportNumbers1283 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1283] using hm

private def transition1298Input0 : List ℕ := [0, 2, 137, 139, 553, 555, 672, 674]
private def transition1298Raw0 : List ℕ := [0, 2, 137, 139, 297, 299, 416, 418]
private theorem transition1298Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1298Input0) = fromList transition1298Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1298 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1283 = 1 • support1284 := by
  have hs : support1283 = fromList transition1298Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1298Chunk0]
  have hn : (transition1298Raw0 : Multiset ℕ) = 1 • (supportNumbers1284 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1284] using hm

private def transition1299Input0 : List ℕ := [0, 2, 137, 139, 553, 555, 672, 674]
private def transition1299Raw0 : List ℕ := [0, 576, 2, 578, 137, 713, 139, 715, 297, 873, 299, 875, 416, 992, 418, 994]
private theorem transition1299Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1299Input0) = fromList transition1299Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1299 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1283 = 1 • support1285 := by
  have hs : support1283 = fromList transition1299Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1299Chunk0]
  have hn : (transition1299Raw0 : Multiset ℕ) = 1 • (supportNumbers1285 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1285] using hm

private def transition1300Input0 : List ℕ := [0, 2, 9, 11, 384, 386, 393, 395, 640, 642, 649, 651, 768, 770, 777, 779]
private def transition1300Raw0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 384, 386, 393, 395, 256, 258, 265, 267]
private theorem transition1300Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1300Input0) = fromList transition1300Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1300 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0177 = 1 • support0261 := by
  have hs : support0177 = fromList transition1300Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1300Chunk0]
  have hn : (transition1300Raw0 : Multiset ℕ) = 1 • (supportNumbers0261 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0261] using hm

private def transition1301Input0 : List ℕ := [0, 2, 9, 11, 384, 386, 393, 395, 640, 642, 649, 651, 768, 770, 777, 779]
private def transition1301Raw0 : List ℕ := [0, 640, 2, 642, 9, 649, 11, 651, 128, 512, 130, 514, 137, 521, 139, 523, 384, 768, 386, 770, 393, 777, 395, 779, 256, 896, 258, 898, 265, 905, 267, 907]
private theorem transition1301Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1301Input0) = fromList transition1301Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1301 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0177 = 1 • support0262 := by
  have hs : support0177 = fromList transition1301Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1301Chunk0]
  have hn : (transition1301Raw0 : Multiset ℕ) = 1 • (supportNumbers0262 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0262] using hm

private def transition1302Input0 : List ℕ := [0, 2, 9, 11, 384, 386, 393, 395, 640, 642, 649, 651, 768, 770, 777, 779]
private def transition1302Raw0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 384, 386, 393, 395, 256, 258, 265, 267]
private theorem transition1302Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1302Input0) = fromList transition1302Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1302 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0177 = 1 • support0261 := by
  have hs : support0177 = fromList transition1302Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1302Chunk0]
  have hn : (transition1302Raw0 : Multiset ℕ) = 1 • (supportNumbers0261 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0261] using hm

private def transition1303Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 256, 258, 265, 267, 384, 386, 393, 395]
private def transition1303Raw0 : List ℕ := [0, 9, 128, 137, 2, 11, 130, 139]
private theorem transition1303Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1303Input0) = fromList transition1303Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1303 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0261 = 1 • support0351 := by
  have hs : support0261 = fromList transition1303Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1303Chunk0]
  have hn : (transition1303Raw0 : Multiset ℕ) = 1 • (supportNumbers0351 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0351] using hm

private def transition1304Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 256, 258, 265, 267, 384, 386, 393, 395]
private def transition1304Raw0 : List ℕ := [0, 578, 9, 587, 128, 706, 137, 715, 576, 2, 585, 11, 704, 130, 713, 139]
private theorem transition1304Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1304Input0) = fromList transition1304Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1304 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0261 = 1 • support1287 := by
  have hs : support0261 = fromList transition1304Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1304Chunk0]
  have hn : (transition1304Raw0 : Multiset ℕ) = 1 • (supportNumbers1287 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1287] using hm

private def transition1305Input0 : List ℕ := [0, 2, 9, 11, 384, 386, 393, 395, 640, 642, 649, 651, 768, 770, 777, 779]
private def transition1305Raw0 : List ℕ := [0, 544, 2, 546, 9, 553, 11, 555, 128, 672, 130, 674, 137, 681, 139, 683, 384, 928, 386, 930, 393, 937, 395, 939, 256, 800, 258, 802, 265, 809, 267, 811]
private theorem transition1305Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1305Input0) = fromList transition1305Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1305 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0177 = 1 • support1289 := by
  have hs : support0177 = fromList transition1305Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1305Chunk0]
  have hn : (transition1305Raw0 : Multiset ℕ) = 1 • (supportNumbers1289 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1289] using hm

private def transition1306Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 256, 258, 265, 267, 384, 386, 393, 395, 544, 546, 553, 555, 672, 674, 681, 683, 800, 802, 809, 811, 928, 930, 937, 939]
private def transition1306Raw0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 0, 2, 9, 11, 128, 130, 137, 139, 288, 290, 297, 299, 416, 418, 425, 427, 288, 290, 297, 299, 416, 418, 425, 427]
private theorem transition1306Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1306Input0) = fromList transition1306Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1306 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1289 = 2 • support1048 := by
  have hs : support1289 = fromList transition1306Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1306Chunk0]
  have hn : (transition1306Raw0 : Multiset ℕ) = 2 • (supportNumbers1048 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1048] using hm

private def transition1307Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 256, 258, 265, 267, 384, 386, 393, 395, 544, 546, 553, 555, 672, 674, 681, 683, 800, 802, 809, 811, 928, 930, 937, 939]
private def transition1307Raw0 : List ℕ := [0, 576, 2, 578, 9, 585, 11, 587, 128, 704, 130, 706, 137, 713, 139, 715, 0, 576, 2, 578, 9, 585, 11, 587, 128, 704, 130, 706, 137, 713, 139, 715, 288, 864, 290, 866, 297, 873, 299, 875, 416, 992, 418, 994, 425, 1001, 427, 1003, 288, 864, 290, 866, 297, 873, 299, 875, 416, 992, 418, 994, 425, 1001, 427, 1003]
private theorem transition1307Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1307Input0) = fromList transition1307Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1307 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1289 = 2 • support1049 := by
  have hs : support1289 = fromList transition1307Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1307Chunk0]
  have hn : (transition1307Raw0 : Multiset ℕ) = 2 • (supportNumbers1049 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1049] using hm

private def transition1308Input0 : List ℕ := [0, 2, 136, 138, 265, 267, 385, 387]
private def transition1308Raw0 : List ℕ := [0, 2, 9, 11]
private theorem transition1308Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1308Input0) = fromList transition1308Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1308 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0178 = 1 • support0175 := by
  have hs : support0178 = fromList transition1308Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1308Chunk0]
  have hn : (transition1308Raw0 : Multiset ℕ) = 1 • (supportNumbers0175 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0175] using hm

private def transition1309Input0 : List ℕ := [0, 2, 136, 138, 265, 267, 385, 387]
private def transition1309Raw0 : List ℕ := [0, 2, 520, 522, 9, 11, 513, 515]
private theorem transition1309Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1309Input0) = fromList transition1309Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1309 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0178 = 1 • support0263 := by
  have hs : support0178 = fromList transition1309Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1309Chunk0]
  have hn : (transition1309Raw0 : Multiset ℕ) = 1 • (supportNumbers0263 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0263] using hm

private def transition1310Input0 : List ℕ := [0, 2, 136, 138, 265, 267, 385, 387]
private def transition1310Raw0 : List ℕ := [0, 2, 9, 11]
private theorem transition1310Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1310Input0) = fromList transition1310Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1310 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0178 = 1 • support0175 := by
  have hs : support0178 = fromList transition1310Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1310Chunk0]
  have hn : (transition1310Raw0 : Multiset ℕ) = 1 • (supportNumbers0175 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0175] using hm

private def transition1311Input0 : List ℕ := [0, 2, 136, 138, 265, 267, 385, 387]
private def transition1311Raw0 : List ℕ := [0, 2, 680, 682, 9, 11, 673, 675]
private theorem transition1311Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1311Input0) = fromList transition1311Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1311 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0178 = 1 • support1290 := by
  have hs : support0178 = fromList transition1311Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1311Chunk0]
  have hn : (transition1311Raw0 : Multiset ℕ) = 1 • (supportNumbers1290 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1290] using hm

private def transition1312Input0 : List ℕ := [0, 2, 9, 11, 673, 675, 680, 682]
private def transition1312Raw0 : List ℕ := [0, 2, 9, 11, 417, 419, 424, 426]
private theorem transition1312Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1312Input0) = fromList transition1312Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1312 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1290 = 1 • support1291 := by
  have hs : support1290 = fromList transition1312Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1312Chunk0]
  have hn : (transition1312Raw0 : Multiset ℕ) = 1 • (supportNumbers1291 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1291] using hm

private def transition1313Input0 : List ℕ := [0, 2, 9, 11, 673, 675, 680, 682]
private def transition1313Raw0 : List ℕ := [0, 576, 2, 578, 9, 585, 11, 587, 417, 993, 419, 995, 424, 1000, 426, 1002]
private theorem transition1313Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1313Input0) = fromList transition1313Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1313 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1290 = 1 • support1292 := by
  have hs : support1290 = fromList transition1313Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1313Chunk0]
  have hn : (transition1313Raw0 : Multiset ℕ) = 1 • (supportNumbers1292 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1292] using hm

private def transition1314Input0 : List ℕ := [0, 2, 136, 138, 265, 267, 385, 387, 520, 522, 640, 642, 769, 771, 905, 907]
private def transition1314Raw0 : List ℕ := [0, 2, 136, 138, 9, 11, 129, 131, 264, 266, 384, 386, 257, 259, 393, 395]
private theorem transition1314Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1314Input0) = fromList transition1314Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1314 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0179 = 1 • support0185 := by
  have hs : support0179 = fromList transition1314Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1314Chunk0]
  have hn : (transition1314Raw0 : Multiset ℕ) = 1 • (supportNumbers0185 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0185] using hm

private def transition1315Input0 : List ℕ := [0, 2, 136, 138, 265, 267, 385, 387, 520, 522, 640, 642, 769, 771, 905, 907]
private def transition1315Raw0 : List ℕ := [0, 640, 2, 642, 136, 520, 138, 522, 9, 649, 11, 651, 129, 513, 131, 515, 264, 904, 266, 906, 384, 768, 386, 770, 257, 897, 259, 899, 393, 777, 395, 779]
private theorem transition1315Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1315Input0) = fromList transition1315Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1315 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0179 = 1 • support0186 := by
  have hs : support0179 = fromList transition1315Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1315Chunk0]
  have hn : (transition1315Raw0 : Multiset ℕ) = 1 • (supportNumbers0186 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0186] using hm

private def transition1316Input0 : List ℕ := [0, 2, 136, 138, 265, 267, 385, 387, 520, 522, 640, 642, 769, 771, 905, 907]
private def transition1316Raw0 : List ℕ := [0, 2, 136, 138, 9, 11, 129, 131, 264, 266, 384, 386, 257, 259, 393, 395]
private theorem transition1316Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1316Input0) = fromList transition1316Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1316 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0179 = 1 • support0185 := by
  have hs : support0179 = fromList transition1316Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1316Chunk0]
  have hn : (transition1316Raw0 : Multiset ℕ) = 1 • (supportNumbers0185 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0185] using hm

private def transition1317Input0 : List ℕ := [0, 2, 136, 138, 265, 267, 385, 387, 520, 522, 640, 642, 769, 771, 905, 907]
private def transition1317Raw0 : List ℕ := [0, 544, 2, 546, 136, 680, 138, 682, 9, 553, 11, 555, 129, 673, 131, 675, 264, 808, 266, 810, 384, 928, 386, 930, 257, 801, 259, 803, 393, 937, 395, 939]
private theorem transition1317Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1317Input0) = fromList transition1317Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1317 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0179 = 1 • support1071 := by
  have hs : support0179 = fromList transition1317Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1317Chunk0]
  have hn : (transition1317Raw0 : Multiset ℕ) = 1 • (supportNumbers1071 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1071] using hm

private def transition1318Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private def transition1318Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition1318Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1318Input0) = fromList transition1318Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1318 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0180 = 1 • support0030 := by
  have hs : support0180 = fromList transition1318Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1318Chunk0]
  have hn : (transition1318Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition1319Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private def transition1319Raw0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651]
private theorem transition1319Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1319Input0) = fromList transition1319Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1319 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0180 = 1 • support0264 := by
  have hs : support0180 = fromList transition1319Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1319Chunk0]
  have hn : (transition1319Raw0 : Multiset ℕ) = 1 • (supportNumbers0264 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0264] using hm

private def transition1320Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private def transition1320Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition1320Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1320Input0) = fromList transition1320Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1320 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0180 = 1 • support0030 := by
  have hs : support0180 = fromList transition1320Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1320Chunk0]
  have hn : (transition1320Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition1321Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private def transition1321Raw0 : List ℕ := [0, 1, 2, 3, 552, 553, 554, 555]
private theorem transition1321Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1321Input0) = fromList transition1321Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1321 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0180 = 1 • support1294 := by
  have hs : support0180 = fromList transition1321Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1321Chunk0]
  have hn : (transition1321Raw0 : Multiset ℕ) = 1 • (supportNumbers1294 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1294] using hm

private def transition1322Input0 : List ℕ := [0, 1, 2, 3, 552, 553, 554, 555]
private def transition1322Raw0 : List ℕ := [0, 1, 2, 3, 296, 297, 298, 299]
private theorem transition1322Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1322Input0) = fromList transition1322Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1322 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1294 = 1 • support1295 := by
  have hs : support1294 = fromList transition1322Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1322Chunk0]
  have hn : (transition1322Raw0 : Multiset ℕ) = 1 • (supportNumbers1295 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1295] using hm

private def transition1323Input0 : List ℕ := [0, 1, 2, 3, 552, 553, 554, 555]
private def transition1323Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 296, 872, 297, 873, 298, 874, 299, 875]
private theorem transition1323Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1323Input0) = fromList transition1323Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1323 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1294 = 1 • support1296 := by
  have hs : support1294 = fromList transition1323Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1323Chunk0]
  have hn : (transition1323Raw0 : Multiset ℕ) = 1 • (supportNumbers1296 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1296] using hm

private def transition1324Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 512, 513, 514, 515, 520, 521, 522, 523]
private def transition1324Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 256, 257, 258, 259, 264, 265, 266, 267]
private theorem transition1324Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1324Input0) = fromList transition1324Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1324 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0181 = 1 • support0265 := by
  have hs : support0181 = fromList transition1324Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1324Chunk0]
  have hn : (transition1324Raw0 : Multiset ℕ) = 1 • (supportNumbers0265 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0265] using hm

private def transition1325Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 512, 513, 514, 515, 520, 521, 522, 523]
private def transition1325Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 256, 896, 257, 897, 258, 898, 259, 899, 264, 904, 265, 905, 266, 906, 267, 907]
private theorem transition1325Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1325Input0) = fromList transition1325Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1325 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0181 = 1 • support0266 := by
  have hs : support0181 = fromList transition1325Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1325Chunk0]
  have hn : (transition1325Raw0 : Multiset ℕ) = 1 • (supportNumbers0266 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0266] using hm

private def transition1326Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 512, 513, 514, 515, 520, 521, 522, 523]
private def transition1326Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 256, 257, 258, 259, 264, 265, 266, 267]
private theorem transition1326Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1326Input0) = fromList transition1326Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1326 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0181 = 1 • support0265 := by
  have hs : support0181 = fromList transition1326Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1326Chunk0]
  have hn : (transition1326Raw0 : Multiset ℕ) = 1 • (supportNumbers0265 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0265] using hm

private def transition1327Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 256, 257, 258, 259, 264, 265, 266, 267]
private def transition1327Raw0 : List ℕ := [0, 1, 8, 9, 2, 3, 10, 11]
private theorem transition1327Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1327Input0) = fromList transition1327Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1327 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0265 = 1 • support0180 := by
  have hs : support0265 = fromList transition1327Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1327Chunk0]
  have hn : (transition1327Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def transition1328Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 256, 257, 258, 259, 264, 265, 266, 267]
private def transition1328Raw0 : List ℕ := [0, 1, 578, 579, 8, 9, 586, 587, 576, 577, 2, 3, 584, 585, 10, 11]
private theorem transition1328Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1328Input0) = fromList transition1328Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1328 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0265 = 1 • support1298 := by
  have hs : support0265 = fromList transition1328Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1328Chunk0]
  have hn : (transition1328Raw0 : Multiset ℕ) = 1 • (supportNumbers1298 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1298] using hm

private def transition1329Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 512, 513, 514, 515, 520, 521, 522, 523]
private def transition1329Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 256, 800, 257, 801, 258, 802, 259, 803, 264, 808, 265, 809, 266, 810, 267, 811]
private theorem transition1329Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1329Input0) = fromList transition1329Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1329 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0181 = 1 • support1300 := by
  have hs : support0181 = fromList transition1329Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1329Chunk0]
  have hn : (transition1329Raw0 : Multiset ℕ) = 1 • (supportNumbers1300 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1300] using hm

private def transition1330Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 256, 257, 258, 259, 264, 265, 266, 267, 544, 545, 546, 547, 552, 553, 554, 555, 800, 801, 802, 803, 808, 809, 810, 811]
private def transition1330Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 0, 1, 2, 3, 8, 9, 10, 11, 288, 289, 290, 291, 296, 297, 298, 299, 288, 289, 290, 291, 296, 297, 298, 299]
private theorem transition1330Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1330Input0) = fromList transition1330Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1330 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1300 = 2 • support1099 := by
  have hs : support1300 = fromList transition1330Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1330Chunk0]
  have hn : (transition1330Raw0 : Multiset ℕ) = 2 • (supportNumbers1099 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1099] using hm

private def transition1331Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 256, 257, 258, 259, 264, 265, 266, 267, 544, 545, 546, 547, 552, 553, 554, 555, 800, 801, 802, 803, 808, 809, 810, 811]
private def transition1331Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875]
private theorem transition1331Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1331Input0) = fromList transition1331Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1331 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1300 = 2 • support1100 := by
  have hs : support1300 = fromList transition1331Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1331Chunk0]
  have hn : (transition1331Raw0 : Multiset ℕ) = 2 • (supportNumbers1100 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1100] using hm

private def transition1332Input0 : List ℕ := [0, 2, 129, 131]
private def transition1332Raw0 : List ℕ := [0, 2, 129, 131]
private theorem transition1332Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1332Input0) = fromList transition1332Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1332 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0110 = 1 • support0110 := by
  have hs : support0110 = fromList transition1332Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1332Chunk0]
  have hn : (transition1332Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm

private def transition1333Input0 : List ℕ := [0, 2, 129, 131]
private def transition1333Raw0 : List ℕ := [0, 640, 2, 642, 129, 513, 131, 515]
private theorem transition1333Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1333Input0) = fromList transition1333Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1333 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0110 = 1 • support0267 := by
  have hs : support0110 = fromList transition1333Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1333Chunk0]
  have hn : (transition1333Raw0 : Multiset ℕ) = 1 • (supportNumbers0267 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0267] using hm

private def transition1334Input0 : List ℕ := [0, 2, 129, 131]
private def transition1334Raw0 : List ℕ := [0, 2, 129, 131]
private theorem transition1334Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1334Input0) = fromList transition1334Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1334 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0110 = 1 • support0110 := by
  have hs : support0110 = fromList transition1334Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1334Chunk0]
  have hn : (transition1334Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm

private def transition1335Input0 : List ℕ := [0, 2, 129, 131]
private def transition1335Raw0 : List ℕ := [0, 544, 2, 546, 129, 673, 131, 675]
private theorem transition1335Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1335Input0) = fromList transition1335Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1335 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0110 = 1 • support1301 := by
  have hs : support0110 = fromList transition1335Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1335Chunk0]
  have hn : (transition1335Raw0 : Multiset ℕ) = 1 • (supportNumbers1301 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1301] using hm

private def transition1336Input0 : List ℕ := [0, 2, 129, 131, 544, 546, 673, 675]
private def transition1336Raw0 : List ℕ := [0, 2, 129, 131, 288, 290, 417, 419]
private theorem transition1336Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1336Input0) = fromList transition1336Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1336 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1301 = 1 • support1302 := by
  have hs : support1301 = fromList transition1336Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1336Chunk0]
  have hn : (transition1336Raw0 : Multiset ℕ) = 1 • (supportNumbers1302 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1302] using hm

private def transition1337Input0 : List ℕ := [0, 2, 129, 131, 544, 546, 673, 675]
private def transition1337Raw0 : List ℕ := [0, 576, 2, 578, 129, 705, 131, 707, 288, 864, 290, 866, 417, 993, 419, 995]
private theorem transition1337Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1337Input0) = fromList transition1337Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1337 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1301 = 1 • support1303 := by
  have hs : support1301 = fromList transition1337Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1337Chunk0]
  have hn : (transition1337Raw0 : Multiset ℕ) = 1 • (supportNumbers1303 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1303] using hm

private def transition1338Input0 : List ℕ := [0, 2, 129, 131, 264, 266, 393, 395]
private def transition1338Raw0 : List ℕ := [0, 2, 129, 131, 8, 10, 137, 139]
private theorem transition1338Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1338Input0) = fromList transition1338Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1338 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0182 = 1 • support0268 := by
  have hs : support0182 = fromList transition1338Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1338Chunk0]
  have hn : (transition1338Raw0 : Multiset ℕ) = 1 • (supportNumbers0268 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0268] using hm

private def transition1339Input0 : List ℕ := [0, 2, 129, 131, 264, 266, 393, 395]
private def transition1339Raw0 : List ℕ := [0, 2, 129, 131, 8, 10, 137, 139]
private theorem transition1339Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1339Input0) = fromList transition1339Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1339 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0182 = 1 • support0268 := by
  have hs : support0182 = fromList transition1339Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1339Chunk0]
  have hn : (transition1339Raw0 : Multiset ℕ) = 1 • (supportNumbers0268 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0268] using hm

private def transition1340Input0 : List ℕ := [0, 2, 129, 131, 264, 266, 393, 395]
private def transition1340Raw0 : List ℕ := [0, 2, 129, 131, 8, 10, 137, 139]
private theorem transition1340Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1340Input0) = fromList transition1340Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1340 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0182 = 1 • support0268 := by
  have hs : support0182 = fromList transition1340Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1340Chunk0]
  have hn : (transition1340Raw0 : Multiset ℕ) = 1 • (supportNumbers0268 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0268] using hm

private def transition1341Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private def transition1341Raw0 : List ℕ := [0, 8, 129, 137]
private theorem transition1341Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1341Input0) = fromList transition1341Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1341 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0268 = 1 • support1305 := by
  have hs : support0268 = fromList transition1341Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1341Chunk0]
  have hn : (transition1341Raw0 : Multiset ℕ) = 1 • (supportNumbers1305 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1305] using hm

private def transition1342Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private def transition1342Raw0 : List ℕ := [0, 578, 8, 586, 129, 707, 137, 715]
private theorem transition1342Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1342Input0) = fromList transition1342Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1342 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0268 = 1 • support1306 := by
  have hs : support0268 = fromList transition1342Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1342Chunk0]
  have hn : (transition1342Raw0 : Multiset ℕ) = 1 • (supportNumbers1306 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1306] using hm

private def transition1343Input0 : List ℕ := [0, 2, 129, 131, 264, 266, 393, 395]
private def transition1343Raw0 : List ℕ := [0, 2, 129, 131, 8, 10, 137, 139]
private theorem transition1343Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1343Input0) = fromList transition1343Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1343 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0182 = 1 • support0268 := by
  have hs : support0182 = fromList transition1343Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1343Chunk0]
  have hn : (transition1343Raw0 : Multiset ℕ) = 1 • (supportNumbers0268 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0268] using hm

private def transition1344Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private def transition1344Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private theorem transition1344Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1344Input0) = fromList transition1344Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1344 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0268 = 1 • support0268 := by
  have hs : support0268 = fromList transition1344Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1344Chunk0]
  have hn : (transition1344Raw0 : Multiset ℕ) = 1 • (supportNumbers0268 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0268] using hm

private def transition1345Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private def transition1345Raw0 : List ℕ := [0, 576, 2, 578, 8, 584, 10, 586, 129, 705, 131, 707, 137, 713, 139, 715]
private theorem transition1345Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1345Input0) = fromList transition1345Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1345 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0268 = 1 • support1308 := by
  have hs : support0268 = fromList transition1345Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1345Chunk0]
  have hn : (transition1345Raw0 : Multiset ℕ) = 1 • (supportNumbers1308 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1308] using hm

private def transition1346Input0 : List ℕ := [0, 2, 129, 131, 264, 266, 393, 395, 513, 515, 640, 642, 777, 779, 904, 906]
private def transition1346Raw0 : List ℕ := [0, 2, 129, 131, 8, 10, 137, 139, 257, 259, 384, 386, 265, 267, 392, 394]
private theorem transition1346Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1346Input0) = fromList transition1346Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1346 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0183 = 1 • support0028 := by
  have hs : support0183 = fromList transition1346Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1346Chunk0]
  have hn : (transition1346Raw0 : Multiset ℕ) = 1 • (supportNumbers0028 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0028] using hm

private def transition1347Input0 : List ℕ := [0, 2, 129, 131, 264, 266, 393, 395, 513, 515, 640, 642, 777, 779, 904, 906]
private def transition1347Raw0 : List ℕ := [0, 640, 2, 642, 129, 513, 131, 515, 8, 648, 10, 650, 137, 521, 139, 523, 257, 897, 259, 899, 384, 768, 386, 770, 265, 905, 267, 907, 392, 776, 394, 778]
private theorem transition1347Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1347Input0) = fromList transition1347Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1347 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0183 = 1 • support0029 := by
  have hs : support0183 = fromList transition1347Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1347Chunk0]
  have hn : (transition1347Raw0 : Multiset ℕ) = 1 • (supportNumbers0029 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0029] using hm

private def transition1348Input0 : List ℕ := [0, 2, 129, 131, 264, 266, 393, 395, 513, 515, 640, 642, 777, 779, 904, 906]
private def transition1348Raw0 : List ℕ := [0, 2, 129, 131, 8, 10, 137, 139, 257, 259, 384, 386, 265, 267, 392, 394]
private theorem transition1348Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1348Input0) = fromList transition1348Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1348 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0183 = 1 • support0028 := by
  have hs : support0183 = fromList transition1348Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1348Chunk0]
  have hn : (transition1348Raw0 : Multiset ℕ) = 1 • (supportNumbers0028 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0028] using hm

private def transition1349Input0 : List ℕ := [0, 2, 129, 131, 264, 266, 393, 395, 513, 515, 640, 642, 777, 779, 904, 906]
private def transition1349Raw0 : List ℕ := [0, 544, 2, 546, 129, 673, 131, 675, 8, 552, 10, 554, 137, 681, 139, 683, 257, 801, 259, 803, 384, 928, 386, 930, 265, 809, 267, 811, 392, 936, 394, 938]
private theorem transition1349Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1349Input0) = fromList transition1349Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1349 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0183 = 1 • support0563 := by
  have hs : support0183 = fromList transition1349Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1349Chunk0]
  have hn : (transition1349Raw0 : Multiset ℕ) = 1 • (supportNumbers0563 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0563] using hm

private def transition1350Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 513, 515, 520, 522, 640, 642, 649, 651]
private def transition1350Raw0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 257, 259, 264, 266, 384, 386, 393, 395]
private theorem transition1350Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1350Input0) = fromList transition1350Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1350 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0184 = 1 • support0185 := by
  have hs : support0184 = fromList transition1350Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1350Chunk0]
  have hn : (transition1350Raw0 : Multiset ℕ) = 1 • (supportNumbers0185 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0185] using hm

private def transition1351Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 513, 515, 520, 522, 640, 642, 649, 651]
private def transition1351Raw0 : List ℕ := [0, 640, 2, 642, 9, 649, 11, 651, 129, 513, 131, 515, 136, 520, 138, 522, 257, 897, 259, 899, 264, 904, 266, 906, 384, 768, 386, 770, 393, 777, 395, 779]
private theorem transition1351Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1351Input0) = fromList transition1351Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1351 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0184 = 1 • support0186 := by
  have hs : support0184 = fromList transition1351Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1351Chunk0]
  have hn : (transition1351Raw0 : Multiset ℕ) = 1 • (supportNumbers0186 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0186] using hm

private def transition1352Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 513, 515, 520, 522, 640, 642, 649, 651]
private def transition1352Raw0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 257, 259, 264, 266, 384, 386, 393, 395]
private theorem transition1352Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1352Input0) = fromList transition1352Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1352 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0184 = 1 • support0185 := by
  have hs : support0184 = fromList transition1352Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1352Chunk0]
  have hn : (transition1352Raw0 : Multiset ℕ) = 1 • (supportNumbers0185 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0185] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
