import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1408Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 256, 257, 258, 259, 284, 285, 286, 287]
private def transition1408Raw0 : List ℕ := [0, 1, 578, 579, 28, 29, 606, 607, 576, 577, 2, 3, 604, 605, 30, 31]
private theorem transition1408Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1408Input0) = fromList transition1408Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1408 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0277 = 1 • support1331 := by
  have hs : support0277 = fromList transition1408Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1408Chunk0]
  have hn : (transition1408Raw0 : Multiset ℕ) = 1 • (supportNumbers1331 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1331] using hm

private def transition1409Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 512, 513, 514, 515, 540, 541, 542, 543]
private def transition1409Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 256, 800, 257, 801, 258, 802, 259, 803, 284, 828, 285, 829, 286, 830, 287, 831]
private theorem transition1409Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1409Input0) = fromList transition1409Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1409 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0193 = 1 • support1333 := by
  have hs : support0193 = fromList transition1409Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1409Chunk0]
  have hn : (transition1409Raw0 : Multiset ℕ) = 1 • (supportNumbers1333 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1333] using hm

private def transition1410Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 256, 257, 258, 259, 284, 285, 286, 287, 544, 545, 546, 547, 572, 573, 574, 575, 800, 801, 802, 803, 828, 829, 830, 831]
private def transition1410Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 0, 1, 2, 3, 28, 29, 30, 31, 288, 289, 290, 291, 316, 317, 318, 319, 288, 289, 290, 291, 316, 317, 318, 319]
private theorem transition1410Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1410Input0) = fromList transition1410Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1410 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1333 = 2 • support1328 := by
  have hs : support1333 = fromList transition1410Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1410Chunk0]
  have hn : (transition1410Raw0 : Multiset ℕ) = 2 • (supportNumbers1328 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1328] using hm

private def transition1411Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 256, 257, 258, 259, 284, 285, 286, 287, 544, 545, 546, 547, 572, 573, 574, 575, 800, 801, 802, 803, 828, 829, 830, 831]
private def transition1411Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 288, 864, 289, 865, 290, 866, 291, 867, 316, 892, 317, 893, 318, 894, 319, 895, 288, 864, 289, 865, 290, 866, 291, 867, 316, 892, 317, 893, 318, 894, 319, 895]
private theorem transition1411Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1411Input0) = fromList transition1411Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1411 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1333 = 2 • support1329 := by
  have hs : support1333 = fromList transition1411Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1411Chunk0]
  have hn : (transition1411Raw0 : Multiset ℕ) = 2 • (supportNumbers1329 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1329] using hm

private def transition1412Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition1412Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 28, 29, 30, 31, 156, 157, 158, 159]
private theorem transition1412Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1412Input0) = fromList transition1412Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1412 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0194 = 1 • support0279 := by
  have hs : support0194 = fromList transition1412Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1412Chunk0]
  have hn : (transition1412Raw0 : Multiset ℕ) = 1 • (supportNumbers0279 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0279] using hm

private def transition1413Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition1413Raw0 : List ℕ := [0, 1, 2, 3, 668, 669, 670, 671, 128, 129, 130, 131, 540, 541, 542, 543, 640, 641, 642, 643, 28, 29, 30, 31, 512, 513, 514, 515, 156, 157, 158, 159]
private theorem transition1413Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1413Input0) = fromList transition1413Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1413 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0194 = 1 • support0280 := by
  have hs : support0194 = fromList transition1413Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1413Chunk0]
  have hn : (transition1413Raw0 : Multiset ℕ) = 1 • (supportNumbers0280 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0280] using hm

private def transition1414Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition1414Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 28, 29, 30, 31, 156, 157, 158, 159]
private theorem transition1414Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1414Input0) = fromList transition1414Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1414 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0194 = 1 • support0279 := by
  have hs : support0194 = fromList transition1414Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1414Chunk0]
  have hn : (transition1414Raw0 : Multiset ℕ) = 1 • (supportNumbers0279 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0279] using hm

private def transition1415Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159]
private def transition1415Raw0 : List ℕ := [0, 1, 28, 29, 128, 129, 156, 157]
private theorem transition1415Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1415Input0) = fromList transition1415Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1415 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0279 = 1 • support1334 := by
  have hs : support0279 = fromList transition1415Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1415Chunk0]
  have hn : (transition1415Raw0 : Multiset ℕ) = 1 • (supportNumbers1334 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1334] using hm

private def transition1416Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159]
private def transition1416Raw0 : List ℕ := [0, 1, 578, 579, 28, 29, 606, 607, 128, 129, 706, 707, 156, 157, 734, 735]
private theorem transition1416Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1416Input0) = fromList transition1416Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1416 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0279 = 1 • support1335 := by
  have hs : support0279 = fromList transition1416Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1416Chunk0]
  have hn : (transition1416Raw0 : Multiset ℕ) = 1 • (supportNumbers1335 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1335] using hm

private def transition1417Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition1417Raw0 : List ℕ := [0, 1, 2, 3, 572, 573, 574, 575, 128, 129, 130, 131, 700, 701, 702, 703, 544, 545, 546, 547, 28, 29, 30, 31, 672, 673, 674, 675, 156, 157, 158, 159]
private theorem transition1417Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1417Input0) = fromList transition1417Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1417 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0194 = 1 • support1337 := by
  have hs : support0194 = fromList transition1417Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1417Chunk0]
  have hn : (transition1417Raw0 : Multiset ℕ) = 1 • (supportNumbers1337 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1337] using hm

private def transition1418Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 544, 545, 546, 547, 572, 573, 574, 575, 672, 673, 674, 675, 700, 701, 702, 703]
private def transition1418Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 288, 289, 290, 291, 316, 317, 318, 319, 416, 417, 418, 419, 444, 445, 446, 447]
private theorem transition1418Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1418Input0) = fromList transition1418Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1418 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1337 = 1 • support0861 := by
  have hs : support1337 = fromList transition1418Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1418Chunk0]
  have hn : (transition1418Raw0 : Multiset ℕ) = 1 • (supportNumbers0861 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0861] using hm

private def transition1419Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 544, 545, 546, 547, 572, 573, 574, 575, 672, 673, 674, 675, 700, 701, 702, 703]
private def transition1419Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 128, 704, 129, 705, 130, 706, 131, 707, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 316, 892, 317, 893, 318, 894, 319, 895, 416, 992, 417, 993, 418, 994, 419, 995, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition1419Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1419Input0) = fromList transition1419Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1419 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1337 = 1 • support0863 := by
  have hs : support1337 = fromList transition1419Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1419Chunk0]
  have hn : (transition1419Raw0 : Multiset ℕ) = 1 • (supportNumbers0863 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0863] using hm

private def transition1420Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415, 512, 513, 514, 515, 540, 541, 542, 543, 640, 641, 642, 643, 668, 669, 670, 671, 768, 769, 770, 771, 796, 797, 798, 799, 896, 897, 898, 899, 924, 925, 926, 927]
private def transition1420Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415]
private theorem transition1420Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1420Input0) = fromList transition1420Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1420 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0195 = 2 • support0194 := by
  have hs : support0195 = fromList transition1420Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1420Chunk0]
  have hn : (transition1420Raw0 : Multiset ℕ) = 2 • (supportNumbers0194 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0194] using hm

private def transition1421Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415, 512, 513, 514, 515, 540, 541, 542, 543, 640, 641, 642, 643, 668, 669, 670, 671, 768, 769, 770, 771, 796, 797, 798, 799, 896, 897, 898, 899, 924, 925, 926, 927]
private def transition1421Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 128, 512, 129, 513, 130, 514, 131, 515, 156, 540, 157, 541, 158, 542, 159, 543, 0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 128, 512, 129, 513, 130, 514, 131, 515, 156, 540, 157, 541, 158, 542, 159, 543, 256, 896, 257, 897, 258, 898, 259, 899, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 412, 796, 413, 797, 414, 798, 415, 799, 256, 896, 257, 897, 258, 898, 259, 899, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition1421Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1421Input0) = fromList transition1421Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1421 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0195 = 2 • support0195 := by
  have hs : support0195 = fromList transition1421Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1421Chunk0]
  have hn : (transition1421Raw0 : Multiset ℕ) = 2 • (supportNumbers0195 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0195] using hm

private def transition1422Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415, 512, 513, 514, 515, 540, 541, 542, 543, 640, 641, 642, 643, 668, 669, 670, 671, 768, 769, 770, 771, 796, 797, 798, 799, 896, 897, 898, 899, 924, 925, 926, 927]
private def transition1422Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415]
private theorem transition1422Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1422Input0) = fromList transition1422Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1422 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0195 = 2 • support0194 := by
  have hs : support0195 = fromList transition1422Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1422Chunk0]
  have hn : (transition1422Raw0 : Multiset ℕ) = 2 • (supportNumbers0194 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0194] using hm

private def transition1423Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415, 512, 513, 514, 515, 540, 541, 542, 543, 640, 641, 642, 643, 668, 669, 670, 671, 768, 769, 770, 771, 796, 797, 798, 799, 896, 897, 898, 899, 924, 925, 926, 927]
private def transition1423Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 128, 672, 129, 673, 130, 674, 131, 675, 156, 700, 157, 701, 158, 702, 159, 703, 0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 128, 672, 129, 673, 130, 674, 131, 675, 156, 700, 157, 701, 158, 702, 159, 703, 256, 800, 257, 801, 258, 802, 259, 803, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 412, 956, 413, 957, 414, 958, 415, 959, 256, 800, 257, 801, 258, 802, 259, 803, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition1423Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1423Input0) = fromList transition1423Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1423 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0195 = 2 • support1095 := by
  have hs : support0195 = fromList transition1423Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1423Chunk0]
  have hn : (transition1423Raw0 : Multiset ℕ) = 2 • (supportNumbers1095 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1095] using hm

private def transition1424Input0 : List ℕ := [0, 1, 2, 3, 264, 265, 266, 267]
private def transition1424Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem transition1424Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1424Input0) = fromList transition1424Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1424 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0196 = 1 • support0180 := by
  have hs : support0196 = fromList transition1424Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1424Chunk0]
  have hn : (transition1424Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def transition1425Input0 : List ℕ := [0, 1, 2, 3, 264, 265, 266, 267]
private def transition1425Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem transition1425Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1425Input0) = fromList transition1425Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1425 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0196 = 1 • support0180 := by
  have hs : support0196 = fromList transition1425Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1425Chunk0]
  have hn : (transition1425Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def transition1426Input0 : List ℕ := [0, 1, 2, 3, 264, 265, 266, 267]
private def transition1426Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem transition1426Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1426Input0) = fromList transition1426Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1426 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0196 = 1 • support0180 := by
  have hs : support0196 = fromList transition1426Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1426Chunk0]
  have hn : (transition1426Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def transition1427Input0 : List ℕ := [0, 1, 2, 3, 264, 265, 266, 267]
private def transition1427Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem transition1427Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1427Input0) = fromList transition1427Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1427 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0196 = 1 • support0180 := by
  have hs : support0196 = fromList transition1427Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1427Chunk0]
  have hn : (transition1427Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def transition1428Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private def transition1428Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem transition1428Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1428Input0) = fromList transition1428Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1428 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0180 = 1 • support0180 := by
  have hs : support0180 = fromList transition1428Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1428Chunk0]
  have hn : (transition1428Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def transition1429Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private def transition1429Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587]
private theorem transition1429Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1429Input0) = fromList transition1429Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1429 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0180 = 1 • support1298 := by
  have hs : support0180 = fromList transition1429Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1429Chunk0]
  have hn : (transition1429Raw0 : Multiset ℕ) = 1 • (supportNumbers1298 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1298] using hm

private def transition1430Input0 : List ℕ := [0, 1, 2, 3, 264, 265, 266, 267, 640, 641, 642, 643, 904, 905, 906, 907]
private def transition1430Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395]
private theorem transition1430Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1430Input0) = fromList transition1430Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1430 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0197 = 1 • support0281 := by
  have hs : support0197 = fromList transition1430Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1430Chunk0]
  have hn : (transition1430Raw0 : Multiset ℕ) = 1 • (supportNumbers0281 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0281] using hm

private def transition1431Input0 : List ℕ := [0, 1, 2, 3, 264, 265, 266, 267, 640, 641, 642, 643, 904, 905, 906, 907]
private def transition1431Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779]
private theorem transition1431Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1431Input0) = fromList transition1431Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1431 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0197 = 1 • support0282 := by
  have hs : support0197 = fromList transition1431Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1431Chunk0]
  have hn : (transition1431Raw0 : Multiset ℕ) = 1 • (supportNumbers0282 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0282] using hm

private def transition1432Input0 : List ℕ := [0, 1, 2, 3, 264, 265, 266, 267, 640, 641, 642, 643, 904, 905, 906, 907]
private def transition1432Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395]
private theorem transition1432Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1432Input0) = fromList transition1432Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1432 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0197 = 1 • support0281 := by
  have hs : support0197 = fromList transition1432Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1432Chunk0]
  have hn : (transition1432Raw0 : Multiset ℕ) = 1 • (supportNumbers0281 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0281] using hm

private def transition1433Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition1433Raw0 : List ℕ := [0, 1, 8, 9, 130, 131, 138, 139]
private theorem transition1433Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1433Input0) = fromList transition1433Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1433 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0281 = 1 • support0502 := by
  have hs : support0281 = fromList transition1433Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1433Chunk0]
  have hn : (transition1433Raw0 : Multiset ℕ) = 1 • (supportNumbers0502 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0502] using hm

private def transition1434Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition1434Raw0 : List ℕ := [0, 1, 578, 579, 8, 9, 586, 587, 704, 705, 130, 131, 712, 713, 138, 139]
private theorem transition1434Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1434Input0) = fromList transition1434Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1434 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0281 = 1 • support1338 := by
  have hs : support0281 = fromList transition1434Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1434Chunk0]
  have hn : (transition1434Raw0 : Multiset ℕ) = 1 • (supportNumbers1338 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1338] using hm

private def transition1435Input0 : List ℕ := [0, 1, 2, 3, 264, 265, 266, 267, 640, 641, 642, 643, 904, 905, 906, 907]
private def transition1435Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939]
private theorem transition1435Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1435Input0) = fromList transition1435Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1435 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0197 = 1 • support1340 := by
  have hs : support0197 = fromList transition1435Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1435Chunk0]
  have hn : (transition1435Raw0 : Multiset ℕ) = 1 • (supportNumbers1340 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1340] using hm

private def transition1436Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395, 544, 545, 546, 547, 552, 553, 554, 555, 928, 929, 930, 931, 936, 937, 938, 939]
private def transition1436Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 288, 289, 290, 291, 296, 297, 298, 299, 416, 417, 418, 419, 424, 425, 426, 427]
private theorem transition1436Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1436Input0) = fromList transition1436Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1436 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1340 = 1 • support0564 := by
  have hs : support1340 = fromList transition1436Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1436Chunk0]
  have hn : (transition1436Raw0 : Multiset ℕ) = 1 • (supportNumbers0564 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0564] using hm

private def transition1437Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395, 544, 545, 546, 547, 552, 553, 554, 555, 928, 929, 930, 931, 936, 937, 938, 939]
private def transition1437Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 128, 704, 129, 705, 130, 706, 131, 707, 136, 712, 137, 713, 138, 714, 139, 715, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 416, 992, 417, 993, 418, 994, 419, 995, 424, 1000, 425, 1001, 426, 1002, 427, 1003]
private theorem transition1437Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1437Input0) = fromList transition1437Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1437 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1340 = 1 • support0565 := by
  have hs : support1340 = fromList transition1437Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1437Chunk0]
  have hn : (transition1437Raw0 : Multiset ℕ) = 1 • (supportNumbers0565 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0565] using hm

private def transition1438Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 520, 521, 522, 523, 660, 661, 662, 663]
private def transition1438Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 264, 265, 266, 267, 404, 405, 406, 407]
private theorem transition1438Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1438Input0) = fromList transition1438Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1438 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0198 = 1 • support0283 := by
  have hs : support0198 = fromList transition1438Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1438Chunk0]
  have hn : (transition1438Raw0 : Multiset ℕ) = 1 • (supportNumbers0283 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0283] using hm

private def transition1439Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 520, 521, 522, 523, 660, 661, 662, 663]
private def transition1439Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 156, 540, 157, 541, 158, 542, 159, 543, 264, 904, 265, 905, 266, 906, 267, 907, 404, 788, 405, 789, 406, 790, 407, 791]
private theorem transition1439Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1439Input0) = fromList transition1439Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1439 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0198 = 1 • support0284 := by
  have hs : support0198 = fromList transition1439Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1439Chunk0]
  have hn : (transition1439Raw0 : Multiset ℕ) = 1 • (supportNumbers0284 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0284] using hm

private def transition1440Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 520, 521, 522, 523, 660, 661, 662, 663]
private def transition1440Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 264, 265, 266, 267, 404, 405, 406, 407]
private theorem transition1440Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1440Input0) = fromList transition1440Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1440 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0198 = 1 • support0283 := by
  have hs : support0198 = fromList transition1440Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1440Chunk0]
  have hn : (transition1440Raw0 : Multiset ℕ) = 1 • (supportNumbers0283 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0283] using hm

private def transition1441Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 264, 265, 266, 267, 404, 405, 406, 407]
private def transition1441Raw0 : List ℕ := [0, 1, 156, 157, 10, 11, 150, 151]
private theorem transition1441Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1441Input0) = fromList transition1441Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1441 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0283 = 1 • support1341 := by
  have hs : support0283 = fromList transition1441Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1441Chunk0]
  have hn : (transition1441Raw0 : Multiset ℕ) = 1 • (supportNumbers1341 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1341] using hm

private def transition1442Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 264, 265, 266, 267, 404, 405, 406, 407]
private def transition1442Raw0 : List ℕ := [0, 1, 578, 579, 156, 157, 734, 735, 584, 585, 10, 11, 724, 725, 150, 151]
private theorem transition1442Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1442Input0) = fromList transition1442Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1442 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0283 = 1 • support1342 := by
  have hs : support0283 = fromList transition1442Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1442Chunk0]
  have hn : (transition1442Raw0 : Multiset ℕ) = 1 • (supportNumbers1342 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1342] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
