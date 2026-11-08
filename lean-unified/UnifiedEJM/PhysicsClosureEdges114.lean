import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2053Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition2053Raw0 : List ℕ := [0, 1, 2, 3, 552, 553, 554, 555, 148, 149, 150, 151, 700, 701, 702, 703, 564, 565, 566, 567, 28, 29, 30, 31, 672, 673, 674, 675, 136, 137, 138, 139]
private theorem transition2053Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2053Input0) = fromList transition2053Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2053 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0288 = 1 • support1545 := by
  have hs : support0288 = fromList transition2053Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2053Chunk0]
  have hn : (transition2053Raw0 : Multiset ℕ) = 1 • (supportNumbers1545 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1545] using hm

private def transition2054Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 552, 553, 554, 555, 564, 565, 566, 567, 672, 673, 674, 675, 700, 701, 702, 703]
private def transition2054Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 296, 297, 298, 299, 308, 309, 310, 311, 416, 417, 418, 419, 444, 445, 446, 447]
private theorem transition2054Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2054Input0) = fromList transition2054Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2054 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1545 = 1 • support1546 := by
  have hs : support1545 = fromList transition2054Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2054Chunk0]
  have hn : (transition2054Raw0 : Multiset ℕ) = 1 • (supportNumbers1546 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1546] using hm

private def transition2055Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 552, 553, 554, 555, 564, 565, 566, 567, 672, 673, 674, 675, 700, 701, 702, 703]
private def transition2055Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 136, 712, 137, 713, 138, 714, 139, 715, 148, 724, 149, 725, 150, 726, 151, 727, 296, 872, 297, 873, 298, 874, 299, 875, 308, 884, 309, 885, 310, 886, 311, 887, 416, 992, 417, 993, 418, 994, 419, 995, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition2055Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2055Input0) = fromList transition2055Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2055 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1545 = 1 • support1547 := by
  have hs : support1545 = fromList transition2055Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2055Chunk0]
  have hn : (transition2055Raw0 : Multiset ℕ) = 1 • (supportNumbers1547 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1547] using hm

private def transition2056Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651, 768, 769, 770, 771, 776, 777, 778, 779, 916, 917, 918, 919, 924, 925, 926, 927]
private def transition2056Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 256, 257, 258, 259, 264, 265, 266, 267, 404, 405, 406, 407, 412, 413, 414, 415]
private theorem transition2056Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2056Input0) = fromList transition2056Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2056 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0289 = 1 • support0036 := by
  have hs : support0289 = fromList transition2056Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2056Chunk0]
  have hn : (transition2056Raw0 : Multiset ℕ) = 1 • (supportNumbers0036 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0036] using hm

private def transition2057Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651, 768, 769, 770, 771, 776, 777, 778, 779, 916, 917, 918, 919, 924, 925, 926, 927]
private def transition2057Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 148, 532, 149, 533, 150, 534, 151, 535, 156, 540, 157, 541, 158, 542, 159, 543, 20, 660, 21, 661, 22, 662, 23, 663, 28, 668, 29, 669, 30, 670, 31, 671, 128, 512, 129, 513, 130, 514, 131, 515, 136, 520, 137, 521, 138, 522, 139, 523, 276, 916, 277, 917, 278, 918, 279, 919, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779, 256, 896, 257, 897, 258, 898, 259, 899, 264, 904, 265, 905, 266, 906, 267, 907, 404, 788, 405, 789, 406, 790, 407, 791, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition2057Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2057Input0) = fromList transition2057Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2057 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0289 = 1 • support0037 := by
  have hs : support0289 = fromList transition2057Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2057Chunk0]
  have hn : (transition2057Raw0 : Multiset ℕ) = 1 • (supportNumbers0037 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0037] using hm

private def transition2058Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651, 768, 769, 770, 771, 776, 777, 778, 779, 916, 917, 918, 919, 924, 925, 926, 927]
private def transition2058Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 256, 257, 258, 259, 264, 265, 266, 267, 404, 405, 406, 407, 412, 413, 414, 415]
private theorem transition2058Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2058Input0) = fromList transition2058Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2058 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0289 = 1 • support0036 := by
  have hs : support0289 = fromList transition2058Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2058Chunk0]
  have hn : (transition2058Raw0 : Multiset ℕ) = 1 • (supportNumbers0036 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0036] using hm

private def transition2059Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651, 768, 769, 770, 771, 776, 777, 778, 779, 916, 917, 918, 919, 924, 925, 926, 927]
private def transition2059Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 148, 692, 149, 693, 150, 694, 151, 695, 156, 700, 157, 701, 158, 702, 159, 703, 20, 564, 21, 565, 22, 566, 23, 567, 28, 572, 29, 573, 30, 574, 31, 575, 128, 672, 129, 673, 130, 674, 131, 675, 136, 680, 137, 681, 138, 682, 139, 683, 276, 820, 277, 821, 278, 822, 279, 823, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939, 256, 800, 257, 801, 258, 802, 259, 803, 264, 808, 265, 809, 266, 810, 267, 811, 404, 948, 405, 949, 406, 950, 407, 951, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition2059Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2059Input0) = fromList transition2059Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2059 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0289 = 1 • support0593 := by
  have hs : support0289 = fromList transition2059Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2059Chunk0]
  have hn : (transition2059Raw0 : Multiset ℕ) = 1 • (supportNumbers0593 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0593] using hm

private def transition2060Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition2060Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private theorem transition2060Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2060Input0) = fromList transition2060Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2060 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0290 = 1 • support0069 := by
  have hs : support0290 = fromList transition2060Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2060Chunk0]
  have hn : (transition2060Raw0 : Multiset ℕ) = 1 • (supportNumbers0069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0069] using hm

private def transition2061Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition2061Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 512, 513, 514, 515, 532, 533, 534, 535]
private theorem transition2061Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2061Input0) = fromList transition2061Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2061 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0290 = 1 • support0376 := by
  have hs : support0290 = fromList transition2061Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2061Chunk0]
  have hn : (transition2061Raw0 : Multiset ℕ) = 1 • (supportNumbers0376 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0376] using hm

private def transition2062Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition2062Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private theorem transition2062Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2062Input0) = fromList transition2062Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2062 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0290 = 1 • support0069 := by
  have hs : support0290 = fromList transition2062Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2062Chunk0]
  have hn : (transition2062Raw0 : Multiset ℕ) = 1 • (supportNumbers0069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0069] using hm

private def transition2063Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition2063Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 672, 673, 674, 675, 692, 693, 694, 695]
private theorem transition2063Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2063Input0) = fromList transition2063Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2063 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0290 = 1 • support1549 := by
  have hs : support0290 = fromList transition2063Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2063Chunk0]
  have hn : (transition2063Raw0 : Multiset ℕ) = 1 • (supportNumbers1549 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1549] using hm

private def transition2064Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 672, 673, 674, 675, 692, 693, 694, 695]
private def transition2064Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 416, 417, 418, 419, 436, 437, 438, 439]
private theorem transition2064Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2064Input0) = fromList transition2064Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2064 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1549 = 1 • support1550 := by
  have hs : support1549 = fromList transition2064Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2064Chunk0]
  have hn : (transition2064Raw0 : Multiset ℕ) = 1 • (supportNumbers1550 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1550] using hm

private def transition2065Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 672, 673, 674, 675, 692, 693, 694, 695]
private def transition2065Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 416, 992, 417, 993, 418, 994, 419, 995, 436, 1012, 437, 1013, 438, 1014, 439, 1015]
private theorem transition2065Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2065Input0) = fromList transition2065Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2065 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1549 = 1 • support1551 := by
  have hs : support1549 = fromList transition2065Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2065Chunk0]
  have hn : (transition2065Raw0 : Multiset ℕ) = 1 • (supportNumbers1551 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1551] using hm

private def transition2066Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 384, 385, 386, 387, 404, 405, 406, 407, 640, 641, 642, 643, 660, 661, 662, 663, 768, 769, 770, 771, 788, 789, 790, 791]
private def transition2066Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 384, 385, 386, 387, 404, 405, 406, 407, 256, 257, 258, 259, 276, 277, 278, 279]
private theorem transition2066Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2066Input0) = fromList transition2066Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2066 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0291 = 1 • support0377 := by
  have hs : support0291 = fromList transition2066Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2066Chunk0]
  have hn : (transition2066Raw0 : Multiset ℕ) = 1 • (supportNumbers0377 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0377] using hm

private def transition2067Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 384, 385, 386, 387, 404, 405, 406, 407, 640, 641, 642, 643, 660, 661, 662, 663, 768, 769, 770, 771, 788, 789, 790, 791]
private def transition2067Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 128, 512, 129, 513, 130, 514, 131, 515, 148, 532, 149, 533, 150, 534, 151, 535, 384, 768, 385, 769, 386, 770, 387, 771, 404, 788, 405, 789, 406, 790, 407, 791, 256, 896, 257, 897, 258, 898, 259, 899, 276, 916, 277, 917, 278, 918, 279, 919]
private theorem transition2067Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2067Input0) = fromList transition2067Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2067 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0291 = 1 • support0378 := by
  have hs : support0291 = fromList transition2067Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2067Chunk0]
  have hn : (transition2067Raw0 : Multiset ℕ) = 1 • (supportNumbers0378 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0378] using hm

private def transition2068Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 384, 385, 386, 387, 404, 405, 406, 407, 640, 641, 642, 643, 660, 661, 662, 663, 768, 769, 770, 771, 788, 789, 790, 791]
private def transition2068Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 384, 385, 386, 387, 404, 405, 406, 407, 256, 257, 258, 259, 276, 277, 278, 279]
private theorem transition2068Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2068Input0) = fromList transition2068Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2068 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0291 = 1 • support0377 := by
  have hs : support0291 = fromList transition2068Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2068Chunk0]
  have hn : (transition2068Raw0 : Multiset ℕ) = 1 • (supportNumbers0377 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0377] using hm

private def transition2069Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition2069Raw0 : List ℕ := [0, 1, 20, 21, 128, 129, 148, 149, 2, 3, 22, 23, 130, 131, 150, 151]
private theorem transition2069Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2069Input0) = fromList transition2069Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2069 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0377 = 1 • support0130 := by
  have hs : support0377 = fromList transition2069Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2069Chunk0]
  have hn : (transition2069Raw0 : Multiset ℕ) = 1 • (supportNumbers0130 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0130] using hm

private def transition2070Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition2070Raw0 : List ℕ := [0, 1, 578, 579, 20, 21, 598, 599, 128, 129, 706, 707, 148, 149, 726, 727, 576, 577, 2, 3, 596, 597, 22, 23, 704, 705, 130, 131, 724, 725, 150, 151]
private theorem transition2070Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2070Input0) = fromList transition2070Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2070 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0377 = 1 • support1133 := by
  have hs : support0377 = fromList transition2070Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2070Chunk0]
  have hn : (transition2070Raw0 : Multiset ℕ) = 1 • (supportNumbers1133 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1133] using hm

private def transition2071Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 384, 385, 386, 387, 404, 405, 406, 407, 640, 641, 642, 643, 660, 661, 662, 663, 768, 769, 770, 771, 788, 789, 790, 791]
private def transition2071Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 128, 672, 129, 673, 130, 674, 131, 675, 148, 692, 149, 693, 150, 694, 151, 695, 384, 928, 385, 929, 386, 930, 387, 931, 404, 948, 405, 949, 406, 950, 407, 951, 256, 800, 257, 801, 258, 802, 259, 803, 276, 820, 277, 821, 278, 822, 279, 823]
private theorem transition2071Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2071Input0) = fromList transition2071Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2071 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0291 = 1 • support1553 := by
  have hs : support0291 = fromList transition2071Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2071Chunk0]
  have hn : (transition2071Raw0 : Multiset ℕ) = 1 • (supportNumbers1553 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1553] using hm

private def transition2072Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407, 544, 545, 546, 547, 564, 565, 566, 567, 672, 673, 674, 675, 692, 693, 694, 695, 800, 801, 802, 803, 820, 821, 822, 823, 928, 929, 930, 931, 948, 949, 950, 951]
private def transition2072Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 288, 289, 290, 291, 308, 309, 310, 311, 416, 417, 418, 419, 436, 437, 438, 439, 288, 289, 290, 291, 308, 309, 310, 311, 416, 417, 418, 419, 436, 437, 438, 439]
private theorem transition2072Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2072Input0) = fromList transition2072Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2072 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1553 = 2 • support1360 := by
  have hs : support1553 = fromList transition2072Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2072Chunk0]
  have hn : (transition2072Raw0 : Multiset ℕ) = 2 • (supportNumbers1360 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1360] using hm

private def transition2073Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407, 544, 545, 546, 547, 564, 565, 566, 567, 672, 673, 674, 675, 692, 693, 694, 695, 800, 801, 802, 803, 820, 821, 822, 823, 928, 929, 930, 931, 948, 949, 950, 951]
private def transition2073Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 128, 704, 129, 705, 130, 706, 131, 707, 148, 724, 149, 725, 150, 726, 151, 727, 0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 128, 704, 129, 705, 130, 706, 131, 707, 148, 724, 149, 725, 150, 726, 151, 727, 288, 864, 289, 865, 290, 866, 291, 867, 308, 884, 309, 885, 310, 886, 311, 887, 416, 992, 417, 993, 418, 994, 419, 995, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 288, 864, 289, 865, 290, 866, 291, 867, 308, 884, 309, 885, 310, 886, 311, 887, 416, 992, 417, 993, 418, 994, 419, 995, 436, 1012, 437, 1013, 438, 1014, 439, 1015]
private theorem transition2073Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2073Input0) = fromList transition2073Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2073 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1553 = 2 • support1362 := by
  have hs : support1553 = fromList transition2073Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2073Chunk0]
  have hn : (transition2073Raw0 : Multiset ℕ) = 2 • (supportNumbers1362 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1362] using hm

private def transition2074Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 648, 649, 650, 651, 668, 669, 670, 671]
private def transition2074Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 392, 393, 394, 395, 412, 413, 414, 415]
private theorem transition2074Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2074Input0) = fromList transition2074Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2074 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0292 = 1 • support0379 := by
  have hs : support0292 = fromList transition2074Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2074Chunk0]
  have hn : (transition2074Raw0 : Multiset ℕ) = 1 • (supportNumbers0379 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0379] using hm

private def transition2075Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 648, 649, 650, 651, 668, 669, 670, 671]
private def transition2075Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 392, 776, 393, 777, 394, 778, 395, 779, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition2075Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2075Input0) = fromList transition2075Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2075 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0292 = 1 • support0380 := by
  have hs : support0292 = fromList transition2075Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2075Chunk0]
  have hn : (transition2075Raw0 : Multiset ℕ) = 1 • (supportNumbers0380 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0380] using hm

private def transition2076Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 648, 649, 650, 651, 668, 669, 670, 671]
private def transition2076Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 392, 393, 394, 395, 412, 413, 414, 415]
private theorem transition2076Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2076Input0) = fromList transition2076Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2076 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0292 = 1 • support0379 := by
  have hs : support0292 = fromList transition2076Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2076Chunk0]
  have hn : (transition2076Raw0 : Multiset ℕ) = 1 • (supportNumbers0379 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0379] using hm

private def transition2077Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition2077Raw0 : List ℕ := [0, 1, 20, 21, 138, 139, 158, 159]
private theorem transition2077Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2077Input0) = fromList transition2077Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2077 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0379 = 1 • support1554 := by
  have hs : support0379 = fromList transition2077Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2077Chunk0]
  have hn : (transition2077Raw0 : Multiset ℕ) = 1 • (supportNumbers1554 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1554] using hm

private def transition2078Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition2078Raw0 : List ℕ := [0, 1, 578, 579, 20, 21, 598, 599, 712, 713, 138, 139, 732, 733, 158, 159]
private theorem transition2078Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2078Input0) = fromList transition2078Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2078 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0379 = 1 • support1555 := by
  have hs : support0379 = fromList transition2078Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2078Chunk0]
  have hn : (transition2078Raw0 : Multiset ℕ) = 1 • (supportNumbers1555 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1555] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
