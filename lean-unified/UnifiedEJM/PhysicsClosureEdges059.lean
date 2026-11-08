import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1049Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1049Raw0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 130, 134, 139, 143, 195, 199, 202, 206]
private theorem transition1049Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1049Input0) = fromList transition1049Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1049 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0218 = 1 • support1167 := by
  have hs : support0218 = fromList transition1049Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1049Chunk0]
  have hn : (transition1049Raw0 : Multiset ℕ) = 1 • (supportNumbers1167 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1167] using hm

private def transition1050Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1050Raw0 : List ℕ := [0, 578, 4, 582, 9, 587, 13, 591, 65, 515, 69, 519, 72, 522, 76, 526, 704, 130, 708, 134, 713, 139, 717, 143, 641, 195, 645, 199, 648, 202, 652, 206]
private theorem transition1050Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1050Input0) = fromList transition1050Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1050 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0218 = 1 • support1169 := by
  have hs : support0218 = fromList transition1050Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1050Chunk0]
  have hn : (transition1050Raw0 : Multiset ℕ) = 1 • (supportNumbers1169 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1169] using hm

private def transition1051Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 265, 267, 269, 271, 328, 330, 332, 334, 640, 642, 644, 646, 705, 707, 709, 711, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition1051Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 9, 553, 11, 555, 13, 557, 15, 559, 72, 616, 74, 618, 76, 620, 78, 622, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 393, 937, 395, 939, 397, 941, 399, 943, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition1051Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1051Input0) = fromList transition1051Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1051 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0140 = 1 • support1170 := by
  have hs : support0140 = fromList transition1051Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1051Chunk0]
  have hn : (transition1051Raw0 : Multiset ℕ) = 1 • (supportNumbers1170 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1170] using hm

private def transition1052Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622, 928, 930, 932, 934, 937, 939, 941, 943, 993, 995, 997, 999, 1000, 1002, 1004, 1006]
private def transition1052Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366, 416, 418, 420, 422, 425, 427, 429, 431, 481, 483, 485, 487, 488, 490, 492, 494]
private theorem transition1052Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1052Input0) = fromList transition1052Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1052 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1170 = 1 • support1171 := by
  have hs : support1170 = fromList transition1052Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1052Chunk0]
  have hn : (transition1052Raw0 : Multiset ℕ) = 1 • (supportNumbers1171 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1171] using hm

private def transition1053Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622, 928, 930, 932, 934, 937, 939, 941, 943, 993, 995, 997, 999, 1000, 1002, 1004, 1006]
private def transition1053Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 128, 704, 130, 706, 132, 708, 134, 710, 137, 713, 139, 715, 141, 717, 143, 719, 193, 641, 195, 643, 197, 645, 199, 647, 200, 648, 202, 650, 204, 652, 206, 654, 288, 864, 290, 866, 292, 868, 294, 870, 297, 873, 299, 875, 301, 877, 303, 879, 353, 801, 355, 803, 357, 805, 359, 807, 360, 808, 362, 810, 364, 812, 366, 814, 416, 992, 418, 994, 420, 996, 422, 998, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 481, 929, 483, 931, 485, 933, 487, 935, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition1053Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1053Input0) = fromList transition1053Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1053 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1170 = 1 • support1173 := by
  have hs : support1170 = fromList transition1053Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1053Chunk0]
  have hn : (transition1053Raw0 : Multiset ℕ) = 1 • (supportNumbers1173 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1173] using hm

private def transition1054Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 521, 523, 525, 527, 584, 586, 588, 590, 641, 643, 645, 647, 704, 706, 708, 710]
private def transition1054Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 265, 267, 269, 271, 328, 330, 332, 334, 385, 387, 389, 391, 448, 450, 452, 454]
private theorem transition1054Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1054Input0) = fromList transition1054Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1054 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0141 = 1 • support0220 := by
  have hs : support0141 = fromList transition1054Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1054Chunk0]
  have hn : (transition1054Raw0 : Multiset ℕ) = 1 • (supportNumbers0220 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0220] using hm

private def transition1055Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 521, 523, 525, 527, 584, 586, 588, 590, 641, 643, 645, 647, 704, 706, 708, 710]
private def transition1055Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 136, 520, 138, 522, 140, 524, 142, 526, 201, 585, 203, 587, 205, 589, 207, 591, 265, 905, 267, 907, 269, 909, 271, 911, 328, 968, 330, 970, 332, 972, 334, 974, 385, 769, 387, 771, 389, 773, 391, 775, 448, 832, 450, 834, 452, 836, 454, 838]
private theorem transition1055Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1055Input0) = fromList transition1055Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1055 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0141 = 1 • support0221 := by
  have hs : support0141 = fromList transition1055Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1055Chunk0]
  have hn : (transition1055Raw0 : Multiset ℕ) = 1 • (supportNumbers0221 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0221] using hm

private def transition1056Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 521, 523, 525, 527, 584, 586, 588, 590, 641, 643, 645, 647, 704, 706, 708, 710]
private def transition1056Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 265, 267, 269, 271, 328, 330, 332, 334, 385, 387, 389, 391, 448, 450, 452, 454]
private theorem transition1056Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1056Input0) = fromList transition1056Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1056 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0141 = 1 • support0220 := by
  have hs : support0141 = fromList transition1056Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1056Chunk0]
  have hn : (transition1056Raw0 : Multiset ℕ) = 1 • (supportNumbers0220 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0220] using hm

private def transition1057Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 265, 267, 269, 271, 328, 330, 332, 334, 385, 387, 389, 391, 448, 450, 452, 454]
private def transition1057Raw0 : List ℕ := [0, 4, 65, 69, 136, 140, 201, 205, 11, 15, 74, 78, 131, 135, 194, 198]
private theorem transition1057Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1057Input0) = fromList transition1057Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1057 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0220 = 1 • support1174 := by
  have hs : support0220 = fromList transition1057Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1057Chunk0]
  have hn : (transition1057Raw0 : Multiset ℕ) = 1 • (supportNumbers1174 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1174] using hm

private def transition1058Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 265, 267, 269, 271, 328, 330, 332, 334, 385, 387, 389, 391, 448, 450, 452, 454]
private def transition1058Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 136, 714, 140, 718, 201, 651, 205, 655, 585, 11, 589, 15, 520, 74, 524, 78, 705, 131, 709, 135, 640, 194, 644, 198]
private theorem transition1058Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1058Input0) = fromList transition1058Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1058 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0220 = 1 • support1176 := by
  have hs : support0220 = fromList transition1058Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1058Chunk0]
  have hn : (transition1058Raw0 : Multiset ℕ) = 1 • (supportNumbers1176 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1176] using hm

private def transition1059Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 521, 523, 525, 527, 584, 586, 588, 590, 641, 643, 645, 647, 704, 706, 708, 710]
private def transition1059Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 136, 680, 138, 682, 140, 684, 142, 686, 201, 745, 203, 747, 205, 749, 207, 751, 265, 809, 267, 811, 269, 813, 271, 815, 328, 872, 330, 874, 332, 876, 334, 878, 385, 929, 387, 931, 389, 933, 391, 935, 448, 992, 450, 994, 452, 996, 454, 998]
private theorem transition1059Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1059Input0) = fromList transition1059Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1059 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0141 = 1 • support1177 := by
  have hs : support0141 = fromList transition1059Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1059Chunk0]
  have hn : (transition1059Raw0 : Multiset ℕ) = 1 • (supportNumbers1177 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1177] using hm

private def transition1060Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 265, 267, 269, 271, 328, 330, 332, 334, 385, 387, 389, 391, 448, 450, 452, 454, 544, 546, 548, 550, 609, 611, 613, 615, 680, 682, 684, 686, 745, 747, 749, 751, 809, 811, 813, 815, 872, 874, 876, 878, 929, 931, 933, 935, 992, 994, 996, 998]
private def transition1060Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 9, 11, 13, 15, 72, 74, 76, 78, 129, 131, 133, 135, 192, 194, 196, 198, 288, 290, 292, 294, 353, 355, 357, 359, 424, 426, 428, 430, 489, 491, 493, 495, 297, 299, 301, 303, 360, 362, 364, 366, 417, 419, 421, 423, 480, 482, 484, 486]
private theorem transition1060Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1060Input0) = fromList transition1060Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1060 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1177 = 1 • support0957 := by
  have hs : support1177 = fromList transition1060Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1060Chunk0]
  have hn : (transition1060Raw0 : Multiset ℕ) = 1 • (supportNumbers0957 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0957] using hm

private def transition1061Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 265, 267, 269, 271, 328, 330, 332, 334, 385, 387, 389, 391, 448, 450, 452, 454, 544, 546, 548, 550, 609, 611, 613, 615, 680, 682, 684, 686, 745, 747, 749, 751, 809, 811, 813, 815, 872, 874, 876, 878, 929, 931, 933, 935, 992, 994, 996, 998]
private def transition1061Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 136, 712, 138, 714, 140, 716, 142, 718, 201, 649, 203, 651, 205, 653, 207, 655, 9, 585, 11, 587, 13, 589, 15, 591, 72, 520, 74, 522, 76, 524, 78, 526, 129, 705, 131, 707, 133, 709, 135, 711, 192, 640, 194, 642, 196, 644, 198, 646, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 489, 937, 491, 939, 493, 941, 495, 943, 297, 873, 299, 875, 301, 877, 303, 879, 360, 808, 362, 810, 364, 812, 366, 814, 417, 993, 419, 995, 421, 997, 423, 999, 480, 928, 482, 930, 484, 932, 486, 934]
private theorem transition1061Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1061Input0) = fromList transition1061Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1061 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1177 = 1 • support0959 := by
  have hs : support1177 = fromList transition1061Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1061Chunk0]
  have hn : (transition1061Raw0 : Multiset ℕ) = 1 • (supportNumbers0959 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0959] using hm

private def transition1062Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1062Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79]
private theorem transition1062Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1062Input0) = fromList transition1062Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1062 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0142 = 1 • support0222 := by
  have hs : support0142 = fromList transition1062Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1062Chunk0]
  have hn : (transition1062Raw0 : Multiset ℕ) = 1 • (supportNumbers0222 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0222] using hm

private def transition1063Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1063Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 520, 521, 522, 523, 524, 525, 526, 527, 584, 585, 586, 587, 588, 589, 590, 591, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583]
private theorem transition1063Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1063Input0) = fromList transition1063Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1063 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0142 = 1 • support0223 := by
  have hs : support0142 = fromList transition1063Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1063Chunk0]
  have hn : (transition1063Raw0 : Multiset ℕ) = 1 • (supportNumbers0223 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0223] using hm

private def transition1064Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1064Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79]
private theorem transition1064Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1064Input0) = fromList transition1064Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1064 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0142 = 1 • support0222 := by
  have hs : support0142 = fromList transition1064Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1064Chunk0]
  have hn : (transition1064Raw0 : Multiset ℕ) = 1 • (supportNumbers0222 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0222] using hm

private def transition1065Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
private def transition1065Raw0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77]
private theorem transition1065Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1065Input0) = fromList transition1065Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1065 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0222 = 1 • support1178 := by
  have hs : support0222 = fromList transition1065Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1065Chunk0]
  have hn : (transition1065Raw0 : Multiset ℕ) = 1 • (supportNumbers1178 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1178] using hm

private def transition1066Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
private def transition1066Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 8, 9, 586, 587, 12, 13, 590, 591, 64, 65, 514, 515, 68, 69, 518, 519, 72, 73, 522, 523, 76, 77, 526, 527]
private theorem transition1066Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1066Input0) = fromList transition1066Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1066 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0222 = 1 • support1180 := by
  have hs : support0222 = fromList transition1066Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1066Chunk0]
  have hn : (transition1066Raw0 : Multiset ℕ) = 1 • (supportNumbers1180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1180] using hm

private def transition1067Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1067Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 680, 681, 682, 683, 684, 685, 686, 687, 744, 745, 746, 747, 748, 749, 750, 751, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79, 672, 673, 674, 675, 676, 677, 678, 679, 736, 737, 738, 739, 740, 741, 742, 743]
private theorem transition1067Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1067Input0) = fromList transition1067Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1067 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0142 = 1 • support1181 := by
  have hs : support0142 = fromList transition1067Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1067Chunk0]
  have hn : (transition1067Raw0 : Multiset ℕ) = 1 • (supportNumbers1181 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1181] using hm

private def transition1068Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751]
private def transition1068Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]
private theorem transition1068Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1068Input0) = fromList transition1068Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1068 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1181 = 1 • support1182 := by
  have hs : support1181 = fromList transition1068Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1068Chunk0]
  have hn : (transition1068Raw0 : Multiset ℕ) = 1 • (supportNumbers1182 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1182] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
