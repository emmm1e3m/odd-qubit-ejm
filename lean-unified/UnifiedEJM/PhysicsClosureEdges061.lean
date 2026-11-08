import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1084Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 264, 266, 268, 270, 329, 331, 333, 335, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition1084Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 129, 707, 133, 711, 192, 642, 196, 646, 584, 10, 588, 14, 521, 75, 525, 79, 713, 139, 717, 143, 648, 202, 652, 206]
private theorem transition1084Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1084Input0) = fromList transition1084Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1084 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0224 = 1 • support1188 := by
  have hs : support0224 = fromList transition1084Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1084Chunk0]
  have hn : (transition1084Raw0 : Multiset ℕ) = 1 • (supportNumbers1188 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1188] using hm

private def transition1085Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 520, 522, 524, 526, 585, 587, 589, 591, 649, 651, 653, 655, 712, 714, 716, 718]
private def transition1085Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 129, 673, 131, 675, 133, 677, 135, 679, 192, 736, 194, 738, 196, 740, 198, 742, 264, 808, 266, 810, 268, 812, 270, 814, 329, 873, 331, 875, 333, 877, 335, 879, 393, 937, 395, 939, 397, 941, 399, 943, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition1085Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1085Input0) = fromList transition1085Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1085 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0145 = 1 • support1189 := by
  have hs : support0145 = fromList transition1085Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1085Chunk0]
  have hn : (transition1085Raw0 : Multiset ℕ) = 1 • (supportNumbers1189 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1189] using hm

private def transition1086Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 264, 266, 268, 270, 329, 331, 333, 335, 393, 395, 397, 399, 456, 458, 460, 462, 544, 546, 548, 550, 609, 611, 613, 615, 673, 675, 677, 679, 736, 738, 740, 742, 808, 810, 812, 814, 873, 875, 877, 879, 937, 939, 941, 943, 1000, 1002, 1004, 1006]
private def transition1086Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 8, 10, 12, 14, 73, 75, 77, 79, 137, 139, 141, 143, 200, 202, 204, 206, 288, 290, 292, 294, 353, 355, 357, 359, 417, 419, 421, 423, 480, 482, 484, 486, 296, 298, 300, 302, 361, 363, 365, 367, 425, 427, 429, 431, 488, 490, 492, 494]
private theorem transition1086Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1086Input0) = fromList transition1086Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1086 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1189 = 1 • support0524 := by
  have hs : support1189 = fromList transition1086Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1086Chunk0]
  have hn : (transition1086Raw0 : Multiset ℕ) = 1 • (supportNumbers0524 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0524] using hm

private def transition1087Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 264, 266, 268, 270, 329, 331, 333, 335, 393, 395, 397, 399, 456, 458, 460, 462, 544, 546, 548, 550, 609, 611, 613, 615, 673, 675, 677, 679, 736, 738, 740, 742, 808, 810, 812, 814, 873, 875, 877, 879, 937, 939, 941, 943, 1000, 1002, 1004, 1006]
private def transition1087Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 129, 705, 131, 707, 133, 709, 135, 711, 192, 640, 194, 642, 196, 644, 198, 646, 8, 584, 10, 586, 12, 588, 14, 590, 73, 521, 75, 523, 77, 525, 79, 527, 137, 713, 139, 715, 141, 717, 143, 719, 200, 648, 202, 650, 204, 652, 206, 654, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 417, 993, 419, 995, 421, 997, 423, 999, 480, 928, 482, 930, 484, 932, 486, 934, 296, 872, 298, 874, 300, 876, 302, 878, 361, 809, 363, 811, 365, 813, 367, 815, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition1087Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1087Input0) = fromList transition1087Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1087 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1189 = 1 • support0526 := by
  have hs : support1189 = fromList transition1087Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1087Chunk0]
  have hn : (transition1087Raw0 : Multiset ℕ) = 1 • (supportNumbers0526 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0526] using hm

private def transition1088Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private def transition1088Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 9, 11, 13, 15, 72, 74, 76, 78, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition1088Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1088Input0) = fromList transition1088Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1088 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0146 = 1 • support0082 := by
  have hs : support0146 = fromList transition1088Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1088Chunk0]
  have hn : (transition1088Raw0 : Multiset ℕ) = 1 • (supportNumbers0082 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0082] using hm

private def transition1089Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private def transition1089Raw0 : List ℕ := [0, 2, 4, 6, 649, 651, 653, 655, 65, 67, 69, 71, 712, 714, 716, 718, 129, 131, 133, 135, 520, 522, 524, 526, 192, 194, 196, 198, 585, 587, 589, 591, 640, 642, 644, 646, 9, 11, 13, 15, 705, 707, 709, 711, 72, 74, 76, 78, 513, 515, 517, 519, 136, 138, 140, 142, 576, 578, 580, 582, 201, 203, 205, 207]
private theorem transition1089Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1089Input0) = fromList transition1089Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1089 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0146 = 1 • support0226 := by
  have hs : support0146 = fromList transition1089Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1089Chunk0]
  have hn : (transition1089Raw0 : Multiset ℕ) = 1 • (supportNumbers0226 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0226] using hm

private def transition1090Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private def transition1090Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 9, 11, 13, 15, 72, 74, 76, 78, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition1090Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1090Input0) = fromList transition1090Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1090 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0146 = 1 • support0082 := by
  have hs : support0146 = fromList transition1090Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1090Chunk0]
  have hn : (transition1090Raw0 : Multiset ℕ) = 1 • (supportNumbers0082 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0082] using hm

private def transition1091Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private def transition1091Raw0 : List ℕ := [0, 2, 4, 6, 553, 555, 557, 559, 65, 67, 69, 71, 616, 618, 620, 622, 129, 131, 133, 135, 680, 682, 684, 686, 192, 194, 196, 198, 745, 747, 749, 751, 544, 546, 548, 550, 9, 11, 13, 15, 609, 611, 613, 615, 72, 74, 76, 78, 673, 675, 677, 679, 136, 138, 140, 142, 736, 738, 740, 742, 201, 203, 205, 207]
private theorem transition1091Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1091Input0) = fromList transition1091Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1091 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0146 = 1 • support1190 := by
  have hs : support0146 = fromList transition1091Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1091Chunk0]
  have hn : (transition1091Raw0 : Multiset ℕ) = 1 • (supportNumbers1190 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1190] using hm

private def transition1092Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622, 673, 675, 677, 679, 680, 682, 684, 686, 736, 738, 740, 742, 745, 747, 749, 751]
private def transition1092Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366, 417, 419, 421, 423, 424, 426, 428, 430, 480, 482, 484, 486, 489, 491, 493, 495]
private theorem transition1092Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1092Input0) = fromList transition1092Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1092 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1190 = 1 • support0957 := by
  have hs : support1190 = fromList transition1092Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1092Chunk0]
  have hn : (transition1092Raw0 : Multiset ℕ) = 1 • (supportNumbers0957 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0957] using hm

private def transition1093Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622, 673, 675, 677, 679, 680, 682, 684, 686, 736, 738, 740, 742, 745, 747, 749, 751]
private def transition1093Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 129, 705, 131, 707, 133, 709, 135, 711, 136, 712, 138, 714, 140, 716, 142, 718, 192, 640, 194, 642, 196, 644, 198, 646, 201, 649, 203, 651, 205, 653, 207, 655, 288, 864, 290, 866, 292, 868, 294, 870, 297, 873, 299, 875, 301, 877, 303, 879, 353, 801, 355, 803, 357, 805, 359, 807, 360, 808, 362, 810, 364, 812, 366, 814, 417, 993, 419, 995, 421, 997, 423, 999, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 480, 928, 482, 930, 484, 932, 486, 934, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition1093Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1093Input0) = fromList transition1093Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1093 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1190 = 1 • support0959 := by
  have hs : support1190 = fromList transition1093Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1093Chunk0]
  have hn : (transition1093Raw0 : Multiset ℕ) = 1 • (supportNumbers0959 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0959] using hm

private def transition1094Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private def transition1094Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private theorem transition1094Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1094Input0) = fromList transition1094Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1094Input1 : List ℕ := [513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 769, 771, 773, 775, 776, 778, 780, 782, 832, 834, 836, 838, 841, 843, 845, 847, 896, 898, 900, 902, 905, 907, 909, 911, 961, 963, 965, 967, 968, 970, 972, 974]
private def transition1094Raw1 : List ℕ := [257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private theorem transition1094Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1094Input1) = fromList transition1094Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1094 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0147 = 2 • support0227 := by
  have hs : support0147 = fromList transition1094Input0 + fromList transition1094Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1094Chunk0, transition1094Chunk1]
  have hn : (transition1094Raw0 : Multiset ℕ) + (transition1094Raw1 : Multiset ℕ) = 2 • (supportNumbers0227 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0227] using hm

private def transition1095Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private def transition1095Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718, 129, 513, 131, 515, 133, 517, 135, 519, 136, 520, 138, 522, 140, 524, 142, 526, 192, 576, 194, 578, 196, 580, 198, 582, 201, 585, 203, 587, 205, 589, 207, 591, 0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718, 129, 513, 131, 515, 133, 517, 135, 519, 136, 520, 138, 522, 140, 524, 142, 526, 192, 576, 194, 578, 196, 580, 198, 582, 201, 585, 203, 587, 205, 589, 207, 591]
private theorem transition1095Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1095Input0) = fromList transition1095Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1095Input1 : List ℕ := [513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 769, 771, 773, 775, 776, 778, 780, 782, 832, 834, 836, 838, 841, 843, 845, 847, 896, 898, 900, 902, 905, 907, 909, 911, 961, 963, 965, 967, 968, 970, 972, 974]
private def transition1095Raw1 : List ℕ := [257, 897, 259, 899, 261, 901, 263, 903, 264, 904, 266, 906, 268, 908, 270, 910, 320, 960, 322, 962, 324, 964, 326, 966, 329, 969, 331, 971, 333, 973, 335, 975, 384, 768, 386, 770, 388, 772, 390, 774, 393, 777, 395, 779, 397, 781, 399, 783, 449, 833, 451, 835, 453, 837, 455, 839, 456, 840, 458, 842, 460, 844, 462, 846, 257, 897, 259, 899, 261, 901, 263, 903, 264, 904, 266, 906, 268, 908, 270, 910, 320, 960, 322, 962, 324, 964, 326, 966, 329, 969, 331, 971, 333, 973, 335, 975, 384, 768, 386, 770, 388, 772, 390, 774, 393, 777, 395, 779, 397, 781, 399, 783, 449, 833, 451, 835, 453, 837, 455, 839, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition1095Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1095Input1) = fromList transition1095Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1095 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0147 = 2 • support0228 := by
  have hs : support0147 = fromList transition1095Input0 + fromList transition1095Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1095Chunk0, transition1095Chunk1]
  have hn : (transition1095Raw0 : Multiset ℕ) + (transition1095Raw1 : Multiset ℕ) = 2 • (supportNumbers0228 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0228] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
