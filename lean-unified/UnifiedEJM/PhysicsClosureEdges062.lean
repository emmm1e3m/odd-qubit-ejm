import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1096Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private def transition1096Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private theorem transition1096Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1096Input0) = fromList transition1096Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1096Input1 : List ℕ := [513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 769, 771, 773, 775, 776, 778, 780, 782, 832, 834, 836, 838, 841, 843, 845, 847, 896, 898, 900, 902, 905, 907, 909, 911, 961, 963, 965, 967, 968, 970, 972, 974]
private def transition1096Raw1 : List ℕ := [257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private theorem transition1096Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1096Input1) = fromList transition1096Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1096 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0147 = 2 • support0227 := by
  have hs : support0147 = fromList transition1096Input0 + fromList transition1096Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1096Chunk0, transition1096Chunk1]
  have hn : (transition1096Raw0 : Multiset ℕ) + (transition1096Raw1 : Multiset ℕ) = 2 • (supportNumbers0227 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0227] using hm

private def transition1097Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1097Raw0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 129, 133, 136, 140, 192, 196, 201, 205, 3, 7, 10, 14, 66, 70, 75, 79, 130, 134, 139, 143, 195, 199, 202, 206]
private theorem transition1097Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1097Input0) = fromList transition1097Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1097 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0227 = 1 • support0735 := by
  have hs : support0227 = fromList transition1097Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1097Chunk0]
  have hn : (transition1097Raw0 : Multiset ℕ) = 1 • (supportNumbers0735 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0735] using hm

private def transition1098Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1098Raw0 : List ℕ := [0, 578, 4, 582, 9, 587, 13, 591, 65, 515, 69, 519, 72, 522, 76, 526, 129, 707, 133, 711, 136, 714, 140, 718, 192, 642, 196, 646, 201, 651, 205, 655, 577, 3, 581, 7, 584, 10, 588, 14, 512, 66, 516, 70, 521, 75, 525, 79, 704, 130, 708, 134, 713, 139, 717, 143, 641, 195, 645, 199, 648, 202, 652, 206]
private theorem transition1098Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1098Input0) = fromList transition1098Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1098 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0227 = 1 • support1191 := by
  have hs : support0227 = fromList transition1098Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1098Chunk0]
  have hn : (transition1098Raw0 : Multiset ℕ) = 1 • (supportNumbers1191 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1191] using hm

private def transition1099Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private def transition1099Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 9, 553, 11, 555, 13, 557, 15, 559, 65, 609, 67, 611, 69, 613, 71, 615, 72, 616, 74, 618, 76, 620, 78, 622, 129, 673, 131, 675, 133, 677, 135, 679, 136, 680, 138, 682, 140, 684, 142, 686, 192, 736, 194, 738, 196, 740, 198, 742, 201, 745, 203, 747, 205, 749, 207, 751, 0, 544, 2, 546, 4, 548, 6, 550, 9, 553, 11, 555, 13, 557, 15, 559, 65, 609, 67, 611, 69, 613, 71, 615, 72, 616, 74, 618, 76, 620, 78, 622, 129, 673, 131, 675, 133, 677, 135, 679, 136, 680, 138, 682, 140, 684, 142, 686, 192, 736, 194, 738, 196, 740, 198, 742, 201, 745, 203, 747, 205, 749, 207, 751]
private theorem transition1099Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1099Input0) = fromList transition1099Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1099Input1 : List ℕ := [513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 769, 771, 773, 775, 776, 778, 780, 782, 832, 834, 836, 838, 841, 843, 845, 847, 896, 898, 900, 902, 905, 907, 909, 911, 961, 963, 965, 967, 968, 970, 972, 974]
private def transition1099Raw1 : List ℕ := [257, 801, 259, 803, 261, 805, 263, 807, 264, 808, 266, 810, 268, 812, 270, 814, 320, 864, 322, 866, 324, 868, 326, 870, 329, 873, 331, 875, 333, 877, 335, 879, 384, 928, 386, 930, 388, 932, 390, 934, 393, 937, 395, 939, 397, 941, 399, 943, 449, 993, 451, 995, 453, 997, 455, 999, 456, 1000, 458, 1002, 460, 1004, 462, 1006, 257, 801, 259, 803, 261, 805, 263, 807, 264, 808, 266, 810, 268, 812, 270, 814, 320, 864, 322, 866, 324, 868, 326, 870, 329, 873, 331, 875, 333, 877, 335, 879, 384, 928, 386, 930, 388, 932, 390, 934, 393, 937, 395, 939, 397, 941, 399, 943, 449, 993, 451, 995, 453, 997, 455, 999, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition1099Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1099Input1) = fromList transition1099Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1099 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0147 = 2 • support1192 := by
  have hs : support0147 = fromList transition1099Input0 + fromList transition1099Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1099Chunk0, transition1099Chunk1]
  have hn : (transition1099Raw0 : Multiset ℕ) + (transition1099Raw1 : Multiset ℕ) = 2 • (supportNumbers1192 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1192] using hm

private def transition1100Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1100Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 1, 3, 5, 7, 8, 10, 12, 14, 64, 66, 68, 70, 73, 75, 77, 79, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private theorem transition1100Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1100Input0) = fromList transition1100Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1100Input1 : List ℕ := [544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622, 673, 675, 677, 679, 680, 682, 684, 686, 736, 738, 740, 742, 745, 747, 749, 751, 801, 803, 805, 807, 808, 810, 812, 814, 864, 866, 868, 870, 873, 875, 877, 879, 928, 930, 932, 934, 937, 939, 941, 943, 993, 995, 997, 999, 1000, 1002, 1004, 1006]
private def transition1100Raw1 : List ℕ := [288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366, 417, 419, 421, 423, 424, 426, 428, 430, 480, 482, 484, 486, 489, 491, 493, 495, 289, 291, 293, 295, 296, 298, 300, 302, 352, 354, 356, 358, 361, 363, 365, 367, 416, 418, 420, 422, 425, 427, 429, 431, 481, 483, 485, 487, 488, 490, 492, 494]
private theorem transition1100Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1100Input1) = fromList transition1100Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1100 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1192 = 1 • support0616 := by
  have hs : support1192 = fromList transition1100Input0 + fromList transition1100Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1100Chunk0, transition1100Chunk1]
  have hn : (transition1100Raw0 : Multiset ℕ) + (transition1100Raw1 : Multiset ℕ) = 1 • (supportNumbers0616 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0616] using hm

private def transition1101Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1101Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 129, 705, 131, 707, 133, 709, 135, 711, 136, 712, 138, 714, 140, 716, 142, 718, 192, 640, 194, 642, 196, 644, 198, 646, 201, 649, 203, 651, 205, 653, 207, 655, 1, 577, 3, 579, 5, 581, 7, 583, 8, 584, 10, 586, 12, 588, 14, 590, 64, 512, 66, 514, 68, 516, 70, 518, 73, 521, 75, 523, 77, 525, 79, 527, 128, 704, 130, 706, 132, 708, 134, 710, 137, 713, 139, 715, 141, 717, 143, 719, 193, 641, 195, 643, 197, 645, 199, 647, 200, 648, 202, 650, 204, 652, 206, 654]
private theorem transition1101Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1101Input0) = fromList transition1101Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1101Input1 : List ℕ := [544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622, 673, 675, 677, 679, 680, 682, 684, 686, 736, 738, 740, 742, 745, 747, 749, 751, 801, 803, 805, 807, 808, 810, 812, 814, 864, 866, 868, 870, 873, 875, 877, 879, 928, 930, 932, 934, 937, 939, 941, 943, 993, 995, 997, 999, 1000, 1002, 1004, 1006]
private def transition1101Raw1 : List ℕ := [288, 864, 290, 866, 292, 868, 294, 870, 297, 873, 299, 875, 301, 877, 303, 879, 353, 801, 355, 803, 357, 805, 359, 807, 360, 808, 362, 810, 364, 812, 366, 814, 417, 993, 419, 995, 421, 997, 423, 999, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 480, 928, 482, 930, 484, 932, 486, 934, 489, 937, 491, 939, 493, 941, 495, 943, 289, 865, 291, 867, 293, 869, 295, 871, 296, 872, 298, 874, 300, 876, 302, 878, 352, 800, 354, 802, 356, 804, 358, 806, 361, 809, 363, 811, 365, 813, 367, 815, 416, 992, 418, 994, 420, 996, 422, 998, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 481, 929, 483, 931, 485, 933, 487, 935, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition1101Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1101Input1) = fromList transition1101Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1101 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1192 = 1 • support0618 := by
  have hs : support1192 = fromList transition1101Input0 + fromList transition1101Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1101Chunk0, transition1101Chunk1]
  have hn : (transition1101Raw0 : Multiset ℕ) + (transition1101Raw1 : Multiset ℕ) = 1 • (supportNumbers0618 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0618] using hm

private def transition1102Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition1102Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition1102Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1102Input0) = fromList transition1102Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1102 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0148 = 1 • support0229 := by
  have hs : support0148 = fromList transition1102Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1102Chunk0]
  have hn : (transition1102Raw0 : Multiset ℕ) = 1 • (supportNumbers0229 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0229] using hm

private def transition1103Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition1103Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 648, 649, 650, 651, 652, 653, 654, 655, 64, 65, 66, 67, 68, 69, 70, 71, 712, 713, 714, 715, 716, 717, 718, 719, 128, 129, 130, 131, 132, 133, 134, 135, 520, 521, 522, 523, 524, 525, 526, 527, 192, 193, 194, 195, 196, 197, 198, 199, 584, 585, 586, 587, 588, 589, 590, 591]
private theorem transition1103Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1103Input0) = fromList transition1103Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1103 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0148 = 1 • support0230 := by
  have hs : support0148 = fromList transition1103Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1103Chunk0]
  have hn : (transition1103Raw0 : Multiset ℕ) = 1 • (supportNumbers0230 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0230] using hm

private def transition1104Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition1104Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition1104Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1104Input0) = fromList transition1104Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1104 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0148 = 1 • support0229 := by
  have hs : support0148 = fromList transition1104Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1104Chunk0]
  have hn : (transition1104Raw0 : Multiset ℕ) = 1 • (supportNumbers0229 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0229] using hm

private def transition1105Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private def transition1105Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 128, 129, 132, 133, 192, 193, 196, 197]
private theorem transition1105Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1105Input0) = fromList transition1105Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1105 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0229 = 1 • support1193 := by
  have hs : support0229 = fromList transition1105Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1105Chunk0]
  have hn : (transition1105Raw0 : Multiset ℕ) = 1 • (supportNumbers1193 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1193] using hm

private def transition1106Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private def transition1106Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 64, 65, 514, 515, 68, 69, 518, 519, 128, 129, 706, 707, 132, 133, 710, 711, 192, 193, 642, 643, 196, 197, 646, 647]
private theorem transition1106Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1106Input0) = fromList transition1106Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1106 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0229 = 1 • support1195 := by
  have hs : support0229 = fromList transition1106Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1106Chunk0]
  have hn : (transition1106Raw0 : Multiset ℕ) = 1 • (supportNumbers1195 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1195] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
