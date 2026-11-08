import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1069Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751]
private def transition1069Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 8, 584, 9, 585, 10, 586, 11, 587, 12, 588, 13, 589, 14, 590, 15, 591, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 72, 520, 73, 521, 74, 522, 75, 523, 76, 524, 77, 525, 78, 526, 79, 527, 416, 992, 417, 993, 418, 994, 419, 995, 420, 996, 421, 997, 422, 998, 423, 999, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 428, 1004, 429, 1005, 430, 1006, 431, 1007, 480, 928, 481, 929, 482, 930, 483, 931, 484, 932, 485, 933, 486, 934, 487, 935, 488, 936, 489, 937, 490, 938, 491, 939, 492, 940, 493, 941, 494, 942, 495, 943]
private theorem transition1069Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1069Input0) = fromList transition1069Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1069 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1181 = 1 • support1184 := by
  have hs : support1181 = fromList transition1069Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1069Chunk0]
  have hn : (transition1069Raw0 : Multiset ℕ) = 1 • (supportNumbers1184 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1184] using hm

private def transition1070Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1070Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition1070Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1070Input0) = fromList transition1070Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1070Input1 : List ℕ := [520, 521, 522, 523, 524, 525, 526, 527, 584, 585, 586, 587, 588, 589, 590, 591, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 768, 769, 770, 771, 772, 773, 774, 775, 832, 833, 834, 835, 836, 837, 838, 839, 904, 905, 906, 907, 908, 909, 910, 911, 968, 969, 970, 971, 972, 973, 974, 975]
private def transition1070Raw1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private theorem transition1070Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1070Input1) = fromList transition1070Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1070 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0143 = 1 • support0084 := by
  have hs : support0143 = fromList transition1070Input0 + fromList transition1070Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1070Chunk0, transition1070Chunk1]
  have hn : (transition1070Raw0 : Multiset ℕ) + (transition1070Raw1 : Multiset ℕ) = 1 • (supportNumbers0084 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0084] using hm

private def transition1071Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1071Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 136, 520, 137, 521, 138, 522, 139, 523, 140, 524, 141, 525, 142, 526, 143, 527, 200, 584, 201, 585, 202, 586, 203, 587, 204, 588, 205, 589, 206, 590, 207, 591, 8, 648, 9, 649, 10, 650, 11, 651, 12, 652, 13, 653, 14, 654, 15, 655, 72, 712, 73, 713, 74, 714, 75, 715, 76, 716, 77, 717, 78, 718, 79, 719, 128, 512, 129, 513, 130, 514, 131, 515, 132, 516, 133, 517, 134, 518, 135, 519, 192, 576, 193, 577, 194, 578, 195, 579, 196, 580, 197, 581, 198, 582, 199, 583]
private theorem transition1071Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1071Input0) = fromList transition1071Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1071Input1 : List ℕ := [520, 521, 522, 523, 524, 525, 526, 527, 584, 585, 586, 587, 588, 589, 590, 591, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 768, 769, 770, 771, 772, 773, 774, 775, 832, 833, 834, 835, 836, 837, 838, 839, 904, 905, 906, 907, 908, 909, 910, 911, 968, 969, 970, 971, 972, 973, 974, 975]
private def transition1071Raw1 : List ℕ := [264, 904, 265, 905, 266, 906, 267, 907, 268, 908, 269, 909, 270, 910, 271, 911, 328, 968, 329, 969, 330, 970, 331, 971, 332, 972, 333, 973, 334, 974, 335, 975, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 256, 896, 257, 897, 258, 898, 259, 899, 260, 900, 261, 901, 262, 902, 263, 903, 320, 960, 321, 961, 322, 962, 323, 963, 324, 964, 325, 965, 326, 966, 327, 967, 392, 776, 393, 777, 394, 778, 395, 779, 396, 780, 397, 781, 398, 782, 399, 783, 456, 840, 457, 841, 458, 842, 459, 843, 460, 844, 461, 845, 462, 846, 463, 847]
private theorem transition1071Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1071Input1) = fromList transition1071Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1071 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0143 = 1 • support0085 := by
  have hs : support0143 = fromList transition1071Input0 + fromList transition1071Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1071Chunk0, transition1071Chunk1]
  have hn : (transition1071Raw0 : Multiset ℕ) + (transition1071Raw1 : Multiset ℕ) = 1 • (supportNumbers0085 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0085] using hm

private def transition1072Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1072Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition1072Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1072Input0) = fromList transition1072Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1072Input1 : List ℕ := [520, 521, 522, 523, 524, 525, 526, 527, 584, 585, 586, 587, 588, 589, 590, 591, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 768, 769, 770, 771, 772, 773, 774, 775, 832, 833, 834, 835, 836, 837, 838, 839, 904, 905, 906, 907, 908, 909, 910, 911, 968, 969, 970, 971, 972, 973, 974, 975]
private def transition1072Raw1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private theorem transition1072Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1072Input1) = fromList transition1072Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1072 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0143 = 1 • support0084 := by
  have hs : support0143 = fromList transition1072Input0 + fromList transition1072Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1072Chunk0, transition1072Chunk1]
  have hn : (transition1072Raw0 : Multiset ℕ) + (transition1072Raw1 : Multiset ℕ) = 1 • (supportNumbers0084 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0084] using hm

private def transition1073Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1073Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 8, 552, 9, 553, 10, 554, 11, 555, 12, 556, 13, 557, 14, 558, 15, 559, 72, 616, 73, 617, 74, 618, 75, 619, 76, 620, 77, 621, 78, 622, 79, 623, 128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743]
private theorem transition1073Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1073Input0) = fromList transition1073Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1073Input1 : List ℕ := [520, 521, 522, 523, 524, 525, 526, 527, 584, 585, 586, 587, 588, 589, 590, 591, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 768, 769, 770, 771, 772, 773, 774, 775, 832, 833, 834, 835, 836, 837, 838, 839, 904, 905, 906, 907, 908, 909, 910, 911, 968, 969, 970, 971, 972, 973, 974, 975]
private def transition1073Raw1 : List ℕ := [264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007]
private theorem transition1073Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1073Input1) = fromList transition1073Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1073 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0143 = 1 • support0757 := by
  have hs : support0143 = fromList transition1073Input0 + fromList transition1073Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1073Chunk0, transition1073Chunk1]
  have hn : (transition1073Raw0 : Multiset ℕ) + (transition1073Raw1 : Multiset ℕ) = 1 • (supportNumbers0757 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0757] using hm

private def transition1074Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private def transition1074Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private theorem transition1074Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1074Input0) = fromList transition1074Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1074 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0144 = 1 • support0144 := by
  have hs : support0144 = fromList transition1074Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1074Chunk0]
  have hn : (transition1074Raw0 : Multiset ℕ) = 1 • (supportNumbers0144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0144] using hm

private def transition1075Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private def transition1075Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private theorem transition1075Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1075Input0) = fromList transition1075Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1075 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0144 = 1 • support0144 := by
  have hs : support0144 = fromList transition1075Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1075Chunk0]
  have hn : (transition1075Raw0 : Multiset ℕ) = 1 • (supportNumbers0144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0144] using hm

private def transition1076Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private def transition1076Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private theorem transition1076Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1076Input0) = fromList transition1076Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1076 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0144 = 1 • support0144 := by
  have hs : support0144 = fromList transition1076Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1076Chunk0]
  have hn : (transition1076Raw0 : Multiset ℕ) = 1 • (supportNumbers0144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0144] using hm

private def transition1077Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private def transition1077Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private theorem transition1077Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1077Input0) = fromList transition1077Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1077 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0144 = 1 • support0144 := by
  have hs : support0144 = fromList transition1077Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1077Chunk0]
  have hn : (transition1077Raw0 : Multiset ℕ) = 1 • (supportNumbers0144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0144] using hm

private def transition1078Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private def transition1078Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private theorem transition1078Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1078Input0) = fromList transition1078Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1078 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0144 = 1 • support0144 := by
  have hs : support0144 = fromList transition1078Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1078Chunk0]
  have hn : (transition1078Raw0 : Multiset ℕ) = 1 • (supportNumbers0144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0144] using hm

private def transition1079Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private def transition1079Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 129, 705, 131, 707, 133, 709, 135, 711, 192, 640, 194, 642, 196, 644, 198, 646]
private theorem transition1079Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1079Input0) = fromList transition1079Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1079 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0144 = 1 • support0314 := by
  have hs : support0144 = fromList transition1079Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1079Chunk0]
  have hn : (transition1079Raw0 : Multiset ℕ) = 1 • (supportNumbers0314 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0314] using hm

private def transition1080Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 520, 522, 524, 526, 585, 587, 589, 591, 649, 651, 653, 655, 712, 714, 716, 718]
private def transition1080Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 264, 266, 268, 270, 329, 331, 333, 335, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition1080Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1080Input0) = fromList transition1080Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1080 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0145 = 1 • support0224 := by
  have hs : support0145 = fromList transition1080Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1080Chunk0]
  have hn : (transition1080Raw0 : Multiset ℕ) = 1 • (supportNumbers0224 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0224] using hm

private def transition1081Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 520, 522, 524, 526, 585, 587, 589, 591, 649, 651, 653, 655, 712, 714, 716, 718]
private def transition1081Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 129, 513, 131, 515, 133, 517, 135, 519, 192, 576, 194, 578, 196, 580, 198, 582, 264, 904, 266, 906, 268, 908, 270, 910, 329, 969, 331, 971, 333, 973, 335, 975, 393, 777, 395, 779, 397, 781, 399, 783, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition1081Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1081Input0) = fromList transition1081Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1081 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0145 = 1 • support0225 := by
  have hs : support0145 = fromList transition1081Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1081Chunk0]
  have hn : (transition1081Raw0 : Multiset ℕ) = 1 • (supportNumbers0225 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0225] using hm

private def transition1082Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 520, 522, 524, 526, 585, 587, 589, 591, 649, 651, 653, 655, 712, 714, 716, 718]
private def transition1082Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 264, 266, 268, 270, 329, 331, 333, 335, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition1082Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1082Input0) = fromList transition1082Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1082 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0145 = 1 • support0224 := by
  have hs : support0145 = fromList transition1082Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1082Chunk0]
  have hn : (transition1082Raw0 : Multiset ℕ) = 1 • (supportNumbers0224 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0224] using hm

private def transition1083Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 264, 266, 268, 270, 329, 331, 333, 335, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition1083Raw0 : List ℕ := [0, 4, 65, 69, 129, 133, 192, 196, 10, 14, 75, 79, 139, 143, 202, 206]
private theorem transition1083Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1083Input0) = fromList transition1083Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1083 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0224 = 1 • support1186 := by
  have hs : support0224 = fromList transition1083Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1083Chunk0]
  have hn : (transition1083Raw0 : Multiset ℕ) = 1 • (supportNumbers1186 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1186] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
