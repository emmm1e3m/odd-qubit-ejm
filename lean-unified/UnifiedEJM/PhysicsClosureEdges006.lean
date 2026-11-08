import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0155Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition0155Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 129, 705, 131, 707, 133, 709, 135, 711, 137, 713, 139, 715, 141, 717, 143, 719, 192, 640, 194, 642, 196, 644, 198, 646, 200, 648, 202, 650, 204, 652, 206, 654, 1, 577, 3, 579, 5, 581, 7, 583, 9, 585, 11, 587, 13, 589, 15, 591, 64, 512, 66, 514, 68, 516, 70, 518, 72, 520, 74, 522, 76, 524, 78, 526, 128, 704, 130, 706, 132, 708, 134, 710, 136, 712, 138, 714, 140, 716, 142, 718, 193, 641, 195, 643, 197, 645, 199, 647, 201, 649, 203, 651, 205, 653, 207, 655]
private theorem transition0155Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0155Input0) = fromList transition0155Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0155Input1 : List ℕ := [544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623, 673, 675, 677, 679, 681, 683, 685, 687, 736, 738, 740, 742, 744, 746, 748, 750, 801, 803, 805, 807, 809, 811, 813, 815, 864, 866, 868, 870, 872, 874, 876, 878, 928, 930, 932, 934, 936, 938, 940, 942, 993, 995, 997, 999, 1001, 1003, 1005, 1007]
private def transition0155Raw1 : List ℕ := [288, 864, 290, 866, 292, 868, 294, 870, 296, 872, 298, 874, 300, 876, 302, 878, 353, 801, 355, 803, 357, 805, 359, 807, 361, 809, 363, 811, 365, 813, 367, 815, 417, 993, 419, 995, 421, 997, 423, 999, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 480, 928, 482, 930, 484, 932, 486, 934, 488, 936, 490, 938, 492, 940, 494, 942, 289, 865, 291, 867, 293, 869, 295, 871, 297, 873, 299, 875, 301, 877, 303, 879, 352, 800, 354, 802, 356, 804, 358, 806, 360, 808, 362, 810, 364, 812, 366, 814, 416, 992, 418, 994, 420, 996, 422, 998, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 481, 929, 483, 931, 485, 933, 487, 935, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition0155Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0155Input1) = fromList transition0155Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0155 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0615 = 1 • support0618 := by
  have hs : support0615 = fromList transition0155Input0 + fromList transition0155Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0155Chunk0, transition0155Chunk1]
  have hn : (transition0155Raw0 : Multiset ℕ) + (transition0155Raw1 : Multiset ℕ) = 1 • (supportNumbers0618 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0618] using hm

private def transition0156Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0156Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71]
private theorem transition0156Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0156Input0) = fromList transition0156Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0156 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0020 = 1 • support0044 := by
  have hs : support0020 = fromList transition0156Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0156Chunk0]
  have hn : (transition0156Raw0 : Multiset ℕ) = 1 • (supportNumbers0044 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0044] using hm

private def transition0157Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0157Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 664, 665, 666, 667, 668, 669, 670, 671, 64, 65, 66, 67, 68, 69, 70, 71, 728, 729, 730, 731, 732, 733, 734, 735]
private theorem transition0157Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0157Input0) = fromList transition0157Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0157 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0020 = 1 • support0045 := by
  have hs : support0020 = fromList transition0157Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0157Chunk0]
  have hn : (transition0157Raw0 : Multiset ℕ) = 1 • (supportNumbers0045 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0045] using hm

private def transition0158Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0158Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71]
private theorem transition0158Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0158Input0) = fromList transition0158Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0158 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0020 = 1 • support0044 := by
  have hs : support0020 = fromList transition0158Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0158Chunk0]
  have hn : (transition0158Raw0 : Multiset ℕ) = 1 • (supportNumbers0044 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0044] using hm

private def transition0159Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71]
private def transition0159Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69]
private theorem transition0159Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0159Input0) = fromList transition0159Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0159 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0044 = 1 • support0619 := by
  have hs : support0044 = fromList transition0159Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0159Chunk0]
  have hn : (transition0159Raw0 : Multiset ℕ) = 1 • (supportNumbers0619 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0619] using hm

private def transition0160Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71]
private def transition0160Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 64, 65, 514, 515, 68, 69, 518, 519]
private theorem transition0160Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0160Input0) = fromList transition0160Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0160 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0044 = 1 • support0621 := by
  have hs : support0044 = fromList transition0160Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0160Chunk0]
  have hn : (transition0160Raw0 : Multiset ℕ) = 1 • (supportNumbers0621 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0621] using hm

private def transition0161Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0161Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 568, 569, 570, 571, 572, 573, 574, 575, 64, 65, 66, 67, 68, 69, 70, 71, 632, 633, 634, 635, 636, 637, 638, 639]
private theorem transition0161Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0161Input0) = fromList transition0161Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0161 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0020 = 1 • support0622 := by
  have hs : support0020 = fromList transition0161Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0161Chunk0]
  have hn : (transition0161Raw0 : Multiset ℕ) = 1 • (supportNumbers0622 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0622] using hm

private def transition0162Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 568, 569, 570, 571, 572, 573, 574, 575, 632, 633, 634, 635, 636, 637, 638, 639]
private def transition0162Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 312, 313, 314, 315, 316, 317, 318, 319, 376, 377, 378, 379, 380, 381, 382, 383]
private theorem transition0162Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0162Input0) = fromList transition0162Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0162 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0622 = 1 • support0623 := by
  have hs : support0622 = fromList transition0162Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0162Chunk0]
  have hn : (transition0162Raw0 : Multiset ℕ) = 1 • (supportNumbers0623 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0623] using hm

private def transition0163Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 568, 569, 570, 571, 572, 573, 574, 575, 632, 633, 634, 635, 636, 637, 638, 639]
private def transition0163Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 312, 888, 313, 889, 314, 890, 315, 891, 316, 892, 317, 893, 318, 894, 319, 895, 376, 824, 377, 825, 378, 826, 379, 827, 380, 828, 381, 829, 382, 830, 383, 831]
private theorem transition0163Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0163Input0) = fromList transition0163Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0163 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0622 = 1 • support0624 := by
  have hs : support0622 = fromList transition0163Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0163Chunk0]
  have hn : (transition0163Raw0 : Multiset ℕ) = 1 • (supportNumbers0624 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0624] using hm

private def transition0164Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition0164Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private theorem transition0164Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0164Input0) = fromList transition0164Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0164 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0021 = 1 • support0046 := by
  have hs : support0021 = fromList transition0164Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0164Chunk0]
  have hn : (transition0164Raw0 : Multiset ℕ) = 1 • (supportNumbers0046 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0046] using hm

private def transition0165Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition0165Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 24, 664, 25, 665, 26, 666, 27, 667, 28, 668, 29, 669, 30, 670, 31, 671, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 88, 728, 89, 729, 90, 730, 91, 731, 92, 732, 93, 733, 94, 734, 95, 735, 392, 776, 393, 777, 394, 778, 395, 779, 396, 780, 397, 781, 398, 782, 399, 783, 400, 784, 401, 785, 402, 786, 403, 787, 404, 788, 405, 789, 406, 790, 407, 791, 456, 840, 457, 841, 458, 842, 459, 843, 460, 844, 461, 845, 462, 846, 463, 847, 464, 848, 465, 849, 466, 850, 467, 851, 468, 852, 469, 853, 470, 854, 471, 855]
private theorem transition0165Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0165Input0) = fromList transition0165Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0165 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0021 = 1 • support0047 := by
  have hs : support0021 = fromList transition0165Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0165Chunk0]
  have hn : (transition0165Raw0 : Multiset ℕ) = 1 • (supportNumbers0047 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0047] using hm

private def transition0166Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition0166Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private theorem transition0166Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0166Input0) = fromList transition0166Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0166 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0021 = 1 • support0046 := by
  have hs : support0021 = fromList transition0166Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0166Chunk0]
  have hn : (transition0166Raw0 : Multiset ℕ) = 1 • (supportNumbers0046 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0046] using hm

private def transition0167Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition0167Raw0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 138, 139, 142, 143, 146, 147, 150, 151, 202, 203, 206, 207, 210, 211, 214, 215]
private theorem transition0167Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0167Input0) = fromList transition0167Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0167 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0046 = 1 • support0626 := by
  have hs : support0046 = fromList transition0167Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0167Chunk0]
  have hn : (transition0167Raw0 : Multiset ℕ) = 1 • (supportNumbers0626 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0626] using hm

private def transition0168Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition0168Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 24, 25, 602, 603, 28, 29, 606, 607, 64, 65, 514, 515, 68, 69, 518, 519, 88, 89, 538, 539, 92, 93, 542, 543, 712, 713, 138, 139, 716, 717, 142, 143, 720, 721, 146, 147, 724, 725, 150, 151, 648, 649, 202, 203, 652, 653, 206, 207, 656, 657, 210, 211, 660, 661, 214, 215]
private theorem transition0168Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0168Input0) = fromList transition0168Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0168 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0046 = 1 • support0628 := by
  have hs : support0046 = fromList transition0168Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0168Chunk0]
  have hn : (transition0168Raw0 : Multiset ℕ) = 1 • (supportNumbers0628 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0628] using hm

private def transition0169Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition0169Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 24, 568, 25, 569, 26, 570, 27, 571, 28, 572, 29, 573, 30, 574, 31, 575, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 88, 632, 89, 633, 90, 634, 91, 635, 92, 636, 93, 637, 94, 638, 95, 639, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015]
private theorem transition0169Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0169Input0) = fromList transition0169Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0169 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0021 = 1 • support0629 := by
  have hs : support0021 = fromList transition0169Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0169Chunk0]
  have hn : (transition0169Raw0 : Multiset ℕ) = 1 • (supportNumbers0629 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0629] using hm

private def transition0170Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition0170Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition0170Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0170Input0) = fromList transition0170Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0170Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 568, 569, 570, 571, 572, 573, 574, 575, 608, 609, 610, 611, 612, 613, 614, 615, 632, 633, 634, 635, 636, 637, 638, 639, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015]
private def transition0170Raw1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 312, 313, 314, 315, 316, 317, 318, 319, 352, 353, 354, 355, 356, 357, 358, 359, 376, 377, 378, 379, 380, 381, 382, 383, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503]
private theorem transition0170Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0170Input1) = fromList transition0170Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0170 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0629 = 1 • support0630 := by
  have hs : support0629 = fromList transition0170Input0 + fromList transition0170Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0170Chunk0, transition0170Chunk1]
  have hn : (transition0170Raw0 : Multiset ℕ) + (transition0170Raw1 : Multiset ℕ) = 1 • (supportNumbers0630 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0630] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
