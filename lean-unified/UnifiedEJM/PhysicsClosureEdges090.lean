import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1648Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 545, 547, 549, 551, 553, 555, 557, 559, 608, 610, 612, 614, 616, 618, 620, 622, 672, 674, 676, 678, 680, 682, 684, 686, 737, 739, 741, 743, 745, 747, 749, 751]
private def transition1648Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 289, 291, 293, 295, 297, 299, 301, 303, 352, 354, 356, 358, 360, 362, 364, 366, 416, 418, 420, 422, 424, 426, 428, 430, 481, 483, 485, 487, 489, 491, 493, 495]
private theorem transition1648Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1648Input0) = fromList transition1648Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1648 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1415 = 1 • support1416 := by
  have hs : support1415 = fromList transition1648Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1648Chunk0]
  have hn : (transition1648Raw0 : Multiset ℕ) = 1 • (supportNumbers1416 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1416] using hm

private def transition1649Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 545, 547, 549, 551, 553, 555, 557, 559, 608, 610, 612, 614, 616, 618, 620, 622, 672, 674, 676, 678, 680, 682, 684, 686, 737, 739, 741, 743, 745, 747, 749, 751]
private def transition1649Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 129, 705, 131, 707, 133, 709, 135, 711, 137, 713, 139, 715, 141, 717, 143, 719, 192, 640, 194, 642, 196, 644, 198, 646, 200, 648, 202, 650, 204, 652, 206, 654, 289, 865, 291, 867, 293, 869, 295, 871, 297, 873, 299, 875, 301, 877, 303, 879, 352, 800, 354, 802, 356, 804, 358, 806, 360, 808, 362, 810, 364, 812, 366, 814, 416, 992, 418, 994, 420, 996, 422, 998, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 481, 929, 483, 931, 485, 933, 487, 935, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition1649Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1649Input0) = fromList transition1649Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1649 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1415 = 1 • support1418 := by
  have hs : support1415 = fromList transition1649Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1649Chunk0]
  have hn : (transition1649Raw0 : Multiset ℕ) = 1 • (supportNumbers1418 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1418] using hm

private def transition1650Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1650Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 1, 3, 5, 7, 8, 10, 12, 14, 64, 66, 68, 70, 73, 75, 77, 79, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private theorem transition1650Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1650Input0) = fromList transition1650Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1650Input1 : List ℕ := [513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 768, 770, 772, 774, 777, 779, 781, 783, 833, 835, 837, 839, 840, 842, 844, 846, 897, 899, 901, 903, 904, 906, 908, 910, 960, 962, 964, 966, 969, 971, 973, 975]
private def transition1650Raw1 : List ℕ := [257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private theorem transition1650Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1650Input1) = fromList transition1650Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1650 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0228 = 1 • support0084 := by
  have hs : support0228 = fromList transition1650Input0 + fromList transition1650Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1650Chunk0, transition1650Chunk1]
  have hn : (transition1650Raw0 : Multiset ℕ) + (transition1650Raw1 : Multiset ℕ) = 1 • (supportNumbers0084 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0084] using hm

private def transition1651Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1651Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718, 129, 513, 131, 515, 133, 517, 135, 519, 136, 520, 138, 522, 140, 524, 142, 526, 192, 576, 194, 578, 196, 580, 198, 582, 201, 585, 203, 587, 205, 589, 207, 591, 1, 641, 3, 643, 5, 645, 7, 647, 8, 648, 10, 650, 12, 652, 14, 654, 64, 704, 66, 706, 68, 708, 70, 710, 73, 713, 75, 715, 77, 717, 79, 719, 128, 512, 130, 514, 132, 516, 134, 518, 137, 521, 139, 523, 141, 525, 143, 527, 193, 577, 195, 579, 197, 581, 199, 583, 200, 584, 202, 586, 204, 588, 206, 590]
private theorem transition1651Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1651Input0) = fromList transition1651Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1651Input1 : List ℕ := [513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 768, 770, 772, 774, 777, 779, 781, 783, 833, 835, 837, 839, 840, 842, 844, 846, 897, 899, 901, 903, 904, 906, 908, 910, 960, 962, 964, 966, 969, 971, 973, 975]
private def transition1651Raw1 : List ℕ := [257, 897, 259, 899, 261, 901, 263, 903, 264, 904, 266, 906, 268, 908, 270, 910, 320, 960, 322, 962, 324, 964, 326, 966, 329, 969, 331, 971, 333, 973, 335, 975, 384, 768, 386, 770, 388, 772, 390, 774, 393, 777, 395, 779, 397, 781, 399, 783, 449, 833, 451, 835, 453, 837, 455, 839, 456, 840, 458, 842, 460, 844, 462, 846, 256, 896, 258, 898, 260, 900, 262, 902, 265, 905, 267, 907, 269, 909, 271, 911, 321, 961, 323, 963, 325, 965, 327, 967, 328, 968, 330, 970, 332, 972, 334, 974, 385, 769, 387, 771, 389, 773, 391, 775, 392, 776, 394, 778, 396, 780, 398, 782, 448, 832, 450, 834, 452, 836, 454, 838, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition1651Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1651Input1) = fromList transition1651Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1651 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0228 = 1 • support0085 := by
  have hs : support0228 = fromList transition1651Input0 + fromList transition1651Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1651Chunk0, transition1651Chunk1]
  have hn : (transition1651Raw0 : Multiset ℕ) + (transition1651Raw1 : Multiset ℕ) = 1 • (supportNumbers0085 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0085] using hm

private def transition1652Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1652Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 1, 3, 5, 7, 8, 10, 12, 14, 64, 66, 68, 70, 73, 75, 77, 79, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private theorem transition1652Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1652Input0) = fromList transition1652Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1652Input1 : List ℕ := [513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 768, 770, 772, 774, 777, 779, 781, 783, 833, 835, 837, 839, 840, 842, 844, 846, 897, 899, 901, 903, 904, 906, 908, 910, 960, 962, 964, 966, 969, 971, 973, 975]
private def transition1652Raw1 : List ℕ := [257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private theorem transition1652Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1652Input1) = fromList transition1652Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1652 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0228 = 1 • support0084 := by
  have hs : support0228 = fromList transition1652Input0 + fromList transition1652Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1652Chunk0, transition1652Chunk1]
  have hn : (transition1652Raw0 : Multiset ℕ) + (transition1652Raw1 : Multiset ℕ) = 1 • (supportNumbers0084 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0084] using hm

private def transition1653Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1653Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 9, 553, 11, 555, 13, 557, 15, 559, 65, 609, 67, 611, 69, 613, 71, 615, 72, 616, 74, 618, 76, 620, 78, 622, 129, 673, 131, 675, 133, 677, 135, 679, 136, 680, 138, 682, 140, 684, 142, 686, 192, 736, 194, 738, 196, 740, 198, 742, 201, 745, 203, 747, 205, 749, 207, 751, 1, 545, 3, 547, 5, 549, 7, 551, 8, 552, 10, 554, 12, 556, 14, 558, 64, 608, 66, 610, 68, 612, 70, 614, 73, 617, 75, 619, 77, 621, 79, 623, 128, 672, 130, 674, 132, 676, 134, 678, 137, 681, 139, 683, 141, 685, 143, 687, 193, 737, 195, 739, 197, 741, 199, 743, 200, 744, 202, 746, 204, 748, 206, 750]
private theorem transition1653Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1653Input0) = fromList transition1653Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1653Input1 : List ℕ := [513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 768, 770, 772, 774, 777, 779, 781, 783, 833, 835, 837, 839, 840, 842, 844, 846, 897, 899, 901, 903, 904, 906, 908, 910, 960, 962, 964, 966, 969, 971, 973, 975]
private def transition1653Raw1 : List ℕ := [257, 801, 259, 803, 261, 805, 263, 807, 264, 808, 266, 810, 268, 812, 270, 814, 320, 864, 322, 866, 324, 868, 326, 870, 329, 873, 331, 875, 333, 877, 335, 879, 384, 928, 386, 930, 388, 932, 390, 934, 393, 937, 395, 939, 397, 941, 399, 943, 449, 993, 451, 995, 453, 997, 455, 999, 456, 1000, 458, 1002, 460, 1004, 462, 1006, 256, 800, 258, 802, 260, 804, 262, 806, 265, 809, 267, 811, 269, 813, 271, 815, 321, 865, 323, 867, 325, 869, 327, 871, 328, 872, 330, 874, 332, 876, 334, 878, 385, 929, 387, 931, 389, 933, 391, 935, 392, 936, 394, 938, 396, 940, 398, 942, 448, 992, 450, 994, 452, 996, 454, 998, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition1653Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1653Input1) = fromList transition1653Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1653 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0228 = 1 • support0757 := by
  have hs : support0228 = fromList transition1653Input0 + fromList transition1653Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1653Chunk0, transition1653Chunk1]
  have hn : (transition1653Raw0 : Multiset ℕ) + (transition1653Raw1 : Multiset ℕ) = 1 • (supportNumbers0757 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0757] using hm

private def transition1654Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private def transition1654Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition1654Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1654Input0) = fromList transition1654Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1654 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0229 = 1 • support0229 := by
  have hs : support0229 = fromList transition1654Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1654Chunk0]
  have hn : (transition1654Raw0 : Multiset ℕ) = 1 • (supportNumbers0229 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0229] using hm

private def transition1655Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private def transition1655Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition1655Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1655Input0) = fromList transition1655Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1655 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0229 = 1 • support0229 := by
  have hs : support0229 = fromList transition1655Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1655Chunk0]
  have hn : (transition1655Raw0 : Multiset ℕ) = 1 • (supportNumbers0229 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0229] using hm

private def transition1656Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private def transition1656Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition1656Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1656Input0) = fromList transition1656Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1656 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0229 = 1 • support0229 := by
  have hs : support0229 = fromList transition1656Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1656Chunk0]
  have hn : (transition1656Raw0 : Multiset ℕ) = 1 • (supportNumbers0229 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0229] using hm

private def transition1657Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private def transition1657Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition1657Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1657Input0) = fromList transition1657Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1657 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0229 = 1 • support0229 := by
  have hs : support0229 = fromList transition1657Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1657Chunk0]
  have hn : (transition1657Raw0 : Multiset ℕ) = 1 • (supportNumbers0229 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0229] using hm

private def transition1658Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private def transition1658Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition1658Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1658Input0) = fromList transition1658Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1658 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0229 = 1 • support0229 := by
  have hs : support0229 = fromList transition1658Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1658Chunk0]
  have hn : (transition1658Raw0 : Multiset ℕ) = 1 • (supportNumbers0229 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0229] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
