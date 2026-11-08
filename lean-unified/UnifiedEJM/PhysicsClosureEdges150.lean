import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2668Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 512, 514, 516, 518, 521, 523, 525, 527, 577, 579, 581, 583, 584, 586, 588, 590, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718]
private def transition2668Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private theorem transition2668Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2668Input0) = fromList transition2668Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2668 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0389 = 1 • support0308 := by
  have hs : support0389 = fromList transition2668Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2668Chunk0]
  have hn : (transition2668Raw0 : Multiset ℕ) = 1 • (supportNumbers0308 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0308] using hm

private def transition2669Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 512, 514, 516, 518, 521, 523, 525, 527, 577, 579, 581, 583, 584, 586, 588, 590, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718]
private def transition2669Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 9, 553, 11, 555, 13, 557, 15, 559, 65, 609, 67, 611, 69, 613, 71, 615, 72, 616, 74, 618, 76, 620, 78, 622, 128, 672, 130, 674, 132, 676, 134, 678, 137, 681, 139, 683, 141, 685, 143, 687, 193, 737, 195, 739, 197, 741, 199, 743, 200, 744, 202, 746, 204, 748, 206, 750, 256, 800, 258, 802, 260, 804, 262, 806, 265, 809, 267, 811, 269, 813, 271, 815, 321, 865, 323, 867, 325, 869, 327, 871, 328, 872, 330, 874, 332, 876, 334, 878, 384, 928, 386, 930, 388, 932, 390, 934, 393, 937, 395, 939, 397, 941, 399, 943, 449, 993, 451, 995, 453, 997, 455, 999, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition2669Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2669Input0) = fromList transition2669Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2669 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0389 = 1 • support1397 := by
  have hs : support0389 = fromList transition2669Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2669Chunk0]
  have hn : (transition2669Raw0 : Multiset ℕ) = 1 • (supportNumbers1397 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1397] using hm

private def transition2670Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335]
private def transition2670Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 8, 10, 12, 14, 73, 75, 77, 79]
private theorem transition2670Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2670Input0) = fromList transition2670Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2670 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0390 = 1 • support0004 := by
  have hs : support0390 = fromList transition2670Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2670Chunk0]
  have hn : (transition2670Raw0 : Multiset ℕ) = 1 • (supportNumbers0004 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0004] using hm

private def transition2671Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335]
private def transition2671Raw0 : List ℕ := [0, 2, 4, 6, 649, 651, 653, 655, 65, 67, 69, 71, 712, 714, 716, 718, 641, 643, 645, 647, 8, 10, 12, 14, 704, 706, 708, 710, 73, 75, 77, 79]
private theorem transition2671Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2671Input0) = fromList transition2671Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2671 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0390 = 1 • support0005 := by
  have hs : support0390 = fromList transition2671Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2671Chunk0]
  have hn : (transition2671Raw0 : Multiset ℕ) = 1 • (supportNumbers0005 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0005] using hm

private def transition2672Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335]
private def transition2672Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 8, 10, 12, 14, 73, 75, 77, 79]
private theorem transition2672Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2672Input0) = fromList transition2672Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2672 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0390 = 1 • support0004 := by
  have hs : support0390 = fromList transition2672Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2672Chunk0]
  have hn : (transition2672Raw0 : Multiset ℕ) = 1 • (supportNumbers0004 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0004] using hm

private def transition2673Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335]
private def transition2673Raw0 : List ℕ := [0, 2, 4, 6, 553, 555, 557, 559, 65, 67, 69, 71, 616, 618, 620, 622, 545, 547, 549, 551, 8, 10, 12, 14, 608, 610, 612, 614, 73, 75, 77, 79]
private theorem transition2673Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2673Input0) = fromList transition2673Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2673 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0390 = 1 • support1699 := by
  have hs : support0390 = fromList transition2673Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2673Chunk0]
  have hn : (transition2673Raw0 : Multiset ℕ) = 1 • (supportNumbers1699 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1699] using hm

private def transition2674Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 545, 547, 549, 551, 553, 555, 557, 559, 608, 610, 612, 614, 616, 618, 620, 622]
private def transition2674Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 289, 291, 293, 295, 297, 299, 301, 303, 352, 354, 356, 358, 360, 362, 364, 366]
private theorem transition2674Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2674Input0) = fromList transition2674Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2674 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1699 = 1 • support1700 := by
  have hs : support1699 = fromList transition2674Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2674Chunk0]
  have hn : (transition2674Raw0 : Multiset ℕ) = 1 • (supportNumbers1700 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1700] using hm

private def transition2675Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 545, 547, 549, 551, 553, 555, 557, 559, 608, 610, 612, 614, 616, 618, 620, 622]
private def transition2675Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 289, 865, 291, 867, 293, 869, 295, 871, 297, 873, 299, 875, 301, 877, 303, 879, 352, 800, 354, 802, 356, 804, 358, 806, 360, 808, 362, 810, 364, 812, 366, 814]
private theorem transition2675Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2675Input0) = fromList transition2675Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2675 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1699 = 1 • support1702 := by
  have hs : support1699 = fromList transition2675Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2675Chunk0]
  have hn : (transition2675Raw0 : Multiset ℕ) = 1 • (supportNumbers1702 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1702] using hm

private def transition2676Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 897, 899, 901, 903, 904, 906, 908, 910, 960, 962, 964, 966, 969, 971, 973, 975]
private def transition2676Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 1, 3, 5, 7, 8, 10, 12, 14, 64, 66, 68, 70, 73, 75, 77, 79, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private theorem transition2676Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2676Input0) = fromList transition2676Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2676 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0391 = 1 • support0328 := by
  have hs : support0391 = fromList transition2676Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2676Chunk0]
  have hn : (transition2676Raw0 : Multiset ℕ) = 1 • (supportNumbers0328 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0328] using hm

private def transition2677Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 897, 899, 901, 903, 904, 906, 908, 910, 960, 962, 964, 966, 969, 971, 973, 975]
private def transition2677Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718, 1, 641, 3, 643, 5, 645, 7, 647, 8, 648, 10, 650, 12, 652, 14, 654, 64, 704, 66, 706, 68, 708, 70, 710, 73, 713, 75, 715, 77, 717, 79, 719, 384, 768, 386, 770, 388, 772, 390, 774, 393, 777, 395, 779, 397, 781, 399, 783, 449, 833, 451, 835, 453, 837, 455, 839, 456, 840, 458, 842, 460, 844, 462, 846, 385, 769, 387, 771, 389, 773, 391, 775, 392, 776, 394, 778, 396, 780, 398, 782, 448, 832, 450, 834, 452, 836, 454, 838, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition2677Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2677Input0) = fromList transition2677Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2677 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0391 = 1 • support0329 := by
  have hs : support0391 = fromList transition2677Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2677Chunk0]
  have hn : (transition2677Raw0 : Multiset ℕ) = 1 • (supportNumbers0329 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0329] using hm

private def transition2678Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 897, 899, 901, 903, 904, 906, 908, 910, 960, 962, 964, 966, 969, 971, 973, 975]
private def transition2678Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 1, 3, 5, 7, 8, 10, 12, 14, 64, 66, 68, 70, 73, 75, 77, 79, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private theorem transition2678Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2678Input0) = fromList transition2678Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2678 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0391 = 1 • support0328 := by
  have hs : support0391 = fromList transition2678Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2678Chunk0]
  have hn : (transition2678Raw0 : Multiset ℕ) = 1 • (supportNumbers0328 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0328] using hm

private def transition2679Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 897, 899, 901, 903, 904, 906, 908, 910, 960, 962, 964, 966, 969, 971, 973, 975]
private def transition2679Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 9, 553, 11, 555, 13, 557, 15, 559, 65, 609, 67, 611, 69, 613, 71, 615, 72, 616, 74, 618, 76, 620, 78, 622, 1, 545, 3, 547, 5, 549, 7, 551, 8, 552, 10, 554, 12, 556, 14, 558, 64, 608, 66, 610, 68, 612, 70, 614, 73, 617, 75, 619, 77, 621, 79, 623, 384, 928, 386, 930, 388, 932, 390, 934, 393, 937, 395, 939, 397, 941, 399, 943, 449, 993, 451, 995, 453, 997, 455, 999, 456, 1000, 458, 1002, 460, 1004, 462, 1006, 385, 929, 387, 931, 389, 933, 391, 935, 392, 936, 394, 938, 396, 940, 398, 942, 448, 992, 450, 994, 452, 996, 454, 998, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition2679Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2679Input0) = fromList transition2679Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2679 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0391 = 1 • support1445 := by
  have hs : support0391 = fromList transition2679Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2679Chunk0]
  have hn : (transition2679Raw0 : Multiset ℕ) = 1 • (supportNumbers1445 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1445] using hm

private def transition2680Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition2680Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition2680Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2680Input0) = fromList transition2680Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2680 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0392 = 1 • support0088 := by
  have hs : support0392 = fromList transition2680Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2680Chunk0]
  have hn : (transition2680Raw0 : Multiset ℕ) = 1 • (supportNumbers0088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0088] using hm

private def transition2681Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition2681Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition2681Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2681Input0) = fromList transition2681Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2681 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0392 = 1 • support0088 := by
  have hs : support0392 = fromList transition2681Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2681Chunk0]
  have hn : (transition2681Raw0 : Multiset ℕ) = 1 • (supportNumbers0088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0088] using hm

private def transition2682Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition2682Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition2682Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2682Input0) = fromList transition2682Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2682 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0392 = 1 • support0088 := by
  have hs : support0392 = fromList transition2682Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2682Chunk0]
  have hn : (transition2682Raw0 : Multiset ℕ) = 1 • (supportNumbers0088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0088] using hm

private def transition2683Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition2683Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition2683Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2683Input0) = fromList transition2683Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2683 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0392 = 1 • support0088 := by
  have hs : support0392 = fromList transition2683Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2683Chunk0]
  have hn : (transition2683Raw0 : Multiset ℕ) = 1 • (supportNumbers0088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0088] using hm

private def transition2684Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition2684Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition2684Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2684Input0) = fromList transition2684Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2684 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0088 = 1 • support0088 := by
  have hs : support0088 = fromList transition2684Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2684Chunk0]
  have hn : (transition2684Raw0 : Multiset ℕ) = 1 • (supportNumbers0088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0088] using hm

private def transition2685Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition2685Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 136, 712, 137, 713, 138, 714, 139, 715, 140, 716, 141, 717, 142, 718, 143, 719, 200, 648, 201, 649, 202, 650, 203, 651, 204, 652, 205, 653, 206, 654, 207, 655]
private theorem transition2685Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2685Input0) = fromList transition2685Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2685 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0088 = 1 • support0408 := by
  have hs : support0088 = fromList transition2685Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2685Chunk0]
  have hn : (transition2685Raw0 : Multiset ℕ) = 1 • (supportNumbers0408 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0408] using hm

private def transition2686Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 776, 777, 778, 779, 780, 781, 782, 783, 840, 841, 842, 843, 844, 845, 846, 847]
private def transition2686Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335]
private theorem transition2686Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2686Input0) = fromList transition2686Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2686 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0393 = 1 • support0142 := by
  have hs : support0393 = fromList transition2686Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2686Chunk0]
  have hn : (transition2686Raw0 : Multiset ℕ) = 1 • (supportNumbers0142 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0142] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
