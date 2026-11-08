import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2687Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 776, 777, 778, 779, 780, 781, 782, 783, 840, 841, 842, 843, 844, 845, 846, 847]
private def transition2687Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 136, 520, 137, 521, 138, 522, 139, 523, 140, 524, 141, 525, 142, 526, 143, 527, 200, 584, 201, 585, 202, 586, 203, 587, 204, 588, 205, 589, 206, 590, 207, 591, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 264, 904, 265, 905, 266, 906, 267, 907, 268, 908, 269, 909, 270, 910, 271, 911, 328, 968, 329, 969, 330, 970, 331, 971, 332, 972, 333, 973, 334, 974, 335, 975]
private theorem transition2687Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2687Input0) = fromList transition2687Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2687 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0393 = 1 • support0143 := by
  have hs : support0393 = fromList transition2687Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2687Chunk0]
  have hn : (transition2687Raw0 : Multiset ℕ) = 1 • (supportNumbers0143 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0143] using hm

private def transition2688Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 776, 777, 778, 779, 780, 781, 782, 783, 840, 841, 842, 843, 844, 845, 846, 847]
private def transition2688Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335]
private theorem transition2688Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2688Input0) = fromList transition2688Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2688 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0393 = 1 • support0142 := by
  have hs : support0393 = fromList transition2688Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2688Chunk0]
  have hn : (transition2688Raw0 : Multiset ℕ) = 1 • (supportNumbers0142 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0142] using hm

private def transition2689Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 776, 777, 778, 779, 780, 781, 782, 783, 840, 841, 842, 843, 844, 845, 846, 847]
private def transition2689Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879]
private theorem transition2689Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2689Input0) = fromList transition2689Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2689 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0393 = 1 • support0946 := by
  have hs : support0393 = fromList transition2689Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2689Chunk0]
  have hn : (transition2689Raw0 : Multiset ℕ) = 1 • (supportNumbers0946 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0946] using hm

private def transition2690Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]
private def transition2690Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]
private theorem transition2690Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2690Input0) = fromList transition2690Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2690 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0394 = 1 • support0328 := by
  have hs : support0394 = fromList transition2690Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2690Chunk0]
  have hn : (transition2690Raw0 : Multiset ℕ) = 1 • (supportNumbers0328 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0328] using hm

private def transition2691Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]
private def transition2691Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 8, 648, 9, 649, 10, 650, 11, 651, 12, 652, 13, 653, 14, 654, 15, 655, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 72, 712, 73, 713, 74, 714, 75, 715, 76, 716, 77, 717, 78, 718, 79, 719, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 392, 776, 393, 777, 394, 778, 395, 779, 396, 780, 397, 781, 398, 782, 399, 783, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 456, 840, 457, 841, 458, 842, 459, 843, 460, 844, 461, 845, 462, 846, 463, 847]
private theorem transition2691Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2691Input0) = fromList transition2691Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2691 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0394 = 1 • support0329 := by
  have hs : support0394 = fromList transition2691Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2691Chunk0]
  have hn : (transition2691Raw0 : Multiset ℕ) = 1 • (supportNumbers0329 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0329] using hm

private def transition2692Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]
private def transition2692Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]
private theorem transition2692Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2692Input0) = fromList transition2692Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2692 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0394 = 1 • support0328 := by
  have hs : support0394 = fromList transition2692Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2692Chunk0]
  have hn : (transition2692Raw0 : Multiset ℕ) = 1 • (supportNumbers0328 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0328] using hm

private def transition2693Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]
private def transition2693Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 8, 552, 9, 553, 10, 554, 11, 555, 12, 556, 13, 557, 14, 558, 15, 559, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 72, 616, 73, 617, 74, 618, 75, 619, 76, 620, 77, 621, 78, 622, 79, 623, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007]
private theorem transition2693Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2693Input0) = fromList transition2693Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2693 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0394 = 1 • support1445 := by
  have hs : support0394 = fromList transition2693Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2693Chunk0]
  have hn : (transition2693Raw0 : Multiset ℕ) = 1 • (supportNumbers1445 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1445] using hm

private def transition2694Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition2694Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private theorem transition2694Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2694Input0) = fromList transition2694Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2694 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0395 = 1 • support0144 := by
  have hs : support0395 = fromList transition2694Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2694Chunk0]
  have hn : (transition2694Raw0 : Multiset ℕ) = 1 • (supportNumbers0144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0144] using hm

private def transition2695Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition2695Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 641, 643, 645, 647, 704, 706, 708, 710, 512, 514, 516, 518, 577, 579, 581, 583]
private theorem transition2695Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2695Input0) = fromList transition2695Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2695 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0395 = 1 • support0443 := by
  have hs : support0395 = fromList transition2695Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2695Chunk0]
  have hn : (transition2695Raw0 : Multiset ℕ) = 1 • (supportNumbers0443 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0443] using hm

private def transition2696Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition2696Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private theorem transition2696Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2696Input0) = fromList transition2696Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2696 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0395 = 1 • support0144 := by
  have hs : support0395 = fromList transition2696Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2696Chunk0]
  have hn : (transition2696Raw0 : Multiset ℕ) = 1 • (supportNumbers0144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0144] using hm

private def transition2697Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition2697Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 545, 547, 549, 551, 608, 610, 612, 614, 672, 674, 676, 678, 737, 739, 741, 743]
private theorem transition2697Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2697Input0) = fromList transition2697Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2697 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0395 = 1 • support1703 := by
  have hs : support0395 = fromList transition2697Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2697Chunk0]
  have hn : (transition2697Raw0 : Multiset ℕ) = 1 • (supportNumbers1703 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1703] using hm

private def transition2698Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 545, 547, 549, 551, 608, 610, 612, 614, 672, 674, 676, 678, 737, 739, 741, 743]
private def transition2698Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 289, 291, 293, 295, 352, 354, 356, 358, 416, 418, 420, 422, 481, 483, 485, 487]
private theorem transition2698Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2698Input0) = fromList transition2698Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2698 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1703 = 1 • support1704 := by
  have hs : support1703 = fromList transition2698Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2698Chunk0]
  have hn : (transition2698Raw0 : Multiset ℕ) = 1 • (supportNumbers1704 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1704] using hm

private def transition2699Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 545, 547, 549, 551, 608, 610, 612, 614, 672, 674, 676, 678, 737, 739, 741, 743]
private def transition2699Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 129, 705, 131, 707, 133, 709, 135, 711, 192, 640, 194, 642, 196, 644, 198, 646, 289, 865, 291, 867, 293, 869, 295, 871, 352, 800, 354, 802, 356, 804, 358, 806, 416, 992, 418, 994, 420, 996, 422, 998, 481, 929, 483, 931, 485, 933, 487, 935]
private theorem transition2699Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2699Input0) = fromList transition2699Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2699 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1703 = 1 • support1706 := by
  have hs : support1703 = fromList transition2699Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2699Chunk0]
  have hn : (transition2699Raw0 : Multiset ℕ) = 1 • (supportNumbers1706 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1706] using hm

private def transition2700Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839, 897, 899, 901, 903, 960, 962, 964, 966]
private def transition2700Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 1, 3, 5, 7, 64, 66, 68, 70, 128, 130, 132, 134, 193, 195, 197, 199, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455, 256, 258, 260, 262, 321, 323, 325, 327, 385, 387, 389, 391, 448, 450, 452, 454]
private theorem transition2700Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2700Input0) = fromList transition2700Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2700 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0396 = 1 • support0320 := by
  have hs : support0396 = fromList transition2700Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2700Chunk0]
  have hn : (transition2700Raw0 : Multiset ℕ) = 1 • (supportNumbers0320 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0320] using hm

private def transition2701Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839, 897, 899, 901, 903, 960, 962, 964, 966]
private def transition2701Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 129, 513, 131, 515, 133, 517, 135, 519, 192, 576, 194, 578, 196, 580, 198, 582, 1, 641, 3, 643, 5, 645, 7, 647, 64, 704, 66, 706, 68, 708, 70, 710, 128, 512, 130, 514, 132, 516, 134, 518, 193, 577, 195, 579, 197, 581, 199, 583, 257, 897, 259, 899, 261, 901, 263, 903, 320, 960, 322, 962, 324, 964, 326, 966, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 256, 896, 258, 898, 260, 900, 262, 902, 321, 961, 323, 963, 325, 965, 327, 967, 385, 769, 387, 771, 389, 773, 391, 775, 448, 832, 450, 834, 452, 836, 454, 838]
private theorem transition2701Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2701Input0) = fromList transition2701Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2701 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0396 = 1 • support0321 := by
  have hs : support0396 = fromList transition2701Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2701Chunk0]
  have hn : (transition2701Raw0 : Multiset ℕ) = 1 • (supportNumbers0321 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0321] using hm

private def transition2702Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839, 897, 899, 901, 903, 960, 962, 964, 966]
private def transition2702Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 1, 3, 5, 7, 64, 66, 68, 70, 128, 130, 132, 134, 193, 195, 197, 199, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455, 256, 258, 260, 262, 321, 323, 325, 327, 385, 387, 389, 391, 448, 450, 452, 454]
private theorem transition2702Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2702Input0) = fromList transition2702Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2702 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0396 = 1 • support0320 := by
  have hs : support0396 = fromList transition2702Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2702Chunk0]
  have hn : (transition2702Raw0 : Multiset ℕ) = 1 • (supportNumbers0320 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0320] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
