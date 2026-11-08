import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2977Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 680, 681, 682, 683, 684, 685, 686, 687, 744, 745, 746, 747, 748, 749, 750, 751]
private def transition2977Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 136, 712, 137, 713, 138, 714, 139, 715, 140, 716, 141, 717, 142, 718, 143, 719, 200, 648, 201, 649, 202, 650, 203, 651, 204, 652, 205, 653, 206, 654, 207, 655, 288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 428, 1004, 429, 1005, 430, 1006, 431, 1007, 488, 936, 489, 937, 490, 938, 491, 939, 492, 940, 493, 941, 494, 942, 495, 943]
private theorem transition2977Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2977Input0) = fromList transition2977Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2977 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1762 = 1 • support0749 := by
  have hs : support1762 = fromList transition2977Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2977Chunk0]
  have hn : (transition2977Raw0 : Multiset ℕ) = 1 • (supportNumbers0749 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0749] using hm

private def transition2978Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 512, 514, 516, 518, 577, 579, 581, 583, 641, 643, 645, 647, 704, 706, 708, 710]
private def transition2978Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 256, 258, 260, 262, 321, 323, 325, 327, 385, 387, 389, 391, 448, 450, 452, 454]
private theorem transition2978Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2978Input0) = fromList transition2978Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2978 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0443 = 1 • support0467 := by
  have hs : support0443 = fromList transition2978Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2978Chunk0]
  have hn : (transition2978Raw0 : Multiset ℕ) = 1 • (supportNumbers0467 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0467] using hm

private def transition2979Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 512, 514, 516, 518, 577, 579, 581, 583, 641, 643, 645, 647, 704, 706, 708, 710]
private def transition2979Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 129, 513, 131, 515, 133, 517, 135, 519, 192, 576, 194, 578, 196, 580, 198, 582, 256, 896, 258, 898, 260, 900, 262, 902, 321, 961, 323, 963, 325, 965, 327, 967, 385, 769, 387, 771, 389, 773, 391, 775, 448, 832, 450, 834, 452, 836, 454, 838]
private theorem transition2979Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2979Input0) = fromList transition2979Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2979 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0443 = 1 • support0468 := by
  have hs : support0443 = fromList transition2979Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2979Chunk0]
  have hn : (transition2979Raw0 : Multiset ℕ) = 1 • (supportNumbers0468 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0468] using hm

private def transition2980Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 512, 514, 516, 518, 577, 579, 581, 583, 641, 643, 645, 647, 704, 706, 708, 710]
private def transition2980Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 256, 258, 260, 262, 321, 323, 325, 327, 385, 387, 389, 391, 448, 450, 452, 454]
private theorem transition2980Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2980Input0) = fromList transition2980Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2980 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0443 = 1 • support0467 := by
  have hs : support0443 = fromList transition2980Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2980Chunk0]
  have hn : (transition2980Raw0 : Multiset ℕ) = 1 • (supportNumbers0467 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0467] using hm

private def transition2981Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 256, 258, 260, 262, 321, 323, 325, 327, 385, 387, 389, 391, 448, 450, 452, 454]
private def transition2981Raw0 : List ℕ := [0, 4, 65, 69, 129, 133, 192, 196, 2, 6, 67, 71, 131, 135, 194, 198]
private theorem transition2981Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2981Input0) = fromList transition2981Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2981 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0467 = 1 • support0144 := by
  have hs : support0467 = fromList transition2981Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2981Chunk0]
  have hn : (transition2981Raw0 : Multiset ℕ) = 1 • (supportNumbers0144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0144] using hm

private def transition2982Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 256, 258, 260, 262, 321, 323, 325, 327, 385, 387, 389, 391, 448, 450, 452, 454]
private def transition2982Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 129, 707, 133, 711, 192, 642, 196, 646, 576, 2, 580, 6, 513, 67, 517, 71, 705, 131, 709, 135, 640, 194, 644, 198]
private theorem transition2982Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2982Input0) = fromList transition2982Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2982 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0467 = 1 • support0314 := by
  have hs : support0467 = fromList transition2982Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2982Chunk0]
  have hn : (transition2982Raw0 : Multiset ℕ) = 1 • (supportNumbers0314 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0314] using hm

private def transition2983Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 512, 514, 516, 518, 577, 579, 581, 583, 641, 643, 645, 647, 704, 706, 708, 710]
private def transition2983Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 129, 673, 131, 675, 133, 677, 135, 679, 192, 736, 194, 738, 196, 740, 198, 742, 256, 800, 258, 802, 260, 804, 262, 806, 321, 865, 323, 867, 325, 869, 327, 871, 385, 929, 387, 931, 389, 933, 391, 935, 448, 992, 450, 994, 452, 996, 454, 998]
private theorem transition2983Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2983Input0) = fromList transition2983Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2983 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0443 = 1 • support1763 := by
  have hs : support0443 = fromList transition2983Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2983Chunk0]
  have hn : (transition2983Raw0 : Multiset ℕ) = 1 • (supportNumbers1763 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1763] using hm

private def transition2984Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 256, 258, 260, 262, 321, 323, 325, 327, 385, 387, 389, 391, 448, 450, 452, 454, 544, 546, 548, 550, 609, 611, 613, 615, 673, 675, 677, 679, 736, 738, 740, 742, 800, 802, 804, 806, 865, 867, 869, 871, 929, 931, 933, 935, 992, 994, 996, 998]
private def transition2984Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 288, 290, 292, 294, 353, 355, 357, 359, 417, 419, 421, 423, 480, 482, 484, 486, 288, 290, 292, 294, 353, 355, 357, 359, 417, 419, 421, 423, 480, 482, 484, 486]
private theorem transition2984Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2984Input0) = fromList transition2984Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2984 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1763 = 2 • support1408 := by
  have hs : support1763 = fromList transition2984Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2984Chunk0]
  have hn : (transition2984Raw0 : Multiset ℕ) = 2 • (supportNumbers1408 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1408] using hm

private def transition2985Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 256, 258, 260, 262, 321, 323, 325, 327, 385, 387, 389, 391, 448, 450, 452, 454, 544, 546, 548, 550, 609, 611, 613, 615, 673, 675, 677, 679, 736, 738, 740, 742, 800, 802, 804, 806, 865, 867, 869, 871, 929, 931, 933, 935, 992, 994, 996, 998]
private def transition2985Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 129, 705, 131, 707, 133, 709, 135, 711, 192, 640, 194, 642, 196, 644, 198, 646, 0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 129, 705, 131, 707, 133, 709, 135, 711, 192, 640, 194, 642, 196, 644, 198, 646, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 417, 993, 419, 995, 421, 997, 423, 999, 480, 928, 482, 930, 484, 932, 486, 934, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 417, 993, 419, 995, 421, 997, 423, 999, 480, 928, 482, 930, 484, 932, 486, 934]
private theorem transition2985Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2985Input0) = fromList transition2985Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2985 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1763 = 2 • support1410 := by
  have hs : support1763 = fromList transition2985Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2985Chunk0]
  have hn : (transition2985Raw0 : Multiset ℕ) = 2 • (supportNumbers1410 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1410] using hm

private def transition2986Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 265, 267, 269, 271, 328, 330, 332, 334, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2986Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 9, 11, 13, 15, 72, 74, 76, 78, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition2986Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2986Input0) = fromList transition2986Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2986 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0444 = 1 • support0082 := by
  have hs : support0444 = fromList transition2986Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2986Chunk0]
  have hn : (transition2986Raw0 : Multiset ℕ) = 1 • (supportNumbers0082 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0082] using hm

private def transition2987Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 265, 267, 269, 271, 328, 330, 332, 334, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2987Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 9, 11, 13, 15, 72, 74, 76, 78, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition2987Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2987Input0) = fromList transition2987Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2987 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0444 = 1 • support0082 := by
  have hs : support0444 = fromList transition2987Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2987Chunk0]
  have hn : (transition2987Raw0 : Multiset ℕ) = 1 • (supportNumbers0082 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0082] using hm

private def transition2988Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 265, 267, 269, 271, 328, 330, 332, 334, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2988Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 9, 11, 13, 15, 72, 74, 76, 78, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition2988Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2988Input0) = fromList transition2988Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2988 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0444 = 1 • support0082 := by
  have hs : support0444 = fromList transition2988Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2988Chunk0]
  have hn : (transition2988Raw0 : Multiset ℕ) = 1 • (supportNumbers0082 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0082] using hm

private def transition2989Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 265, 267, 269, 271, 328, 330, 332, 334, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2989Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 9, 11, 13, 15, 72, 74, 76, 78, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition2989Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2989Input0) = fromList transition2989Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2989 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0444 = 1 • support0082 := by
  have hs : support0444 = fromList transition2989Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2989Chunk0]
  have hn : (transition2989Raw0 : Multiset ℕ) = 1 • (supportNumbers0082 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0082] using hm

private def transition2990Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private def transition2990Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private theorem transition2990Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2990Input0) = fromList transition2990Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2990 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0082 = 1 • support0082 := by
  have hs : support0082 = fromList transition2990Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2990Chunk0]
  have hn : (transition2990Raw0 : Multiset ℕ) = 1 • (supportNumbers0082 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0082] using hm

private def transition2991Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private def transition2991Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 129, 705, 131, 707, 133, 709, 135, 711, 136, 712, 138, 714, 140, 716, 142, 718, 192, 640, 194, 642, 196, 644, 198, 646, 201, 649, 203, 651, 205, 653, 207, 655]
private theorem transition2991Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2991Input0) = fromList transition2991Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2991 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0082 = 1 • support0226 := by
  have hs : support0082 = fromList transition2991Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2991Chunk0]
  have hn : (transition2991Raw0 : Multiset ℕ) = 1 • (supportNumbers0226 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0226] using hm

private def transition2992Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 265, 267, 269, 271, 328, 330, 332, 334, 392, 394, 396, 398, 457, 459, 461, 463, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition2992Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 9, 11, 13, 15, 72, 74, 76, 78, 136, 138, 140, 142, 201, 203, 205, 207, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455, 264, 266, 268, 270, 329, 331, 333, 335, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition2992Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2992Input0) = fromList transition2992Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2992 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0445 = 1 • support0227 := by
  have hs : support0445 = fromList transition2992Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2992Chunk0]
  have hn : (transition2992Raw0 : Multiset ℕ) = 1 • (supportNumbers0227 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0227] using hm

private def transition2993Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 265, 267, 269, 271, 328, 330, 332, 334, 392, 394, 396, 398, 457, 459, 461, 463, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition2993Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 129, 513, 131, 515, 133, 517, 135, 519, 192, 576, 194, 578, 196, 580, 198, 582, 9, 649, 11, 651, 13, 653, 15, 655, 72, 712, 74, 714, 76, 716, 78, 718, 136, 520, 138, 522, 140, 524, 142, 526, 201, 585, 203, 587, 205, 589, 207, 591, 257, 897, 259, 899, 261, 901, 263, 903, 320, 960, 322, 962, 324, 964, 326, 966, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 264, 904, 266, 906, 268, 908, 270, 910, 329, 969, 331, 971, 333, 973, 335, 975, 393, 777, 395, 779, 397, 781, 399, 783, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition2993Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2993Input0) = fromList transition2993Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2993 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0445 = 1 • support0228 := by
  have hs : support0445 = fromList transition2993Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2993Chunk0]
  have hn : (transition2993Raw0 : Multiset ℕ) = 1 • (supportNumbers0228 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0228] using hm

private def transition2994Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 265, 267, 269, 271, 328, 330, 332, 334, 392, 394, 396, 398, 457, 459, 461, 463, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition2994Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 9, 11, 13, 15, 72, 74, 76, 78, 136, 138, 140, 142, 201, 203, 205, 207, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455, 264, 266, 268, 270, 329, 331, 333, 335, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition2994Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2994Input0) = fromList transition2994Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2994 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0445 = 1 • support0227 := by
  have hs : support0445 = fromList transition2994Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2994Chunk0]
  have hn : (transition2994Raw0 : Multiset ℕ) = 1 • (supportNumbers0227 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0227] using hm

private def transition2995Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 265, 267, 269, 271, 328, 330, 332, 334, 392, 394, 396, 398, 457, 459, 461, 463, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition2995Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 129, 673, 131, 675, 133, 677, 135, 679, 192, 736, 194, 738, 196, 740, 198, 742, 9, 553, 11, 555, 13, 557, 15, 559, 72, 616, 74, 618, 76, 620, 78, 622, 136, 680, 138, 682, 140, 684, 142, 686, 201, 745, 203, 747, 205, 749, 207, 751, 257, 801, 259, 803, 261, 805, 263, 807, 320, 864, 322, 866, 324, 868, 326, 870, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 264, 808, 266, 810, 268, 812, 270, 814, 329, 873, 331, 875, 333, 877, 335, 879, 393, 937, 395, 939, 397, 941, 399, 943, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition2995Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2995Input0) = fromList transition2995Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2995 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0445 = 1 • support1192 := by
  have hs : support0445 = fromList transition2995Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2995Chunk0]
  have hn : (transition2995Raw0 : Multiset ℕ) = 1 • (supportNumbers1192 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1192] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
