import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2703Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839, 897, 899, 901, 903, 960, 962, 964, 966]
private def transition2703Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 129, 673, 131, 675, 133, 677, 135, 679, 192, 736, 194, 738, 196, 740, 198, 742, 1, 545, 3, 547, 5, 549, 7, 551, 64, 608, 66, 610, 68, 612, 70, 614, 128, 672, 130, 674, 132, 676, 134, 678, 193, 737, 195, 739, 197, 741, 199, 743, 257, 801, 259, 803, 261, 805, 263, 807, 320, 864, 322, 866, 324, 868, 326, 870, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 256, 800, 258, 802, 260, 804, 262, 806, 321, 865, 323, 867, 325, 869, 327, 871, 385, 929, 387, 931, 389, 933, 391, 935, 448, 992, 450, 994, 452, 996, 454, 998]
private theorem transition2703Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2703Input0) = fromList transition2703Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2703 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0396 = 1 • support1427 := by
  have hs : support0396 = fromList transition2703Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2703Chunk0]
  have hn : (transition2703Raw0 : Multiset ℕ) = 1 • (supportNumbers1427 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1427] using hm

private def transition2704Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 521, 523, 525, 527, 584, 586, 588, 590, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition2704Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 265, 267, 269, 271, 328, 330, 332, 334, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition2704Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2704Input0) = fromList transition2704Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2704 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0397 = 1 • support0444 := by
  have hs : support0397 = fromList transition2704Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2704Chunk0]
  have hn : (transition2704Raw0 : Multiset ℕ) = 1 • (supportNumbers0444 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0444] using hm

private def transition2705Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 521, 523, 525, 527, 584, 586, 588, 590, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition2705Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 129, 513, 131, 515, 133, 517, 135, 519, 192, 576, 194, 578, 196, 580, 198, 582, 265, 905, 267, 907, 269, 909, 271, 911, 328, 968, 330, 970, 332, 972, 334, 974, 392, 776, 394, 778, 396, 780, 398, 782, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition2705Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2705Input0) = fromList transition2705Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2705 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0397 = 1 • support0445 := by
  have hs : support0397 = fromList transition2705Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2705Chunk0]
  have hn : (transition2705Raw0 : Multiset ℕ) = 1 • (supportNumbers0445 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0445] using hm

private def transition2706Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 521, 523, 525, 527, 584, 586, 588, 590, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition2706Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 265, 267, 269, 271, 328, 330, 332, 334, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition2706Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2706Input0) = fromList transition2706Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2706 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0397 = 1 • support0444 := by
  have hs : support0397 = fromList transition2706Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2706Chunk0]
  have hn : (transition2706Raw0 : Multiset ℕ) = 1 • (supportNumbers0444 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0444] using hm

private def transition2707Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 265, 267, 269, 271, 328, 330, 332, 334, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2707Raw0 : List ℕ := [0, 4, 65, 69, 129, 133, 192, 196, 11, 15, 74, 78, 138, 142, 203, 207]
private theorem transition2707Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2707Input0) = fromList transition2707Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2707 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0444 = 1 • support1707 := by
  have hs : support0444 = fromList transition2707Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2707Chunk0]
  have hn : (transition2707Raw0 : Multiset ℕ) = 1 • (supportNumbers1707 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1707] using hm

private def transition2708Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 265, 267, 269, 271, 328, 330, 332, 334, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2708Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 129, 707, 133, 711, 192, 642, 196, 646, 585, 11, 589, 15, 520, 74, 524, 78, 712, 138, 716, 142, 649, 203, 653, 207]
private theorem transition2708Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2708Input0) = fromList transition2708Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2708 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0444 = 1 • support1709 := by
  have hs : support0444 = fromList transition2708Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2708Chunk0]
  have hn : (transition2708Raw0 : Multiset ℕ) = 1 • (supportNumbers1709 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1709] using hm

private def transition2709Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 521, 523, 525, 527, 584, 586, 588, 590, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition2709Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 129, 673, 131, 675, 133, 677, 135, 679, 192, 736, 194, 738, 196, 740, 198, 742, 265, 809, 267, 811, 269, 813, 271, 815, 328, 872, 330, 874, 332, 876, 334, 878, 392, 936, 394, 938, 396, 940, 398, 942, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition2709Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2709Input0) = fromList transition2709Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2709 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0397 = 1 • support1710 := by
  have hs : support0397 = fromList transition2709Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2709Chunk0]
  have hn : (transition2709Raw0 : Multiset ℕ) = 1 • (supportNumbers1710 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1710] using hm

private def transition2710Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 265, 267, 269, 271, 328, 330, 332, 334, 392, 394, 396, 398, 457, 459, 461, 463, 544, 546, 548, 550, 609, 611, 613, 615, 673, 675, 677, 679, 736, 738, 740, 742, 809, 811, 813, 815, 872, 874, 876, 878, 936, 938, 940, 942, 1001, 1003, 1005, 1007]
private def transition2710Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 9, 11, 13, 15, 72, 74, 76, 78, 136, 138, 140, 142, 201, 203, 205, 207, 288, 290, 292, 294, 353, 355, 357, 359, 417, 419, 421, 423, 480, 482, 484, 486, 297, 299, 301, 303, 360, 362, 364, 366, 424, 426, 428, 430, 489, 491, 493, 495]
private theorem transition2710Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2710Input0) = fromList transition2710Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2710 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1710 = 1 • support0957 := by
  have hs : support1710 = fromList transition2710Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2710Chunk0]
  have hn : (transition2710Raw0 : Multiset ℕ) = 1 • (supportNumbers0957 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0957] using hm

private def transition2711Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 265, 267, 269, 271, 328, 330, 332, 334, 392, 394, 396, 398, 457, 459, 461, 463, 544, 546, 548, 550, 609, 611, 613, 615, 673, 675, 677, 679, 736, 738, 740, 742, 809, 811, 813, 815, 872, 874, 876, 878, 936, 938, 940, 942, 1001, 1003, 1005, 1007]
private def transition2711Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 129, 705, 131, 707, 133, 709, 135, 711, 192, 640, 194, 642, 196, 644, 198, 646, 9, 585, 11, 587, 13, 589, 15, 591, 72, 520, 74, 522, 76, 524, 78, 526, 136, 712, 138, 714, 140, 716, 142, 718, 201, 649, 203, 651, 205, 653, 207, 655, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 417, 993, 419, 995, 421, 997, 423, 999, 480, 928, 482, 930, 484, 932, 486, 934, 297, 873, 299, 875, 301, 877, 303, 879, 360, 808, 362, 810, 364, 812, 366, 814, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition2711Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2711Input0) = fromList transition2711Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2711 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1710 = 1 • support0959 := by
  have hs : support1710 = fromList transition2711Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2711Chunk0]
  have hn : (transition2711Raw0 : Multiset ℕ) = 1 • (supportNumbers0959 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0959] using hm

private def transition2712Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719]
private def transition2712Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private theorem transition2712Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2712Input0) = fromList transition2712Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2712 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0398 = 1 • support0042 := by
  have hs : support0398 = fromList transition2712Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2712Chunk0]
  have hn : (transition2712Raw0 : Multiset ℕ) = 1 • (supportNumbers0042 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0042] using hm

private def transition2713Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719]
private def transition2713Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 129, 513, 131, 515, 133, 517, 135, 519, 137, 521, 139, 523, 141, 525, 143, 527, 192, 576, 194, 578, 196, 580, 198, 582, 200, 584, 202, 586, 204, 588, 206, 590, 257, 897, 259, 899, 261, 901, 263, 903, 265, 905, 267, 907, 269, 909, 271, 911, 320, 960, 322, 962, 324, 964, 326, 966, 328, 968, 330, 970, 332, 972, 334, 974, 384, 768, 386, 770, 388, 772, 390, 774, 392, 776, 394, 778, 396, 780, 398, 782, 449, 833, 451, 835, 453, 837, 455, 839, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition2713Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2713Input0) = fromList transition2713Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2713 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0398 = 1 • support0043 := by
  have hs : support0398 = fromList transition2713Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2713Chunk0]
  have hn : (transition2713Raw0 : Multiset ℕ) = 1 • (supportNumbers0043 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0043] using hm

private def transition2714Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719]
private def transition2714Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private theorem transition2714Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2714Input0) = fromList transition2714Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2714 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0398 = 1 • support0042 := by
  have hs : support0398 = fromList transition2714Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2714Chunk0]
  have hn : (transition2714Raw0 : Multiset ℕ) = 1 • (supportNumbers0042 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0042] using hm

private def transition2715Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719]
private def transition2715Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623, 129, 673, 131, 675, 133, 677, 135, 679, 137, 681, 139, 683, 141, 685, 143, 687, 192, 736, 194, 738, 196, 740, 198, 742, 200, 744, 202, 746, 204, 748, 206, 750, 257, 801, 259, 803, 261, 805, 263, 807, 265, 809, 267, 811, 269, 813, 271, 815, 320, 864, 322, 866, 324, 868, 326, 870, 328, 872, 330, 874, 332, 876, 334, 878, 384, 928, 386, 930, 388, 932, 390, 934, 392, 936, 394, 938, 396, 940, 398, 942, 449, 993, 451, 995, 453, 997, 455, 999, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition2715Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2715Input0) = fromList transition2715Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2715 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0398 = 1 • support0615 := by
  have hs : support0398 = fromList transition2715Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2715Chunk0]
  have hn : (transition2715Raw0 : Multiset ℕ) = 1 • (supportNumbers0615 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0615] using hm

private def transition2716Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition2716Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 8, 10, 12, 14, 73, 75, 77, 79, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition2716Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2716Input0) = fromList transition2716Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2716 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0399 = 1 • support0315 := by
  have hs : support0399 = fromList transition2716Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2716Chunk0]
  have hn : (transition2716Raw0 : Multiset ℕ) = 1 • (supportNumbers0315 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0315] using hm

private def transition2717Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition2717Raw0 : List ℕ := [0, 2, 4, 6, 648, 650, 652, 654, 65, 67, 69, 71, 713, 715, 717, 719, 129, 131, 133, 135, 521, 523, 525, 527, 192, 194, 196, 198, 584, 586, 588, 590, 640, 642, 644, 646, 8, 10, 12, 14, 705, 707, 709, 711, 73, 75, 77, 79, 513, 515, 517, 519, 137, 139, 141, 143, 576, 578, 580, 582, 200, 202, 204, 206]
private theorem transition2717Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2717Input0) = fromList transition2717Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2717 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0399 = 1 • support0398 := by
  have hs : support0399 = fromList transition2717Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2717Chunk0]
  have hn : (transition2717Raw0 : Multiset ℕ) = 1 • (supportNumbers0398 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0398] using hm

private def transition2718Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition2718Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 8, 10, 12, 14, 73, 75, 77, 79, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition2718Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2718Input0) = fromList transition2718Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2718 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0399 = 1 • support0315 := by
  have hs : support0399 = fromList transition2718Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2718Chunk0]
  have hn : (transition2718Raw0 : Multiset ℕ) = 1 • (supportNumbers0315 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0315] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
