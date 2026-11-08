import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0313Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 392, 394, 396, 398, 457, 459, 461, 463, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847]
private def transition0313Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 136, 520, 138, 522, 140, 524, 142, 526, 201, 585, 203, 587, 205, 589, 207, 591, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 264, 904, 266, 906, 268, 908, 270, 910, 329, 969, 331, 971, 333, 973, 335, 975]
private theorem transition0313Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0313Input0) = fromList transition0313Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0313 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0039 = 1 • support0078 := by
  have hs : support0039 = fromList transition0313Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0313Chunk0]
  have hn : (transition0313Raw0 : Multiset ℕ) = 1 • (supportNumbers0078 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0078] using hm

private def transition0314Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 392, 394, 396, 398, 457, 459, 461, 463, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847]
private def transition0314Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 384, 386, 388, 390, 449, 451, 453, 455, 264, 266, 268, 270, 329, 331, 333, 335]
private theorem transition0314Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0314Input0) = fromList transition0314Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0314 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0039 = 1 • support0077 := by
  have hs : support0039 = fromList transition0314Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0314Chunk0]
  have hn : (transition0314Raw0 : Multiset ℕ) = 1 • (supportNumbers0077 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0077] using hm

private def transition0315Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition0315Raw0 : List ℕ := [0, 4, 65, 69, 136, 140, 201, 205, 10, 14, 75, 79, 130, 134, 195, 199]
private theorem transition0315Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0315Input0) = fromList transition0315Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0315 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0077 = 1 • support0732 := by
  have hs : support0077 = fromList transition0315Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0315Chunk0]
  have hn : (transition0315Raw0 : Multiset ℕ) = 1 • (supportNumbers0732 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0732] using hm

private def transition0316Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition0316Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 136, 714, 140, 718, 201, 651, 205, 655, 584, 10, 588, 14, 521, 75, 525, 79, 704, 130, 708, 134, 641, 195, 645, 199]
private theorem transition0316Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0316Input0) = fromList transition0316Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0316 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0077 = 1 • support0734 := by
  have hs : support0077 = fromList transition0316Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0316Chunk0]
  have hn : (transition0316Raw0 : Multiset ℕ) = 1 • (supportNumbers0734 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0734] using hm

private def transition0317Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 392, 394, 396, 398, 457, 459, 461, 463, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847]
private def transition0317Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 136, 680, 138, 682, 140, 684, 142, 686, 201, 745, 203, 747, 205, 749, 207, 751, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 264, 808, 266, 810, 268, 812, 270, 814, 329, 873, 331, 875, 333, 877, 335, 879]
private theorem transition0317Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0317Input0) = fromList transition0317Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0317 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0039 = 1 • support0736 := by
  have hs : support0039 = fromList transition0317Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0317Chunk0]
  have hn : (transition0317Raw0 : Multiset ℕ) = 1 • (supportNumbers0736 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0736] using hm

private def transition0318Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455, 544, 546, 548, 550, 609, 611, 613, 615, 680, 682, 684, 686, 745, 747, 749, 751, 808, 810, 812, 814, 873, 875, 877, 879, 928, 930, 932, 934, 993, 995, 997, 999]
private def transition0318Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 8, 10, 12, 14, 73, 75, 77, 79, 128, 130, 132, 134, 193, 195, 197, 199, 288, 290, 292, 294, 353, 355, 357, 359, 424, 426, 428, 430, 489, 491, 493, 495, 296, 298, 300, 302, 361, 363, 365, 367, 416, 418, 420, 422, 481, 483, 485, 487]
private theorem transition0318Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0318Input0) = fromList transition0318Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0318 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0736 = 1 • support0737 := by
  have hs : support0736 = fromList transition0318Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0318Chunk0]
  have hn : (transition0318Raw0 : Multiset ℕ) = 1 • (supportNumbers0737 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0737] using hm

private def transition0319Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455, 544, 546, 548, 550, 609, 611, 613, 615, 680, 682, 684, 686, 745, 747, 749, 751, 808, 810, 812, 814, 873, 875, 877, 879, 928, 930, 932, 934, 993, 995, 997, 999]
private def transition0319Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 136, 712, 138, 714, 140, 716, 142, 718, 201, 649, 203, 651, 205, 653, 207, 655, 8, 584, 10, 586, 12, 588, 14, 590, 73, 521, 75, 523, 77, 525, 79, 527, 128, 704, 130, 706, 132, 708, 134, 710, 193, 641, 195, 643, 197, 645, 199, 647, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 489, 937, 491, 939, 493, 941, 495, 943, 296, 872, 298, 874, 300, 876, 302, 878, 361, 809, 363, 811, 365, 813, 367, 815, 416, 992, 418, 994, 420, 996, 422, 998, 481, 929, 483, 931, 485, 933, 487, 935]
private theorem transition0319Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0319Input0) = fromList transition0319Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0319 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0736 = 1 • support0739 := by
  have hs : support0736 = fromList transition0319Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0319Chunk0]
  have hn : (transition0319Raw0 : Multiset ℕ) = 1 • (supportNumbers0739 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0739] using hm

private def transition0320Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private def transition0320Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition0320Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0320Input0) = fromList transition0320Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0320 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0040 = 1 • support0016 := by
  have hs : support0040 = fromList transition0320Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0320Chunk0]
  have hn : (transition0320Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition0321Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private def transition0321Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 521, 523, 525, 527, 584, 586, 588, 590]
private theorem transition0321Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0321Input0) = fromList transition0321Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0321 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0040 = 1 • support0079 := by
  have hs : support0040 = fromList transition0321Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0321Chunk0]
  have hn : (transition0321Raw0 : Multiset ℕ) = 1 • (supportNumbers0079 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0079] using hm

private def transition0322Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private def transition0322Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition0322Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0322Input0) = fromList transition0322Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0322 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0040 = 1 • support0016 := by
  have hs : support0040 = fromList transition0322Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0322Chunk0]
  have hn : (transition0322Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition0323Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private def transition0323Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 681, 683, 685, 687, 744, 746, 748, 750]
private theorem transition0323Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0323Input0) = fromList transition0323Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0323 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0040 = 1 • support0740 := by
  have hs : support0040 = fromList transition0323Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0323Chunk0]
  have hn : (transition0323Raw0 : Multiset ℕ) = 1 • (supportNumbers0740 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0740] using hm

private def transition0324Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 681, 683, 685, 687, 744, 746, 748, 750]
private def transition0324Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 425, 427, 429, 431, 488, 490, 492, 494]
private theorem transition0324Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0324Input0) = fromList transition0324Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0324 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0740 = 1 • support0741 := by
  have hs : support0740 = fromList transition0324Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0324Chunk0]
  have hn : (transition0324Raw0 : Multiset ℕ) = 1 • (supportNumbers0741 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0741] using hm

private def transition0325Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 681, 683, 685, 687, 744, 746, 748, 750]
private def transition0325Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition0325Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0325Input0) = fromList transition0325Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0325 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0740 = 1 • support0743 := by
  have hs : support0740 = fromList transition0325Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0325Chunk0]
  have hn : (transition0325Raw0 : Multiset ℕ) = 1 • (supportNumbers0743 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0743] using hm

private def transition0326Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 513, 515, 517, 519, 576, 578, 580, 582, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition0326Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 257, 259, 261, 263, 320, 322, 324, 326, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition0326Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0326Input0) = fromList transition0326Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0326 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0041 = 1 • support0080 := by
  have hs : support0041 = fromList transition0326Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0326Chunk0]
  have hn : (transition0326Raw0 : Multiset ℕ) = 1 • (supportNumbers0080 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0080] using hm

private def transition0327Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 513, 515, 517, 519, 576, 578, 580, 582, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition0327Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 137, 521, 139, 523, 141, 525, 143, 527, 200, 584, 202, 586, 204, 588, 206, 590, 257, 897, 259, 899, 261, 901, 263, 903, 320, 960, 322, 962, 324, 964, 326, 966, 392, 776, 394, 778, 396, 780, 398, 782, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition0327Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0327Input0) = fromList transition0327Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0327 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0041 = 1 • support0081 := by
  have hs : support0041 = fromList transition0327Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0327Chunk0]
  have hn : (transition0327Raw0 : Multiset ℕ) = 1 • (supportNumbers0081 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0081] using hm

private def transition0328Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 513, 515, 517, 519, 576, 578, 580, 582, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition0328Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 257, 259, 261, 263, 320, 322, 324, 326, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition0328Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0328Input0) = fromList transition0328Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0328 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0041 = 1 • support0080 := by
  have hs : support0041 = fromList transition0328Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0328Chunk0]
  have hn : (transition0328Raw0 : Multiset ℕ) = 1 • (supportNumbers0080 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0080] using hm

private def transition0329Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 257, 259, 261, 263, 320, 322, 324, 326, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition0329Raw0 : List ℕ := [0, 4, 65, 69, 137, 141, 200, 204, 3, 7, 66, 70, 138, 142, 203, 207]
private theorem transition0329Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0329Input0) = fromList transition0329Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0329 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0080 = 1 • support0599 := by
  have hs : support0080 = fromList transition0329Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0329Chunk0]
  have hn : (transition0329Raw0 : Multiset ℕ) = 1 • (supportNumbers0599 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0599] using hm

private def transition0330Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 257, 259, 261, 263, 320, 322, 324, 326, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition0330Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 137, 715, 141, 719, 200, 650, 204, 654, 577, 3, 581, 7, 512, 66, 516, 70, 712, 138, 716, 142, 649, 203, 653, 207]
private theorem transition0330Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0330Input0) = fromList transition0330Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0330 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0080 = 1 • support0745 := by
  have hs : support0080 = fromList transition0330Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0330Chunk0]
  have hn : (transition0330Raw0 : Multiset ℕ) = 1 • (supportNumbers0745 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0745] using hm

private def transition0331Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 513, 515, 517, 519, 576, 578, 580, 582, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition0331Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 137, 681, 139, 683, 141, 685, 143, 687, 200, 744, 202, 746, 204, 748, 206, 750, 257, 801, 259, 803, 261, 805, 263, 807, 320, 864, 322, 866, 324, 868, 326, 870, 392, 936, 394, 938, 396, 940, 398, 942, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition0331Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0331Input0) = fromList transition0331Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0331 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0041 = 1 • support0746 := by
  have hs : support0041 = fromList transition0331Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0331Chunk0]
  have hn : (transition0331Raw0 : Multiset ℕ) = 1 • (supportNumbers0746 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0746] using hm

private def transition0332Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 257, 259, 261, 263, 320, 322, 324, 326, 392, 394, 396, 398, 457, 459, 461, 463, 544, 546, 548, 550, 609, 611, 613, 615, 681, 683, 685, 687, 744, 746, 748, 750, 801, 803, 805, 807, 864, 866, 868, 870, 936, 938, 940, 942, 1001, 1003, 1005, 1007]
private def transition0332Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 1, 3, 5, 7, 64, 66, 68, 70, 136, 138, 140, 142, 201, 203, 205, 207, 288, 290, 292, 294, 353, 355, 357, 359, 425, 427, 429, 431, 488, 490, 492, 494, 289, 291, 293, 295, 352, 354, 356, 358, 424, 426, 428, 430, 489, 491, 493, 495]
private theorem transition0332Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0332Input0) = fromList transition0332Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0332 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0746 = 1 • support0747 := by
  have hs : support0746 = fromList transition0332Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0332Chunk0]
  have hn : (transition0332Raw0 : Multiset ℕ) = 1 • (supportNumbers0747 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0747] using hm

private def transition0333Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 257, 259, 261, 263, 320, 322, 324, 326, 392, 394, 396, 398, 457, 459, 461, 463, 544, 546, 548, 550, 609, 611, 613, 615, 681, 683, 685, 687, 744, 746, 748, 750, 801, 803, 805, 807, 864, 866, 868, 870, 936, 938, 940, 942, 1001, 1003, 1005, 1007]
private def transition0333Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 137, 713, 139, 715, 141, 717, 143, 719, 200, 648, 202, 650, 204, 652, 206, 654, 1, 577, 3, 579, 5, 581, 7, 583, 64, 512, 66, 514, 68, 516, 70, 518, 136, 712, 138, 714, 140, 716, 142, 718, 201, 649, 203, 651, 205, 653, 207, 655, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 488, 936, 490, 938, 492, 940, 494, 942, 289, 865, 291, 867, 293, 869, 295, 871, 352, 800, 354, 802, 356, 804, 358, 806, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition0333Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0333Input0) = fromList transition0333Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0333 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0746 = 1 • support0749 := by
  have hs : support0746 = fromList transition0333Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0333Chunk0]
  have hn : (transition0333Raw0 : Multiset ℕ) = 1 • (supportNumbers0749 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0749] using hm

private def transition0334Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition0334Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 9, 11, 13, 15, 72, 74, 76, 78, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition0334Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0334Input0) = fromList transition0334Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0334 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0042 = 1 • support0082 := by
  have hs : support0042 = fromList transition0334Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0334Chunk0]
  have hn : (transition0334Raw0 : Multiset ℕ) = 1 • (supportNumbers0082 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0082] using hm

private def transition0335Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition0335Raw0 : List ℕ := [0, 2, 4, 6, 648, 650, 652, 654, 65, 67, 69, 71, 713, 715, 717, 719, 129, 131, 133, 135, 521, 523, 525, 527, 192, 194, 196, 198, 584, 586, 588, 590, 641, 643, 645, 647, 9, 11, 13, 15, 704, 706, 708, 710, 72, 74, 76, 78, 512, 514, 516, 518, 136, 138, 140, 142, 577, 579, 581, 583, 201, 203, 205, 207]
private theorem transition0335Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0335Input0) = fromList transition0335Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0335 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0042 = 1 • support0083 := by
  have hs : support0042 = fromList transition0335Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0335Chunk0]
  have hn : (transition0335Raw0 : Multiset ℕ) = 1 • (supportNumbers0083 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0083] using hm

private def transition0336Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition0336Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 9, 11, 13, 15, 72, 74, 76, 78, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition0336Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0336Input0) = fromList transition0336Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0336 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0042 = 1 • support0082 := by
  have hs : support0042 = fromList transition0336Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0336Chunk0]
  have hn : (transition0336Raw0 : Multiset ℕ) = 1 • (supportNumbers0082 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0082] using hm

private def transition0337Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private def transition0337Raw0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 129, 133, 136, 140, 192, 196, 201, 205]
private theorem transition0337Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0337Input0) = fromList transition0337Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0337 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0082 = 1 • support0750 := by
  have hs : support0082 = fromList transition0337Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0337Chunk0]
  have hn : (transition0337Raw0 : Multiset ℕ) = 1 • (supportNumbers0750 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0750] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
