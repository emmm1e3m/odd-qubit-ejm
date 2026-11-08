import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0649Input0 : List ℕ := [0, 1, 8, 9, 22, 23, 30, 31, 578, 579, 586, 587, 596, 597, 604, 605]
private def finish0649Raw0 : List ℕ := [0, 1, 8, 9, 22, 23, 30, 31, 66, 67, 74, 75, 84, 85, 92, 93]
private theorem finish0649Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0649Input0) = fromList finish0649Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0649 : finishSupport ⟨true, bits4 4⟩ support1675 = 1 • support1676 := by
  have hs : support1675 = fromList finish0649Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0649Chunk0]
  have hn : (finish0649Raw0 : Multiset ℕ) = 1 • (supportNumbers1676 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1676] using hm

private def finish0650Input0 : List ℕ := [0, 1, 22, 23, 130, 131, 148, 149]
private def finish0650Raw0 : List ℕ := [0, 1, 130, 131]
private theorem finish0650Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0650Input0) = fromList finish0650Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0650 : finishSupport ⟨false, bits4 4⟩ support1678 = 1 • support0857 := by
  have hs : support1678 = fromList finish0650Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0650Chunk0]
  have hn : (finish0650Raw0 : Multiset ℕ) = 1 • (supportNumbers0857 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0857] using hm

private def finish0651Input0 : List ℕ := [0, 1, 22, 23, 130, 131, 148, 149, 578, 579, 596, 597, 704, 705, 726, 727]
private def finish0651Raw0 : List ℕ := [0, 1, 22, 23, 130, 131, 148, 149, 66, 67, 84, 85, 192, 193, 214, 215]
private theorem finish0651Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0651Input0) = fromList finish0651Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0651 : finishSupport ⟨true, bits4 4⟩ support1679 = 1 • support1680 := by
  have hs : support1679 = fromList finish0651Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0651Chunk0]
  have hn : (finish0651Raw0 : Multiset ℕ) = 1 • (supportNumbers1680 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1680] using hm

private def finish0652Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 316, 317, 318, 319, 424, 425, 426, 427]
private def finish0652Raw0 : List ℕ := [0, 1, 2, 3, 60, 61, 62, 63]
private theorem finish0652Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0652Input0) = fromList finish0652Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0652 : finishSupport ⟨false, bits4 4⟩ support1683 = 1 • support0571 := by
  have hs : support1683 = fromList finish0652Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0652Chunk0]
  have hn : (finish0652Raw0 : Multiset ℕ) = 1 • (supportNumbers0571 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0571] using hm

private def finish0653Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 316, 317, 318, 319, 424, 425, 426, 427, 576, 577, 578, 579, 724, 725, 726, 727, 892, 893, 894, 895, 1000, 1001, 1002, 1003]
private def finish0653Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 60, 61, 62, 63, 168, 169, 170, 171, 64, 65, 66, 67, 212, 213, 214, 215, 124, 125, 126, 127, 232, 233, 234, 235]
private theorem finish0653Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0653Input0) = fromList finish0653Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0653 : finishSupport ⟨true, bits4 4⟩ support1684 = 1 • support1685 := by
  have hs : support1684 = fromList finish0653Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0653Chunk0]
  have hn : (finish0653Raw0 : Multiset ℕ) = 1 • (supportNumbers1685 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1685] using hm

private def finish0654Input0 : List ℕ := [0, 4, 11, 15, 65, 69, 74, 78, 130, 134, 137, 141, 195, 199, 200, 204]
private def finish0654Raw0 : List ℕ := [0, 11, 65, 74, 130, 137, 195, 200]
private theorem finish0654Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0654Input0) = fromList finish0654Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0654 : finishSupport ⟨false, bits4 4⟩ support1690 = 1 • support1691 := by
  have hs : support1690 = fromList finish0654Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0654Chunk0]
  have hn : (finish0654Raw0 : Multiset ℕ) = 1 • (supportNumbers1691 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1691] using hm

private def finish0655Input0 : List ℕ := [0, 4, 11, 15, 65, 69, 74, 78, 130, 134, 137, 141, 195, 199, 200, 204, 515, 519, 520, 524, 578, 582, 585, 589, 641, 645, 650, 654, 704, 708, 715, 719]
private def finish0655Raw0 : List ℕ := [0, 4, 11, 15, 65, 69, 74, 78, 130, 134, 137, 141, 195, 199, 200, 204, 3, 7, 8, 12, 66, 70, 73, 77, 129, 133, 138, 142, 192, 196, 203, 207]
private theorem finish0655Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0655Input0) = fromList finish0655Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0655 : finishSupport ⟨true, bits4 4⟩ support1692 = 1 • support0613 := by
  have hs : support1692 = fromList finish0655Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0655Chunk0]
  have hn : (finish0655Raw0 : Multiset ℕ) = 1 • (supportNumbers0613 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0613] using hm

private def finish0656Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 297, 299, 301, 303, 360, 362, 364, 366, 425, 427, 429, 431, 488, 490, 492, 494]
private def finish0656Raw0 : List ℕ := [0, 2, 65, 67, 128, 130, 193, 195, 45, 47, 108, 110, 173, 175, 236, 238]
private theorem finish0656Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0656Input0) = fromList finish0656Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0656 : finishSupport ⟨false, bits4 4⟩ support1696 = 1 • support1697 := by
  have hs : support1696 = fromList finish0656Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0656Chunk0]
  have hn : (finish0656Raw0 : Multiset ℕ) = 1 • (supportNumbers1697 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1697] using hm

private def finish0657Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 297, 299, 301, 303, 360, 362, 364, 366, 425, 427, 429, 431, 488, 490, 492, 494, 513, 515, 517, 519, 576, 578, 580, 582, 641, 643, 645, 647, 704, 706, 708, 710, 808, 810, 812, 814, 873, 875, 877, 879, 936, 938, 940, 942, 1001, 1003, 1005, 1007]
private def finish0657Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 41, 43, 45, 47, 104, 106, 108, 110, 169, 171, 173, 175, 232, 234, 236, 238, 1, 3, 5, 7, 64, 66, 68, 70, 129, 131, 133, 135, 192, 194, 196, 198, 40, 42, 44, 46, 105, 107, 109, 111, 168, 170, 172, 174, 233, 235, 237, 239]
private theorem finish0657Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0657Input0) = fromList finish0657Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0657 : finishSupport ⟨true, bits4 4⟩ support1698 = 1 • support0954 := by
  have hs : support1698 = fromList finish0657Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0657Chunk0]
  have hn : (finish0657Raw0 : Multiset ℕ) = 1 • (supportNumbers0954 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0954] using hm

private def finish0658Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 289, 291, 293, 295, 297, 299, 301, 303, 352, 354, 356, 358, 360, 362, 364, 366]
private def finish0658Raw0 : List ℕ := [0, 2, 8, 10, 65, 67, 73, 75, 37, 39, 45, 47, 100, 102, 108, 110]
private theorem finish0658Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0658Input0) = fromList finish0658Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0658 : finishSupport ⟨false, bits4 4⟩ support1700 = 1 • support1701 := by
  have hs : support1700 = fromList finish0658Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0658Chunk0]
  have hn : (finish0658Raw0 : Multiset ℕ) = 1 • (supportNumbers1701 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1701] using hm

private def finish0659Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 289, 291, 293, 295, 297, 299, 301, 303, 352, 354, 356, 358, 360, 362, 364, 366, 513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 800, 802, 804, 806, 808, 810, 812, 814, 865, 867, 869, 871, 873, 875, 877, 879]
private def finish0659Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 33, 35, 37, 39, 41, 43, 45, 47, 96, 98, 100, 102, 104, 106, 108, 110, 1, 3, 5, 7, 9, 11, 13, 15, 64, 66, 68, 70, 72, 74, 76, 78, 32, 34, 36, 38, 40, 42, 44, 46, 97, 99, 101, 103, 105, 107, 109, 111]
private theorem finish0659Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0659Input0) = fromList finish0659Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0659 : finishSupport ⟨true, bits4 4⟩ support1702 = 1 • support0938 := by
  have hs : support1702 = fromList finish0659Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0659Chunk0]
  have hn : (finish0659Raw0 : Multiset ℕ) = 1 • (supportNumbers0938 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0938] using hm

private def finish0660Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private def finish0660Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 136, 137, 138, 139, 200, 201, 202, 203]
private theorem finish0660Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0660Input0) = fromList finish0660Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0660 : finishSupport ⟨false, bits4 4⟩ support0088 = 1 • support1655 := by
  have hs : support0088 = fromList finish0660Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0660Chunk0]
  have hn : (finish0660Raw0 : Multiset ℕ) = 1 • (supportNumbers1655 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1655] using hm

private def finish0661Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 648, 649, 650, 651, 652, 653, 654, 655, 712, 713, 714, 715, 716, 717, 718, 719]
private def finish0661Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem finish0661Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0661Input0) = fromList finish0661Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0661 : finishSupport ⟨true, bits4 4⟩ support0408 = 2 • support0088 := by
  have hs : support0408 = fromList finish0661Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0661Chunk0]
  have hn : (finish0661Raw0 : Multiset ℕ) = 2 • (supportNumbers0088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0088] using hm

private def finish0662Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 289, 291, 293, 295, 352, 354, 356, 358, 416, 418, 420, 422, 481, 483, 485, 487]
private def finish0662Raw0 : List ℕ := [0, 2, 65, 67, 129, 131, 192, 194, 37, 39, 100, 102, 164, 166, 229, 231]
private theorem finish0662Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0662Input0) = fromList finish0662Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0662 : finishSupport ⟨false, bits4 4⟩ support1704 = 1 • support1705 := by
  have hs : support1704 = fromList finish0662Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0662Chunk0]
  have hn : (finish0662Raw0 : Multiset ℕ) = 1 • (supportNumbers1705 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1705] using hm

private def finish0663Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 289, 291, 293, 295, 352, 354, 356, 358, 416, 418, 420, 422, 481, 483, 485, 487, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 800, 802, 804, 806, 865, 867, 869, 871, 929, 931, 933, 935, 992, 994, 996, 998]
private def finish0663Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 33, 35, 37, 39, 96, 98, 100, 102, 160, 162, 164, 166, 225, 227, 229, 231, 1, 3, 5, 7, 64, 66, 68, 70, 128, 130, 132, 134, 193, 195, 197, 199, 32, 34, 36, 38, 97, 99, 101, 103, 161, 163, 165, 167, 224, 226, 228, 230]
private theorem finish0663Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0663Input0) = fromList finish0663Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0663 : finishSupport ⟨true, bits4 4⟩ support1706 = 1 • support0913 := by
  have hs : support1706 = fromList finish0663Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0663Chunk0]
  have hn : (finish0663Raw0 : Multiset ℕ) = 1 • (supportNumbers0913 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0913] using hm

private def finish0664Input0 : List ℕ := [0, 4, 11, 15, 65, 69, 74, 78, 129, 133, 138, 142, 192, 196, 203, 207]
private def finish0664Raw0 : List ℕ := [0, 11, 65, 74, 129, 138, 192, 203]
private theorem finish0664Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0664Input0) = fromList finish0664Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0664 : finishSupport ⟨false, bits4 4⟩ support1707 = 1 • support1708 := by
  have hs : support1707 = fromList finish0664Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0664Chunk0]
  have hn : (finish0664Raw0 : Multiset ℕ) = 1 • (supportNumbers1708 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1708] using hm

private def finish0665Input0 : List ℕ := [0, 4, 11, 15, 65, 69, 74, 78, 129, 133, 138, 142, 192, 196, 203, 207, 515, 519, 520, 524, 578, 582, 585, 589, 642, 646, 649, 653, 707, 711, 712, 716]
private def finish0665Raw0 : List ℕ := [0, 4, 11, 15, 65, 69, 74, 78, 129, 133, 138, 142, 192, 196, 203, 207, 3, 7, 8, 12, 66, 70, 73, 77, 130, 134, 137, 141, 195, 199, 200, 204]
private theorem finish0665Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0665Input0) = fromList finish0665Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0665 : finishSupport ⟨true, bits4 4⟩ support1709 = 1 • support0613 := by
  have hs : support1709 = fromList finish0665Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0665Chunk0]
  have hn : (finish0665Raw0 : Multiset ℕ) = 1 • (supportNumbers0613 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0613] using hm

private def finish0666Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 312, 313, 314, 315, 316, 317, 318, 319, 376, 377, 378, 379, 380, 381, 382, 383, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487]
private def finish0666Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 152, 153, 154, 155, 216, 217, 218, 219, 60, 61, 62, 63, 124, 125, 126, 127, 164, 165, 166, 167, 228, 229, 230, 231]
private theorem finish0666Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0666Input0) = fromList finish0666Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0666 : finishSupport ⟨false, bits4 4⟩ support1712 = 1 • support1713 := by
  have hs : support1712 = fromList finish0666Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0666Chunk0]
  have hn : (finish0666Raw0 : Multiset ℕ) = 1 • (supportNumbers1713 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1713] using hm

private def finish0667Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 312, 313, 314, 315, 316, 317, 318, 319, 376, 377, 378, 379, 380, 381, 382, 383, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487]
private def finish0667Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 56, 57, 58, 59, 60, 61, 62, 63, 120, 121, 122, 123, 124, 125, 126, 127, 160, 161, 162, 163, 164, 165, 166, 167, 224, 225, 226, 227, 228, 229, 230, 231]
private theorem finish0667Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0667Input0) = fromList finish0667Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0667Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735, 824, 825, 826, 827, 828, 829, 830, 831, 888, 889, 890, 891, 892, 893, 894, 895, 928, 929, 930, 931, 932, 933, 934, 935, 992, 993, 994, 995, 996, 997, 998, 999]
private def finish0667Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 56, 57, 58, 59, 60, 61, 62, 63, 120, 121, 122, 123, 124, 125, 126, 127, 160, 161, 162, 163, 164, 165, 166, 167, 224, 225, 226, 227, 228, 229, 230, 231]
private theorem finish0667Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0667Input1) = fromList finish0667Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0667 : finishSupport ⟨true, bits4 4⟩ support1714 = 2 • support1715 := by
  have hs : support1714 = fromList finish0667Input0 + fromList finish0667Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0667Chunk0, finish0667Chunk1]
  have hn : (finish0667Raw0 : Multiset ℕ) + (finish0667Raw1 : Multiset ℕ) = 2 • (supportNumbers1715 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1715] using hm

private def finish0668Input0 : List ℕ := [0, 1, 4, 5, 26, 27, 30, 31, 64, 65, 68, 69, 90, 91, 94, 95, 128, 129, 132, 133, 154, 155, 158, 159, 192, 193, 196, 197, 218, 219, 222, 223]
private def finish0668Raw0 : List ℕ := [0, 1, 26, 27, 64, 65, 90, 91, 128, 129, 154, 155, 192, 193, 218, 219]
private theorem finish0668Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0668Input0) = fromList finish0668Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0668 : finishSupport ⟨false, bits4 4⟩ support1716 = 1 • support1717 := by
  have hs : support1716 = fromList finish0668Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0668Chunk0]
  have hn : (finish0668Raw0 : Multiset ℕ) = 1 • (supportNumbers1717 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1717] using hm

private def finish0669Input0 : List ℕ := [0, 1, 4, 5, 26, 27, 30, 31, 64, 65, 68, 69, 90, 91, 94, 95, 128, 129, 132, 133, 154, 155, 158, 159, 192, 193, 196, 197, 218, 219, 222, 223, 514, 515, 518, 519, 536, 537, 540, 541, 578, 579, 582, 583, 600, 601, 604, 605, 642, 643, 646, 647, 664, 665, 668, 669, 706, 707, 710, 711, 728, 729, 732, 733]
private def finish0669Raw0 : List ℕ := [0, 1, 4, 5, 26, 27, 30, 31, 64, 65, 68, 69, 90, 91, 94, 95, 128, 129, 132, 133, 154, 155, 158, 159, 192, 193, 196, 197, 218, 219, 222, 223, 2, 3, 6, 7, 24, 25, 28, 29, 66, 67, 70, 71, 88, 89, 92, 93, 130, 131, 134, 135, 152, 153, 156, 157, 194, 195, 198, 199, 216, 217, 220, 221]
private theorem finish0669Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0669Input0) = fromList finish0669Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0669 : finishSupport ⟨true, bits4 4⟩ support1718 = 1 • support0326 := by
  have hs : support1718 = fromList finish0669Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0669Chunk0]
  have hn : (finish0669Raw0 : Multiset ℕ) = 1 • (supportNumbers0326 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0326] using hm

private def finish0670Input0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 18, 19, 22, 23, 26, 27, 30, 31, 64, 65, 68, 69, 72, 73, 76, 77, 82, 83, 86, 87, 90, 91, 94, 95]
private def finish0670Raw0 : List ℕ := [0, 1, 8, 9, 18, 19, 26, 27, 64, 65, 72, 73, 82, 83, 90, 91]
private theorem finish0670Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0670Input0) = fromList finish0670Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0670 : finishSupport ⟨false, bits4 4⟩ support1721 = 1 • support1722 := by
  have hs : support1721 = fromList finish0670Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0670Chunk0]
  have hn : (finish0670Raw0 : Multiset ℕ) = 1 • (supportNumbers1722 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1722] using hm

private def finish0671Input0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 18, 19, 22, 23, 26, 27, 30, 31, 64, 65, 68, 69, 72, 73, 76, 77, 82, 83, 86, 87, 90, 91, 94, 95, 514, 515, 518, 519, 522, 523, 526, 527, 528, 529, 532, 533, 536, 537, 540, 541, 578, 579, 582, 583, 586, 587, 590, 591, 592, 593, 596, 597, 600, 601, 604, 605]
private def finish0671Raw0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 18, 19, 22, 23, 26, 27, 30, 31, 64, 65, 68, 69, 72, 73, 76, 77, 82, 83, 86, 87, 90, 91, 94, 95, 2, 3, 6, 7, 10, 11, 14, 15, 16, 17, 20, 21, 24, 25, 28, 29, 66, 67, 70, 71, 74, 75, 78, 79, 80, 81, 84, 85, 88, 89, 92, 93]
private theorem finish0671Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0671Input0) = fromList finish0671Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0671 : finishSupport ⟨true, bits4 4⟩ support1723 = 1 • support0246 := by
  have hs : support1723 = fromList finish0671Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0671Chunk0]
  have hn : (finish0671Raw0 : Multiset ℕ) = 1 • (supportNumbers0246 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0246] using hm

private def finish0672Input0 : List ℕ := [0, 1, 4, 5, 18, 19, 22, 23, 64, 65, 68, 69, 82, 83, 86, 87, 130, 131, 134, 135, 144, 145, 148, 149, 194, 195, 198, 199, 208, 209, 212, 213]
private def finish0672Raw0 : List ℕ := [0, 1, 18, 19, 64, 65, 82, 83, 130, 131, 144, 145, 194, 195, 208, 209]
private theorem finish0672Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0672Input0) = fromList finish0672Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0672 : finishSupport ⟨false, bits4 4⟩ support1725 = 1 • support1726 := by
  have hs : support1725 = fromList finish0672Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0672Chunk0]
  have hn : (finish0672Raw0 : Multiset ℕ) = 1 • (supportNumbers1726 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1726] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
