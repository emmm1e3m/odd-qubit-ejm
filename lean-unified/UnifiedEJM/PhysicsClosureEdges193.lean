import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0086Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def finish0086Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27, 64, 65, 66, 67, 72, 73, 74, 75, 80, 81, 82, 83, 88, 89, 90, 91]
private theorem finish0086Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0086Input0) = fromList finish0086Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0086Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0086Raw1 : List ℕ := [128, 129, 130, 131, 136, 137, 138, 139, 144, 145, 146, 147, 152, 153, 154, 155, 192, 193, 194, 195, 200, 201, 202, 203, 208, 209, 210, 211, 216, 217, 218, 219]
private theorem finish0086Chunk1 : finishSupport ⟨false, bits4 4⟩ (fromList finish0086Input1) = fromList finish0086Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0086 : finishSupport ⟨false, bits4 4⟩ support0096 = 1 • support0642 := by
  have hs : support0096 = fromList finish0086Input0 + fromList finish0086Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0086Chunk0, finish0086Chunk1]
  have hn : (finish0086Raw0 : Multiset ℕ) + (finish0086Raw1 : Multiset ℕ) = 1 • (supportNumbers0642 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0642] using hm

private def finish0087Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def finish0087Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem finish0087Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0087Input0) = fromList finish0087Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0087Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0087Raw1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem finish0087Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0087Input1) = fromList finish0087Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0087Input2 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]
private def finish0087Raw2 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem finish0087Chunk2 : finishSupport ⟨true, bits4 4⟩ (fromList finish0087Input2) = fromList finish0087Raw2 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0087Input3 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]
private def finish0087Raw3 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem finish0087Chunk3 : finishSupport ⟨true, bits4 4⟩ (fromList finish0087Input3) = fromList finish0087Raw3 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0087 : finishSupport ⟨true, bits4 4⟩ support0097 = 2 • support0096 := by
  have hs : support0097 = fromList finish0087Input0 + fromList finish0087Input1 + fromList finish0087Input2 + fromList finish0087Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0087Chunk0, finish0087Chunk1, finish0087Chunk2, finish0087Chunk3]
  have hn : (finish0087Raw0 : Multiset ℕ) + (finish0087Raw1 : Multiset ℕ) + (finish0087Raw2 : Multiset ℕ) + (finish0087Raw3 : Multiset ℕ) = 2 • (supportNumbers0096 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0096] using hm

private def finish0088Input0 : List ℕ := [0, 2, 288, 290]
private def finish0088Raw0 : List ℕ := [0, 2]
private theorem finish0088Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0088Input0) = fromList finish0088Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0088 : finishSupport ⟨false, bits4 4⟩ support0645 = 1 • support0008 := by
  have hs : support0645 = fromList finish0088Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0088Chunk0]
  have hn : (finish0088Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def finish0089Input0 : List ℕ := [0, 2, 288, 290, 576, 578, 864, 866]
private def finish0089Raw0 : List ℕ := [0, 2, 32, 34, 64, 66, 96, 98]
private theorem finish0089Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0089Input0) = fromList finish0089Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0089 : finishSupport ⟨true, bits4 4⟩ support0646 = 1 • support0647 := by
  have hs : support0646 = fromList finish0089Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0089Chunk0]
  have hn : (finish0089Raw0 : Multiset ℕ) = 1 • (supportNumbers0647 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0647] using hm

private def finish0090Input0 : List ℕ := [0, 136]
private def finish0090Raw0 : List ℕ := [0, 136]
private theorem finish0090Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0090Input0) = fromList finish0090Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0090 : finishSupport ⟨false, bits4 4⟩ support0648 = 1 • support0648 := by
  have hs : support0648 = fromList finish0090Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0090Chunk0]
  have hn : (finish0090Raw0 : Multiset ℕ) = 1 • (supportNumbers0648 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0648] using hm

private def finish0091Input0 : List ℕ := [0, 136, 578, 714]
private def finish0091Raw0 : List ℕ := [0, 136, 66, 202]
private theorem finish0091Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0091Input0) = fromList finish0091Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0091 : finishSupport ⟨true, bits4 4⟩ support0649 = 1 • support0650 := by
  have hs : support0649 = fromList finish0091Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0091Chunk0]
  have hn : (finish0091Raw0 : Multiset ℕ) = 1 • (supportNumbers0650 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0650] using hm

private def finish0092Input0 : List ℕ := [0, 2, 136, 138]
private def finish0092Raw0 : List ℕ := [0, 2, 136, 138]
private theorem finish0092Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0092Input0) = fromList finish0092Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0092 : finishSupport ⟨false, bits4 4⟩ support0053 = 1 • support0053 := by
  have hs : support0053 = fromList finish0092Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0092Chunk0]
  have hn : (finish0092Raw0 : Multiset ℕ) = 1 • (supportNumbers0053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0053] using hm

private def finish0093Input0 : List ℕ := [0, 2, 136, 138, 576, 578, 712, 714]
private def finish0093Raw0 : List ℕ := [0, 2, 136, 138, 64, 66, 200, 202]
private theorem finish0093Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0093Input0) = fromList finish0093Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0093 : finishSupport ⟨true, bits4 4⟩ support0651 = 1 • support0652 := by
  have hs : support0651 = fromList finish0093Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0093Chunk0]
  have hn : (finish0093Raw0 : Multiset ℕ) = 1 • (supportNumbers0652 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0652] using hm

private def finish0094Input0 : List ℕ := [0, 10, 130, 136]
private def finish0094Raw0 : List ℕ := [0, 10, 130, 136]
private theorem finish0094Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0094Input0) = fromList finish0094Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0094 : finishSupport ⟨false, bits4 4⟩ support0653 = 1 • support0653 := by
  have hs : support0653 = fromList finish0094Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0094Chunk0]
  have hn : (finish0094Raw0 : Multiset ℕ) = 1 • (supportNumbers0653 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0653] using hm

private def finish0095Input0 : List ℕ := [0, 10, 130, 136, 578, 584, 704, 714]
private def finish0095Raw0 : List ℕ := [0, 10, 130, 136, 66, 72, 192, 202]
private theorem finish0095Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0095Input0) = fromList finish0095Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0095 : finishSupport ⟨true, bits4 4⟩ support0654 = 1 • support0655 := by
  have hs : support0654 = fromList finish0095Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0095Chunk0]
  have hn : (finish0095Raw0 : Multiset ℕ) = 1 • (supportNumbers0655 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0655] using hm

private def finish0096Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 288, 290, 296, 298, 416, 418, 424, 426]
private def finish0096Raw0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138]
private theorem finish0096Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0096Input0) = fromList finish0096Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0096 : finishSupport ⟨false, bits4 4⟩ support0657 = 1 • support0173 := by
  have hs : support0657 = fromList finish0096Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0096Chunk0]
  have hn : (finish0096Raw0 : Multiset ℕ) = 1 • (supportNumbers0173 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0173] using hm

private def finish0097Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 288, 290, 296, 298, 416, 418, 424, 426, 576, 578, 584, 586, 704, 706, 712, 714, 864, 866, 872, 874, 992, 994, 1000, 1002]
private def finish0097Raw0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 32, 34, 40, 42, 160, 162, 168, 170, 64, 66, 72, 74, 192, 194, 200, 202, 96, 98, 104, 106, 224, 226, 232, 234]
private theorem finish0097Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0097Input0) = fromList finish0097Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0097 : finishSupport ⟨true, bits4 4⟩ support0658 = 1 • support0659 := by
  have hs : support0658 = fromList finish0097Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0097Chunk0]
  have hn : (finish0097Raw0 : Multiset ℕ) = 1 • (supportNumbers0659 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0659] using hm

private def finish0098Input0 : List ℕ := [0, 2, 425, 427]
private def finish0098Raw0 : List ℕ := [0, 2]
private theorem finish0098Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0098Input0) = fromList finish0098Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0098 : finishSupport ⟨false, bits4 4⟩ support0661 = 1 • support0008 := by
  have hs : support0661 = fromList finish0098Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0098Chunk0]
  have hn : (finish0098Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def finish0099Input0 : List ℕ := [0, 2, 425, 427, 576, 578, 1001, 1003]
private def finish0099Raw0 : List ℕ := [0, 2, 169, 171, 64, 66, 233, 235]
private theorem finish0099Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0099Input0) = fromList finish0099Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0099 : finishSupport ⟨true, bits4 4⟩ support0662 = 1 • support0663 := by
  have hs : support0662 = fromList finish0099Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0099Chunk0]
  have hn : (finish0099Raw0 : Multiset ℕ) = 1 • (supportNumbers0663 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0663] using hm

private def finish0100Input0 : List ℕ := [0, 3, 137, 138]
private def finish0100Raw0 : List ℕ := [0, 3, 137, 138]
private theorem finish0100Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0100Input0) = fromList finish0100Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0100 : finishSupport ⟨false, bits4 4⟩ support0664 = 1 • support0664 := by
  have hs : support0664 = fromList finish0100Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0100Chunk0]
  have hn : (finish0100Raw0 : Multiset ℕ) = 1 • (supportNumbers0664 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0664] using hm

private def finish0101Input0 : List ℕ := [0, 3, 137, 138, 577, 578, 712, 715]
private def finish0101Raw0 : List ℕ := [0, 3, 137, 138, 65, 66, 200, 203]
private theorem finish0101Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0101Input0) = fromList finish0101Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0101 : finishSupport ⟨true, bits4 4⟩ support0665 = 1 • support0666 := by
  have hs : support0665 = fromList finish0101Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0101Chunk0]
  have hn : (finish0101Raw0 : Multiset ℕ) = 1 • (supportNumbers0666 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0666] using hm

private def finish0102Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 288, 289, 290, 291, 424, 425, 426, 427]
private def finish0102Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private theorem finish0102Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0102Input0) = fromList finish0102Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0102 : finishSupport ⟨false, bits4 4⟩ support0668 = 1 • support0065 := by
  have hs : support0668 = fromList finish0102Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0102Chunk0]
  have hn : (finish0102Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def finish0103Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 288, 289, 290, 291, 424, 425, 426, 427, 576, 577, 578, 579, 712, 713, 714, 715, 864, 865, 866, 867, 1000, 1001, 1002, 1003]
private def finish0103Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 32, 33, 34, 35, 168, 169, 170, 171, 64, 65, 66, 67, 200, 201, 202, 203, 96, 97, 98, 99, 232, 233, 234, 235]
private theorem finish0103Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0103Input0) = fromList finish0103Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0103 : finishSupport ⟨true, bits4 4⟩ support0669 = 1 • support0670 := by
  have hs : support0669 = fromList finish0103Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0103Chunk0]
  have hn : (finish0103Raw0 : Multiset ℕ) = 1 • (supportNumbers0670 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0670] using hm

private def finish0104Input0 : List ℕ := [0, 9, 129, 136]
private def finish0104Raw0 : List ℕ := [0, 9, 129, 136]
private theorem finish0104Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0104Input0) = fromList finish0104Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0104 : finishSupport ⟨false, bits4 4⟩ support0671 = 1 • support0671 := by
  have hs : support0671 = fromList finish0104Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0104Chunk0]
  have hn : (finish0104Raw0 : Multiset ℕ) = 1 • (supportNumbers0671 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0671] using hm

private def finish0105Input0 : List ℕ := [0, 9, 129, 136, 578, 587, 707, 714]
private def finish0105Raw0 : List ℕ := [0, 9, 129, 136, 66, 75, 195, 202]
private theorem finish0105Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0105Input0) = fromList finish0105Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0105 : finishSupport ⟨true, bits4 4⟩ support0672 = 1 • support0673 := by
  have hs : support0672 = fromList finish0105Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0105Chunk0]
  have hn : (finish0105Raw0 : Multiset ℕ) = 1 • (supportNumbers0673 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0673] using hm

private def finish0106Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 289, 291, 296, 298, 416, 418, 425, 427]
private def finish0106Raw0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138]
private theorem finish0106Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0106Input0) = fromList finish0106Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0106 : finishSupport ⟨false, bits4 4⟩ support0675 = 1 • support0059 := by
  have hs : support0675 = fromList finish0106Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0106Chunk0]
  have hn : (finish0106Raw0 : Multiset ℕ) = 1 • (supportNumbers0059 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0059] using hm

private def finish0107Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 289, 291, 296, 298, 416, 418, 425, 427, 576, 578, 585, 587, 705, 707, 712, 714, 865, 867, 872, 874, 992, 994, 1001, 1003]
private def finish0107Raw0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 33, 35, 40, 42, 160, 162, 169, 171, 64, 66, 73, 75, 193, 195, 200, 202, 97, 99, 104, 106, 224, 226, 233, 235]
private theorem finish0107Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0107Input0) = fromList finish0107Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0107 : finishSupport ⟨true, bits4 4⟩ support0676 = 1 • support0677 := by
  have hs : support0676 = fromList finish0107Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0107Chunk0]
  have hn : (finish0107Raw0 : Multiset ℕ) = 1 • (supportNumbers0677 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0677] using hm

private def finish0108Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private def finish0108Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private theorem finish0108Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0108Input0) = fromList finish0108Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0108 : finishSupport ⟨false, bits4 4⟩ support0114 = 1 • support0114 := by
  have hs : support0114 = fromList finish0108Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0108Chunk0]
  have hn : (finish0108Raw0 : Multiset ℕ) = 1 • (supportNumbers0114 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0114] using hm

private def finish0109Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 576, 577, 578, 579, 584, 585, 586, 587, 704, 705, 706, 707, 712, 713, 714, 715]
private def finish0109Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 64, 65, 66, 67, 72, 73, 74, 75, 192, 193, 194, 195, 200, 201, 202, 203]
private theorem finish0109Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0109Input0) = fromList finish0109Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0109 : finishSupport ⟨true, bits4 4⟩ support0678 = 1 • support0679 := by
  have hs : support0678 = fromList finish0109Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0109Chunk0]
  have hn : (finish0109Raw0 : Multiset ℕ) = 1 • (supportNumbers0679 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0679] using hm

private def finish0110Input0 : List ℕ := [0, 1, 2, 3]
private def finish0110Raw0 : List ℕ := [0, 1, 2, 3]
private theorem finish0110Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0110Input0) = fromList finish0110Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0110 : finishSupport ⟨false, bits4 4⟩ support0030 = 1 • support0030 := by
  have hs : support0030 = fromList finish0110Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0110Chunk0]
  have hn : (finish0110Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def finish0111Input0 : List ℕ := [0, 1, 2, 3, 576, 577, 578, 579]
private def finish0111Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67]
private theorem finish0111Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0111Input0) = fromList finish0111Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0111 : finishSupport ⟨true, bits4 4⟩ support0681 = 1 • support0682 := by
  have hs : support0681 = fromList finish0111Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0111Chunk0]
  have hn : (finish0111Raw0 : Multiset ℕ) = 1 • (supportNumbers0682 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0682] using hm

private def finish0112Input0 : List ℕ := [0, 1, 158, 159]
private def finish0112Raw0 : List ℕ := [0, 1]
private theorem finish0112Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0112Input0) = fromList finish0112Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0112 : finishSupport ⟨false, bits4 4⟩ support0683 = 1 • support0493 := by
  have hs : support0683 = fromList finish0112Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0112Chunk0]
  have hn : (finish0112Raw0 : Multiset ℕ) = 1 • (supportNumbers0493 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0493] using hm

private def finish0113Input0 : List ℕ := [0, 1, 158, 159, 578, 579, 732, 733]
private def finish0113Raw0 : List ℕ := [0, 1, 158, 159, 66, 67, 220, 221]
private theorem finish0113Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0113Input0) = fromList finish0113Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0113 : finishSupport ⟨true, bits4 4⟩ support0684 = 1 • support0685 := by
  have hs : support0684 = fromList finish0113Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0113Chunk0]
  have hn : (finish0113Raw0 : Multiset ℕ) = 1 • (supportNumbers0685 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0685] using hm

private def finish0114Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 288, 289, 290, 291, 444, 445, 446, 447]
private def finish0114Raw0 : List ℕ := [0, 1, 2, 3, 188, 189, 190, 191]
private theorem finish0114Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0114Input0) = fromList finish0114Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0114 : finishSupport ⟨false, bits4 4⟩ support0687 = 1 • support0688 := by
  have hs : support0687 = fromList finish0114Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0114Chunk0]
  have hn : (finish0114Raw0 : Multiset ℕ) = 1 • (supportNumbers0688 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0688] using hm

private def finish0115Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 288, 289, 290, 291, 444, 445, 446, 447, 576, 577, 578, 579, 732, 733, 734, 735, 864, 865, 866, 867, 1020, 1021, 1022, 1023]
private def finish0115Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 32, 33, 34, 35, 188, 189, 190, 191, 64, 65, 66, 67, 220, 221, 222, 223, 96, 97, 98, 99, 252, 253, 254, 255]
private theorem finish0115Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0115Input0) = fromList finish0115Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0115 : finishSupport ⟨true, bits4 4⟩ support0689 = 1 • support0690 := by
  have hs : support0689 = fromList finish0115Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0115Chunk0]
  have hn : (finish0115Raw0 : Multiset ℕ) = 1 • (supportNumbers0690 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0690] using hm

private def finish0116Input0 : List ℕ := [0, 1, 136, 137]
private def finish0116Raw0 : List ℕ := [0, 1, 136, 137]
private theorem finish0116Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0116Input0) = fromList finish0116Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0116 : finishSupport ⟨false, bits4 4⟩ support0584 = 1 • support0584 := by
  have hs : support0584 = fromList finish0116Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0116Chunk0]
  have hn : (finish0116Raw0 : Multiset ℕ) = 1 • (supportNumbers0584 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0584] using hm

private def finish0117Input0 : List ℕ := [0, 1, 136, 137, 578, 579, 714, 715]
private def finish0117Raw0 : List ℕ := [0, 1, 136, 137, 66, 67, 202, 203]
private theorem finish0117Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0117Input0) = fromList finish0117Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0117 : finishSupport ⟨true, bits4 4⟩ support0691 = 1 • support0692 := by
  have hs : support0691 = fromList finish0117Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0117Chunk0]
  have hn : (finish0117Raw0 : Multiset ℕ) = 1 • (supportNumbers0692 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0692] using hm

private def finish0118Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 316, 317, 318, 319, 436, 437, 438, 439]
private def finish0118Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 60, 61, 62, 63, 180, 181, 182, 183]
private theorem finish0118Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0118Input0) = fromList finish0118Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0118 : finishSupport ⟨false, bits4 4⟩ support0694 = 1 • support0580 := by
  have hs : support0694 = fromList finish0118Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0118Chunk0]
  have hn : (finish0118Raw0 : Multiset ℕ) = 1 • (supportNumbers0580 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0580] using hm

private def finish0119Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 316, 317, 318, 319, 436, 437, 438, 439, 576, 577, 578, 579, 712, 713, 714, 715, 892, 893, 894, 895, 1012, 1013, 1014, 1015]
private def finish0119Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 60, 61, 62, 63, 180, 181, 182, 183, 64, 65, 66, 67, 200, 201, 202, 203, 124, 125, 126, 127, 244, 245, 246, 247]
private theorem finish0119Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0119Input0) = fromList finish0119Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0119 : finishSupport ⟨true, bits4 4⟩ support0695 = 1 • support0696 := by
  have hs : support0695 = fromList finish0119Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0119Chunk0]
  have hn : (finish0119Raw0 : Multiset ℕ) = 1 • (supportNumbers0696 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0696] using hm

private def finish0120Input0 : List ℕ := [0, 1, 10, 11, 22, 23, 28, 29, 130, 131, 136, 137, 148, 149, 158, 159]
private def finish0120Raw0 : List ℕ := [0, 1, 10, 11, 130, 131, 136, 137]
private theorem finish0120Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0120Input0) = fromList finish0120Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0120 : finishSupport ⟨false, bits4 4⟩ support0697 = 1 • support0698 := by
  have hs : support0697 = fromList finish0120Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0120Chunk0]
  have hn : (finish0120Raw0 : Multiset ℕ) = 1 • (supportNumbers0698 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0698] using hm

private def finish0121Input0 : List ℕ := [0, 1, 10, 11, 22, 23, 28, 29, 130, 131, 136, 137, 148, 149, 158, 159, 578, 579, 584, 585, 596, 597, 606, 607, 704, 705, 714, 715, 726, 727, 732, 733]
private def finish0121Raw0 : List ℕ := [0, 1, 10, 11, 22, 23, 28, 29, 130, 131, 136, 137, 148, 149, 158, 159, 66, 67, 72, 73, 84, 85, 94, 95, 192, 193, 202, 203, 214, 215, 220, 221]
private theorem finish0121Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0121Input0) = fromList finish0121Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0121 : finishSupport ⟨true, bits4 4⟩ support0699 = 1 • support0700 := by
  have hs : support0699 = fromList finish0121Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0121Chunk0]
  have hn : (finish0121Raw0 : Multiset ℕ) = 1 • (supportNumbers0700 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0700] using hm

private def finish0122Input0 : List ℕ := [0, 1, 20, 21]
private def finish0122Raw0 : List ℕ := [0, 1]
private theorem finish0122Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0122Input0) = fromList finish0122Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0122 : finishSupport ⟨false, bits4 4⟩ support0702 = 1 • support0493 := by
  have hs : support0702 = fromList finish0122Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0122Chunk0]
  have hn : (finish0122Raw0 : Multiset ℕ) = 1 • (supportNumbers0493 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0493] using hm

private def finish0123Input0 : List ℕ := [0, 1, 20, 21, 578, 579, 598, 599]
private def finish0123Raw0 : List ℕ := [0, 1, 20, 21, 66, 67, 86, 87]
private theorem finish0123Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0123Input0) = fromList finish0123Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0123 : finishSupport ⟨true, bits4 4⟩ support0703 = 1 • support0704 := by
  have hs : support0703 = fromList finish0123Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0123Chunk0]
  have hn : (finish0123Raw0 : Multiset ℕ) = 1 • (supportNumbers0704 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0704] using hm

private def finish0124Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 424, 425, 426, 427, 444, 445, 446, 447]
private def finish0124Raw0 : List ℕ := [0, 1, 2, 3, 188, 189, 190, 191]
private theorem finish0124Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0124Input0) = fromList finish0124Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0124 : finishSupport ⟨false, bits4 4⟩ support0706 = 1 • support0688 := by
  have hs : support0706 = fromList finish0124Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0124Chunk0]
  have hn : (finish0124Raw0 : Multiset ℕ) = 1 • (supportNumbers0688 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0688] using hm

private def finish0125Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 424, 425, 426, 427, 444, 445, 446, 447, 576, 577, 578, 579, 596, 597, 598, 599, 1000, 1001, 1002, 1003, 1020, 1021, 1022, 1023]
private def finish0125Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 168, 169, 170, 171, 188, 189, 190, 191, 64, 65, 66, 67, 84, 85, 86, 87, 232, 233, 234, 235, 252, 253, 254, 255]
private theorem finish0125Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0125Input0) = fromList finish0125Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0125 : finishSupport ⟨true, bits4 4⟩ support0707 = 1 • support0708 := by
  have hs : support0707 = fromList finish0125Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0125Chunk0]
  have hn : (finish0125Raw0 : Multiset ℕ) = 1 • (supportNumbers0708 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0708] using hm

private def finish0126Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private def finish0126Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private theorem finish0126Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0126Input0) = fromList finish0126Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0126 : finishSupport ⟨false, bits4 4⟩ support0034 = 1 • support0065 := by
  have hs : support0034 = fromList finish0126Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0126Chunk0]
  have hn : (finish0126Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def finish0127Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 576, 577, 578, 579, 596, 597, 598, 599, 712, 713, 714, 715, 732, 733, 734, 735]
private def finish0127Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 64, 65, 66, 67, 84, 85, 86, 87, 200, 201, 202, 203, 220, 221, 222, 223]
private theorem finish0127Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0127Input0) = fromList finish0127Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0127 : finishSupport ⟨true, bits4 4⟩ support0709 = 1 • support0710 := by
  have hs : support0709 = fromList finish0127Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0127Chunk0]
  have hn : (finish0127Raw0 : Multiset ℕ) = 1 • (supportNumbers0710 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0710] using hm

private def finish0128Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 288, 289, 290, 291, 308, 309, 310, 311, 424, 425, 426, 427, 444, 445, 446, 447]
private def finish0128Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 52, 53, 54, 55, 188, 189, 190, 191]
private theorem finish0128Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0128Input0) = fromList finish0128Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0128 : finishSupport ⟨false, bits4 4⟩ support0712 = 1 • support0713 := by
  have hs : support0712 = fromList finish0128Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0128Chunk0]
  have hn : (finish0128Raw0 : Multiset ℕ) = 1 • (supportNumbers0713 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0713] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
