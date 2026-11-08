import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0529Input0 : List ℕ := [0, 1, 4, 5, 26, 27, 30, 31, 64, 65, 68, 69, 90, 91, 94, 95, 514, 515, 518, 519, 536, 537, 540, 541, 578, 579, 582, 583, 600, 601, 604, 605]
private def finish0529Raw0 : List ℕ := [0, 1, 4, 5, 26, 27, 30, 31, 64, 65, 68, 69, 90, 91, 94, 95, 2, 3, 6, 7, 24, 25, 28, 29, 66, 67, 70, 71, 88, 89, 92, 93]
private theorem finish0529Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0529Input0) = fromList finish0529Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0529 : finishSupport ⟨true, bits4 4⟩ support1430 = 1 • support0020 := by
  have hs : support1430 = fromList finish0529Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0529Chunk0]
  have hn : (finish0529Raw0 : Multiset ℕ) = 1 • (supportNumbers0020 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0020] using hm

private def finish0530Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 288, 289, 290, 291, 292, 293, 294, 295, 312, 313, 314, 315, 316, 317, 318, 319, 352, 353, 354, 355, 356, 357, 358, 359, 376, 377, 378, 379, 380, 381, 382, 383]
private def finish0530Raw0 : List ℕ := [0, 1, 2, 3, 24, 25, 26, 27, 64, 65, 66, 67, 88, 89, 90, 91, 36, 37, 38, 39, 60, 61, 62, 63, 100, 101, 102, 103, 124, 125, 126, 127]
private theorem finish0530Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0530Input0) = fromList finish0530Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0530 : finishSupport ⟨false, bits4 4⟩ support1432 = 1 • support1433 := by
  have hs : support1432 = fromList finish0530Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0530Chunk0]
  have hn : (finish0530Raw0 : Multiset ℕ) = 1 • (supportNumbers1433 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1433] using hm

private def finish0531Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 288, 289, 290, 291, 292, 293, 294, 295, 312, 313, 314, 315, 316, 317, 318, 319, 352, 353, 354, 355, 356, 357, 358, 359, 376, 377, 378, 379, 380, 381, 382, 383]
private def finish0531Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 32, 33, 34, 35, 36, 37, 38, 39, 56, 57, 58, 59, 60, 61, 62, 63, 96, 97, 98, 99, 100, 101, 102, 103, 120, 121, 122, 123, 124, 125, 126, 127]
private theorem finish0531Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0531Input0) = fromList finish0531Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0531Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 800, 801, 802, 803, 804, 805, 806, 807, 824, 825, 826, 827, 828, 829, 830, 831, 864, 865, 866, 867, 868, 869, 870, 871, 888, 889, 890, 891, 892, 893, 894, 895]
private def finish0531Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 32, 33, 34, 35, 36, 37, 38, 39, 56, 57, 58, 59, 60, 61, 62, 63, 96, 97, 98, 99, 100, 101, 102, 103, 120, 121, 122, 123, 124, 125, 126, 127]
private theorem finish0531Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0531Input1) = fromList finish0531Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0531 : finishSupport ⟨true, bits4 4⟩ support1434 = 2 • support1435 := by
  have hs : support1434 = fromList finish0531Input0 + fromList finish0531Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0531Chunk0, finish0531Chunk1]
  have hn : (finish0531Raw0 : Multiset ℕ) + (finish0531Raw1 : Multiset ℕ) = 2 • (supportNumbers1435 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1435] using hm

private def finish0532Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95]
private def finish0532Raw0 : List ℕ := [0, 1, 2, 3, 24, 25, 26, 27, 64, 65, 66, 67, 88, 89, 90, 91]
private theorem finish0532Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0532Input0) = fromList finish0532Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0532 : finishSupport ⟨false, bits4 4⟩ support0020 = 1 • support1436 := by
  have hs : support0020 = fromList finish0532Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0532Chunk0]
  have hn : (finish0532Raw0 : Multiset ℕ) = 1 • (supportNumbers1436 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1436] using hm

private def finish0533Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607]
private def finish0533Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem finish0533Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0533Input0) = fromList finish0533Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0533 : finishSupport ⟨true, bits4 4⟩ support0235 = 2 • support0020 := by
  have hs : support0235 = fromList finish0533Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0533Chunk0]
  have hn : (finish0533Raw0 : Multiset ℕ) = 2 • (supportNumbers0020 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0020] using hm

private def finish0534Input0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 128, 129, 132, 133, 152, 153, 156, 157, 192, 193, 196, 197, 216, 217, 220, 221]
private def finish0534Raw0 : List ℕ := [0, 1, 24, 25, 64, 65, 88, 89, 128, 129, 152, 153, 192, 193, 216, 217]
private theorem finish0534Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0534Input0) = fromList finish0534Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0534 : finishSupport ⟨false, bits4 4⟩ support1438 = 1 • support1439 := by
  have hs : support1438 = fromList finish0534Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0534Chunk0]
  have hn : (finish0534Raw0 : Multiset ℕ) = 1 • (supportNumbers1439 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1439] using hm

private def finish0535Input0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 128, 129, 132, 133, 152, 153, 156, 157, 192, 193, 196, 197, 216, 217, 220, 221, 514, 515, 518, 519, 538, 539, 542, 543, 578, 579, 582, 583, 602, 603, 606, 607, 642, 643, 646, 647, 666, 667, 670, 671, 706, 707, 710, 711, 730, 731, 734, 735]
private def finish0535Raw0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 128, 129, 132, 133, 152, 153, 156, 157, 192, 193, 196, 197, 216, 217, 220, 221, 2, 3, 6, 7, 26, 27, 30, 31, 66, 67, 70, 71, 90, 91, 94, 95, 130, 131, 134, 135, 154, 155, 158, 159, 194, 195, 198, 199, 218, 219, 222, 223]
private theorem finish0535Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0535Input0) = fromList finish0535Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0535 : finishSupport ⟨true, bits4 4⟩ support1440 = 1 • support0326 := by
  have hs : support1440 = fromList finish0535Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0535Chunk0]
  have hn : (finish0535Raw0 : Multiset ℕ) = 1 • (supportNumbers0326 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0326] using hm

private def finish0536Input0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77, 130, 131, 134, 135, 138, 139, 142, 143, 194, 195, 198, 199, 202, 203, 206, 207]
private def finish0536Raw0 : List ℕ := [0, 1, 8, 9, 64, 65, 72, 73, 130, 131, 138, 139, 194, 195, 202, 203]
private theorem finish0536Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0536Input0) = fromList finish0536Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0536 : finishSupport ⟨false, bits4 4⟩ support1442 = 1 • support1443 := by
  have hs : support1442 = fromList finish0536Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0536Chunk0]
  have hn : (finish0536Raw0 : Multiset ℕ) = 1 • (supportNumbers1443 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1443] using hm

private def finish0537Input0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77, 130, 131, 134, 135, 138, 139, 142, 143, 194, 195, 198, 199, 202, 203, 206, 207, 514, 515, 518, 519, 522, 523, 526, 527, 578, 579, 582, 583, 586, 587, 590, 591, 640, 641, 644, 645, 648, 649, 652, 653, 704, 705, 708, 709, 712, 713, 716, 717]
private def finish0537Raw0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77, 130, 131, 134, 135, 138, 139, 142, 143, 194, 195, 198, 199, 202, 203, 206, 207, 2, 3, 6, 7, 10, 11, 14, 15, 66, 67, 70, 71, 74, 75, 78, 79, 128, 129, 132, 133, 136, 137, 140, 141, 192, 193, 196, 197, 200, 201, 204, 205]
private theorem finish0537Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0537Input0) = fromList finish0537Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0537 : finishSupport ⟨true, bits4 4⟩ support1444 = 1 • support0148 := by
  have hs : support1444 = fromList finish0537Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0537Chunk0]
  have hn : (finish0537Raw0 : Multiset ℕ) = 1 • (supportNumbers0148 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0148] using hm

private def finish0538Input0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 64, 65, 68, 69, 74, 75, 78, 79, 146, 147, 150, 151, 152, 153, 156, 157, 210, 211, 214, 215, 216, 217, 220, 221]
private def finish0538Raw0 : List ℕ := [0, 1, 10, 11, 64, 65, 74, 75, 146, 147, 152, 153, 210, 211, 216, 217]
private theorem finish0538Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0538Input0) = fromList finish0538Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0538 : finishSupport ⟨false, bits4 4⟩ support1446 = 1 • support1447 := by
  have hs : support1446 = fromList finish0538Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0538Chunk0]
  have hn : (finish0538Raw0 : Multiset ℕ) = 1 • (supportNumbers1447 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1447] using hm

private def finish0539Input0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 64, 65, 68, 69, 74, 75, 78, 79, 146, 147, 150, 151, 152, 153, 156, 157, 210, 211, 214, 215, 216, 217, 220, 221, 514, 515, 518, 519, 520, 521, 524, 525, 578, 579, 582, 583, 584, 585, 588, 589, 656, 657, 660, 661, 666, 667, 670, 671, 720, 721, 724, 725, 730, 731, 734, 735]
private def finish0539Raw0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 64, 65, 68, 69, 74, 75, 78, 79, 146, 147, 150, 151, 152, 153, 156, 157, 210, 211, 214, 215, 216, 217, 220, 221, 2, 3, 6, 7, 8, 9, 12, 13, 66, 67, 70, 71, 72, 73, 76, 77, 144, 145, 148, 149, 154, 155, 158, 159, 208, 209, 212, 213, 218, 219, 222, 223]
private theorem finish0539Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0539Input0) = fromList finish0539Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0539 : finishSupport ⟨true, bits4 4⟩ support1448 = 1 • support0157 := by
  have hs : support1448 = fromList finish0539Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0539Chunk0]
  have hn : (finish0539Raw0 : Multiset ℕ) = 1 • (supportNumbers0157 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0157] using hm

private def finish0540Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private def finish0540Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 144, 145, 146, 147, 208, 209, 210, 211]
private theorem finish0540Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0540Input0) = fromList finish0540Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0540 : finishSupport ⟨false, bits4 4⟩ support0241 = 1 • support1450 := by
  have hs : support0241 = fromList finish0540Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0540Chunk0]
  have hn : (finish0540Raw0 : Multiset ℕ) = 1 • (supportNumbers1450 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1450] using hm

private def finish0541Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 656, 657, 658, 659, 660, 661, 662, 663, 720, 721, 722, 723, 724, 725, 726, 727]
private def finish0541Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem finish0541Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0541Input0) = fromList finish0541Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0541 : finishSupport ⟨true, bits4 4⟩ support0471 = 2 • support0241 := by
  have hs : support0471 = fromList finish0541Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0541Chunk0]
  have hn : (finish0541Raw0 : Multiset ℕ) = 2 • (supportNumbers0241 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0241] using hm

private def finish0542Input0 : List ℕ := [0, 1, 4, 5, 26, 27, 30, 31, 64, 65, 68, 69, 90, 91, 94, 95, 138, 139, 142, 143, 144, 145, 148, 149, 202, 203, 206, 207, 208, 209, 212, 213]
private def finish0542Raw0 : List ℕ := [0, 1, 26, 27, 64, 65, 90, 91, 138, 139, 144, 145, 202, 203, 208, 209]
private theorem finish0542Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0542Input0) = fromList finish0542Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0542 : finishSupport ⟨false, bits4 4⟩ support1451 = 1 • support1452 := by
  have hs : support1451 = fromList finish0542Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0542Chunk0]
  have hn : (finish0542Raw0 : Multiset ℕ) = 1 • (supportNumbers1452 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1452] using hm

private def finish0543Input0 : List ℕ := [0, 1, 4, 5, 26, 27, 30, 31, 64, 65, 68, 69, 90, 91, 94, 95, 138, 139, 142, 143, 144, 145, 148, 149, 202, 203, 206, 207, 208, 209, 212, 213, 514, 515, 518, 519, 536, 537, 540, 541, 578, 579, 582, 583, 600, 601, 604, 605, 648, 649, 652, 653, 658, 659, 662, 663, 712, 713, 716, 717, 722, 723, 726, 727]
private def finish0543Raw0 : List ℕ := [0, 1, 4, 5, 26, 27, 30, 31, 64, 65, 68, 69, 90, 91, 94, 95, 138, 139, 142, 143, 144, 145, 148, 149, 202, 203, 206, 207, 208, 209, 212, 213, 2, 3, 6, 7, 24, 25, 28, 29, 66, 67, 70, 71, 88, 89, 92, 93, 136, 137, 140, 141, 146, 147, 150, 151, 200, 201, 204, 205, 210, 211, 214, 215]
private theorem finish0543Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0543Input0) = fromList finish0543Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0543 : finishSupport ⟨true, bits4 4⟩ support1453 = 1 • support0411 := by
  have hs : support1453 = fromList finish0543Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0543Chunk0]
  have hn : (finish0543Raw0 : Multiset ℕ) = 1 • (supportNumbers0411 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0411] using hm

private def finish0544Input0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 18, 19, 22, 23, 26, 27, 30, 31, 64, 65, 68, 69, 72, 73, 76, 77, 82, 83, 86, 87, 90, 91, 94, 95, 130, 131, 134, 135, 138, 139, 142, 143, 144, 145, 148, 149, 152, 153, 156, 157, 194, 195, 198, 199, 202, 203, 206, 207, 208, 209, 212, 213, 216, 217, 220, 221]
private def finish0544Raw0 : List ℕ := [0, 1, 8, 9, 18, 19, 26, 27, 64, 65, 72, 73, 82, 83, 90, 91, 130, 131, 138, 139, 144, 145, 152, 153, 194, 195, 202, 203, 208, 209, 216, 217]
private theorem finish0544Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0544Input0) = fromList finish0544Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0544 : finishSupport ⟨false, bits4 4⟩ support1456 = 1 • support1457 := by
  have hs : support1456 = fromList finish0544Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0544Chunk0]
  have hn : (finish0544Raw0 : Multiset ℕ) = 1 • (supportNumbers1457 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1457] using hm

private def finish0545Input0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 18, 19, 22, 23, 26, 27, 30, 31, 64, 65, 68, 69, 72, 73, 76, 77, 82, 83, 86, 87, 90, 91, 94, 95, 130, 131, 134, 135, 138, 139, 142, 143, 144, 145, 148, 149, 152, 153, 156, 157, 194, 195, 198, 199, 202, 203, 206, 207, 208, 209, 212, 213, 216, 217, 220, 221]
private def finish0545Raw0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 18, 19, 22, 23, 26, 27, 30, 31, 64, 65, 68, 69, 72, 73, 76, 77, 82, 83, 86, 87, 90, 91, 94, 95, 130, 131, 134, 135, 138, 139, 142, 143, 144, 145, 148, 149, 152, 153, 156, 157, 194, 195, 198, 199, 202, 203, 206, 207, 208, 209, 212, 213, 216, 217, 220, 221]
private theorem finish0545Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0545Input0) = fromList finish0545Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0545Input1 : List ℕ := [514, 515, 518, 519, 522, 523, 526, 527, 528, 529, 532, 533, 536, 537, 540, 541, 578, 579, 582, 583, 586, 587, 590, 591, 592, 593, 596, 597, 600, 601, 604, 605, 640, 641, 644, 645, 648, 649, 652, 653, 658, 659, 662, 663, 666, 667, 670, 671, 704, 705, 708, 709, 712, 713, 716, 717, 722, 723, 726, 727, 730, 731, 734, 735]
private def finish0545Raw1 : List ℕ := [2, 3, 6, 7, 10, 11, 14, 15, 16, 17, 20, 21, 24, 25, 28, 29, 66, 67, 70, 71, 74, 75, 78, 79, 80, 81, 84, 85, 88, 89, 92, 93, 128, 129, 132, 133, 136, 137, 140, 141, 146, 147, 150, 151, 154, 155, 158, 159, 192, 193, 196, 197, 200, 201, 204, 205, 210, 211, 214, 215, 218, 219, 222, 223]
private theorem finish0545Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0545Input1) = fromList finish0545Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0545 : finishSupport ⟨true, bits4 4⟩ support1458 = 1 • support0096 := by
  have hs : support1458 = fromList finish0545Input0 + fromList finish0545Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0545Chunk0, finish0545Chunk1]
  have hn : (finish0545Raw0 : Multiset ℕ) + (finish0545Raw1 : Multiset ℕ) = 1 • (supportNumbers0096 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0096] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
