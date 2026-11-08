import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0129Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 288, 289, 290, 291, 308, 309, 310, 311, 424, 425, 426, 427, 444, 445, 446, 447, 576, 577, 578, 579, 596, 597, 598, 599, 712, 713, 714, 715, 732, 733, 734, 735, 864, 865, 866, 867, 884, 885, 886, 887, 1000, 1001, 1002, 1003, 1020, 1021, 1022, 1023]
private def finish0129Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 32, 33, 34, 35, 52, 53, 54, 55, 168, 169, 170, 171, 188, 189, 190, 191, 64, 65, 66, 67, 84, 85, 86, 87, 200, 201, 202, 203, 220, 221, 222, 223, 96, 97, 98, 99, 116, 117, 118, 119, 232, 233, 234, 235, 252, 253, 254, 255]
private theorem finish0129Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0129Input0) = fromList finish0129Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0129 : finishSupport ⟨true, bits4 4⟩ support0714 = 1 • support0715 := by
  have hs : support0714 = fromList finish0129Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0129Chunk0]
  have hn : (finish0129Raw0 : Multiset ℕ) = 1 • (supportNumbers0715 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0715] using hm

private def finish0130Input0 : List ℕ := [0, 1, 8, 9, 20, 21, 28, 29, 128, 129, 136, 137, 148, 149, 156, 157]
private def finish0130Raw0 : List ℕ := [0, 1, 8, 9, 128, 129, 136, 137]
private theorem finish0130Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0130Input0) = fromList finish0130Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0130 : finishSupport ⟨false, bits4 4⟩ support0716 = 1 • support0717 := by
  have hs : support0716 = fromList finish0130Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0130Chunk0]
  have hn : (finish0130Raw0 : Multiset ℕ) = 1 • (supportNumbers0717 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0717] using hm

private def finish0131Input0 : List ℕ := [0, 1, 8, 9, 20, 21, 28, 29, 128, 129, 136, 137, 148, 149, 156, 157, 578, 579, 586, 587, 598, 599, 606, 607, 706, 707, 714, 715, 726, 727, 734, 735]
private def finish0131Raw0 : List ℕ := [0, 1, 8, 9, 20, 21, 28, 29, 128, 129, 136, 137, 148, 149, 156, 157, 66, 67, 74, 75, 86, 87, 94, 95, 194, 195, 202, 203, 214, 215, 222, 223]
private theorem finish0131Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0131Input0) = fromList finish0131Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0131 : finishSupport ⟨true, bits4 4⟩ support0718 = 1 • support0719 := by
  have hs : support0718 = fromList finish0131Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0131Chunk0]
  have hn : (finish0131Raw0 : Multiset ℕ) = 1 • (supportNumbers0719 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0719] using hm

private def finish0132Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 288, 290, 292, 294, 353, 355, 357, 359]
private def finish0132Raw0 : List ℕ := [0, 2, 65, 67, 36, 38, 101, 103]
private theorem finish0132Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0132Input0) = fromList finish0132Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0132 : finishSupport ⟨false, bits4 4⟩ support0722 = 1 • support0723 := by
  have hs : support0722 = fromList finish0132Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0132Chunk0]
  have hn : (finish0132Raw0 : Multiset ℕ) = 1 • (supportNumbers0723 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0723] using hm

private def finish0133Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 288, 290, 292, 294, 353, 355, 357, 359, 513, 515, 517, 519, 576, 578, 580, 582, 801, 803, 805, 807, 864, 866, 868, 870]
private def finish0133Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 32, 34, 36, 38, 97, 99, 101, 103, 1, 3, 5, 7, 64, 66, 68, 70, 33, 35, 37, 39, 96, 98, 100, 102]
private theorem finish0133Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0133Input0) = fromList finish0133Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0133 : finishSupport ⟨true, bits4 4⟩ support0724 = 1 • support0725 := by
  have hs : support0724 = fromList finish0133Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0133Chunk0]
  have hn : (finish0133Raw0 : Multiset ℕ) = 1 • (supportNumbers0725 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0725] using hm

private def finish0134Input0 : List ℕ := [0, 4, 65, 69, 136, 140, 201, 205]
private def finish0134Raw0 : List ℕ := [0, 65, 136, 201]
private theorem finish0134Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0134Input0) = fromList finish0134Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0134 : finishSupport ⟨false, bits4 4⟩ support0726 = 1 • support0727 := by
  have hs : support0726 = fromList finish0134Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0134Chunk0]
  have hn : (finish0134Raw0 : Multiset ℕ) = 1 • (supportNumbers0727 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0727] using hm

private def finish0135Input0 : List ℕ := [0, 4, 65, 69, 136, 140, 201, 205, 515, 519, 578, 582, 651, 655, 714, 718]
private def finish0135Raw0 : List ℕ := [0, 4, 65, 69, 136, 140, 201, 205, 3, 7, 66, 70, 139, 143, 202, 206]
private theorem finish0135Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0135Input0) = fromList finish0135Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0135 : finishSupport ⟨true, bits4 4⟩ support0728 = 1 • support0729 := by
  have hs : support0728 = fromList finish0135Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0135Chunk0]
  have hn : (finish0135Raw0 : Multiset ℕ) = 1 • (supportNumbers0729 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0729] using hm

private def finish0136Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private def finish0136Raw0 : List ℕ := [0, 2, 65, 67, 136, 138, 201, 203]
private theorem finish0136Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0136Input0) = fromList finish0136Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0136 : finishSupport ⟨false, bits4 4⟩ support0076 = 1 • support0730 := by
  have hs : support0076 = fromList finish0136Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0136Chunk0]
  have hn : (finish0136Raw0 : Multiset ℕ) = 1 • (supportNumbers0730 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0730] using hm

private def finish0137Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 513, 515, 517, 519, 576, 578, 580, 582, 649, 651, 653, 655, 712, 714, 716, 718]
private def finish0137Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 1, 3, 5, 7, 64, 66, 68, 70, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem finish0137Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0137Input0) = fromList finish0137Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0137 : finishSupport ⟨true, bits4 4⟩ support0731 = 1 • support0088 := by
  have hs : support0731 = fromList finish0137Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0137Chunk0]
  have hn : (finish0137Raw0 : Multiset ℕ) = 1 • (supportNumbers0088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0088] using hm

private def finish0138Input0 : List ℕ := [0, 4, 10, 14, 65, 69, 75, 79, 130, 134, 136, 140, 195, 199, 201, 205]
private def finish0138Raw0 : List ℕ := [0, 10, 65, 75, 130, 136, 195, 201]
private theorem finish0138Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0138Input0) = fromList finish0138Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0138 : finishSupport ⟨false, bits4 4⟩ support0732 = 1 • support0733 := by
  have hs : support0732 = fromList finish0138Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0138Chunk0]
  have hn : (finish0138Raw0 : Multiset ℕ) = 1 • (supportNumbers0733 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0733] using hm

private def finish0139Input0 : List ℕ := [0, 4, 10, 14, 65, 69, 75, 79, 130, 134, 136, 140, 195, 199, 201, 205, 515, 519, 521, 525, 578, 582, 584, 588, 641, 645, 651, 655, 704, 708, 714, 718]
private def finish0139Raw0 : List ℕ := [0, 4, 10, 14, 65, 69, 75, 79, 130, 134, 136, 140, 195, 199, 201, 205, 3, 7, 9, 13, 66, 70, 72, 76, 129, 133, 139, 143, 192, 196, 202, 206]
private theorem finish0139Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0139Input0) = fromList finish0139Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0139 : finishSupport ⟨true, bits4 4⟩ support0734 = 1 • support0735 := by
  have hs : support0734 = fromList finish0139Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0139Chunk0]
  have hn : (finish0139Raw0 : Multiset ℕ) = 1 • (supportNumbers0735 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0735] using hm

private def finish0140Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367, 416, 418, 420, 422, 424, 426, 428, 430, 481, 483, 485, 487, 489, 491, 493, 495]
private def finish0140Raw0 : List ℕ := [0, 2, 8, 10, 65, 67, 73, 75, 128, 130, 136, 138, 193, 195, 201, 203, 36, 38, 44, 46, 101, 103, 109, 111, 164, 166, 172, 174, 229, 231, 237, 239]
private theorem finish0140Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0140Input0) = fromList finish0140Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0140 : finishSupport ⟨false, bits4 4⟩ support0737 = 1 • support0738 := by
  have hs : support0737 = fromList finish0140Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0140Chunk0]
  have hn : (finish0140Raw0 : Multiset ℕ) = 1 • (supportNumbers0738 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0738] using hm

private def finish0141Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367, 416, 418, 420, 422, 424, 426, 428, 430, 481, 483, 485, 487, 489, 491, 493, 495]
private def finish0141Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 32, 34, 36, 38, 40, 42, 44, 46, 97, 99, 101, 103, 105, 107, 109, 111, 160, 162, 164, 166, 168, 170, 172, 174, 225, 227, 229, 231, 233, 235, 237, 239]
private theorem finish0141Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0141Input0) = fromList finish0141Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0141Input1 : List ℕ := [513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 641, 643, 645, 647, 649, 651, 653, 655, 704, 706, 708, 710, 712, 714, 716, 718, 801, 803, 805, 807, 809, 811, 813, 815, 864, 866, 868, 870, 872, 874, 876, 878, 929, 931, 933, 935, 937, 939, 941, 943, 992, 994, 996, 998, 1000, 1002, 1004, 1006]
private def finish0141Raw1 : List ℕ := [1, 3, 5, 7, 9, 11, 13, 15, 64, 66, 68, 70, 72, 74, 76, 78, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 33, 35, 37, 39, 41, 43, 45, 47, 96, 98, 100, 102, 104, 106, 108, 110, 161, 163, 165, 167, 169, 171, 173, 175, 224, 226, 228, 230, 232, 234, 236, 238]
private theorem finish0141Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0141Input1) = fromList finish0141Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0141 : finishSupport ⟨true, bits4 4⟩ support0739 = 1 • support0527 := by
  have hs : support0739 = fromList finish0141Input0 + fromList finish0141Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0141Chunk0, finish0141Chunk1]
  have hn : (finish0141Raw0 : Multiset ℕ) + (finish0141Raw1 : Multiset ℕ) = 1 • (supportNumbers0527 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0527] using hm

private def finish0142Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 425, 427, 429, 431, 488, 490, 492, 494]
private def finish0142Raw0 : List ℕ := [0, 2, 65, 67, 173, 175, 236, 238]
private theorem finish0142Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0142Input0) = fromList finish0142Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0142 : finishSupport ⟨false, bits4 4⟩ support0741 = 1 • support0742 := by
  have hs : support0741 = fromList finish0142Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0142Chunk0]
  have hn : (finish0142Raw0 : Multiset ℕ) = 1 • (supportNumbers0742 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0742] using hm

private def finish0143Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 425, 427, 429, 431, 488, 490, 492, 494, 513, 515, 517, 519, 576, 578, 580, 582, 936, 938, 940, 942, 1001, 1003, 1005, 1007]
private def finish0143Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 169, 171, 173, 175, 232, 234, 236, 238, 1, 3, 5, 7, 64, 66, 68, 70, 168, 170, 172, 174, 233, 235, 237, 239]
private theorem finish0143Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0143Input0) = fromList finish0143Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0143 : finishSupport ⟨true, bits4 4⟩ support0743 = 1 • support0744 := by
  have hs : support0743 = fromList finish0143Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0143Chunk0]
  have hn : (finish0143Raw0 : Multiset ℕ) = 1 • (supportNumbers0744 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0744] using hm

private def finish0144Input0 : List ℕ := [0, 3, 4, 7, 65, 66, 69, 70, 137, 138, 141, 142, 200, 203, 204, 207]
private def finish0144Raw0 : List ℕ := [0, 3, 65, 66, 137, 138, 200, 203]
private theorem finish0144Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0144Input0) = fromList finish0144Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0144 : finishSupport ⟨false, bits4 4⟩ support0599 = 1 • support0666 := by
  have hs : support0599 = fromList finish0144Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0144Chunk0]
  have hn : (finish0144Raw0 : Multiset ℕ) = 1 • (supportNumbers0666 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0666] using hm

private def finish0145Input0 : List ℕ := [0, 3, 4, 7, 65, 66, 69, 70, 137, 138, 141, 142, 200, 203, 204, 207, 512, 515, 516, 519, 577, 578, 581, 582, 649, 650, 653, 654, 712, 715, 716, 719]
private def finish0145Raw0 : List ℕ := [0, 3, 4, 7, 65, 66, 69, 70, 137, 138, 141, 142, 200, 203, 204, 207, 0, 3, 4, 7, 65, 66, 69, 70, 137, 138, 141, 142, 200, 203, 204, 207]
private theorem finish0145Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0145Input0) = fromList finish0145Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0145 : finishSupport ⟨true, bits4 4⟩ support0745 = 2 • support0599 := by
  have hs : support0745 = fromList finish0145Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0145Chunk0]
  have hn : (finish0145Raw0 : Multiset ℕ) = 2 • (supportNumbers0599 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0599] using hm

private def finish0146Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495]
private def finish0146Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 136, 137, 138, 139, 200, 201, 202, 203, 36, 37, 38, 39, 100, 101, 102, 103, 172, 173, 174, 175, 236, 237, 238, 239]
private theorem finish0146Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0146Input0) = fromList finish0146Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0146 : finishSupport ⟨false, bits4 4⟩ support0747 = 1 • support0748 := by
  have hs : support0747 = fromList finish0146Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0146Chunk0]
  have hn : (finish0146Raw0 : Multiset ℕ) = 1 • (supportNumbers0748 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0748] using hm

private def finish0147Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495]
private def finish0147Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 32, 33, 34, 35, 36, 37, 38, 39, 96, 97, 98, 99, 100, 101, 102, 103, 168, 169, 170, 171, 172, 173, 174, 175, 232, 233, 234, 235, 236, 237, 238, 239]
private theorem finish0147Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0147Input0) = fromList finish0147Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0147Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 648, 649, 650, 651, 652, 653, 654, 655, 712, 713, 714, 715, 716, 717, 718, 719, 800, 801, 802, 803, 804, 805, 806, 807, 864, 865, 866, 867, 868, 869, 870, 871, 936, 937, 938, 939, 940, 941, 942, 943, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]
private def finish0147Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 32, 33, 34, 35, 36, 37, 38, 39, 96, 97, 98, 99, 100, 101, 102, 103, 168, 169, 170, 171, 172, 173, 174, 175, 232, 233, 234, 235, 236, 237, 238, 239]
private theorem finish0147Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0147Input1) = fromList finish0147Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0147 : finishSupport ⟨true, bits4 4⟩ support0749 = 2 • support0604 := by
  have hs : support0749 = fromList finish0147Input0 + fromList finish0147Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0147Chunk0, finish0147Chunk1]
  have hn : (finish0147Raw0 : Multiset ℕ) + (finish0147Raw1 : Multiset ℕ) = 2 • (supportNumbers0604 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0604] using hm

private def finish0148Input0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 129, 133, 136, 140, 192, 196, 201, 205]
private def finish0148Raw0 : List ℕ := [0, 9, 65, 72, 129, 136, 192, 201]
private theorem finish0148Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0148Input0) = fromList finish0148Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0148 : finishSupport ⟨false, bits4 4⟩ support0750 = 1 • support0751 := by
  have hs : support0750 = fromList finish0148Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0148Chunk0]
  have hn : (finish0148Raw0 : Multiset ℕ) = 1 • (supportNumbers0751 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0751] using hm

private def finish0149Input0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 129, 133, 136, 140, 192, 196, 201, 205, 515, 519, 522, 526, 578, 582, 587, 591, 642, 646, 651, 655, 707, 711, 714, 718]
private def finish0149Raw0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 129, 133, 136, 140, 192, 196, 201, 205, 3, 7, 10, 14, 66, 70, 75, 79, 130, 134, 139, 143, 195, 199, 202, 206]
private theorem finish0149Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0149Input0) = fromList finish0149Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0149 : finishSupport ⟨true, bits4 4⟩ support0752 = 1 • support0735 := by
  have hs : support0752 = fromList finish0149Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0149Chunk0]
  have hn : (finish0149Raw0 : Multiset ℕ) = 1 • (supportNumbers0735 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0735] using hm

private def finish0150Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 289, 291, 293, 295, 296, 298, 300, 302, 352, 354, 356, 358, 361, 363, 365, 367, 416, 418, 420, 422, 425, 427, 429, 431, 481, 483, 485, 487, 488, 490, 492, 494]
private def finish0150Raw0 : List ℕ := [0, 2, 9, 11, 65, 67, 72, 74, 129, 131, 136, 138, 192, 194, 201, 203, 37, 39, 44, 46, 100, 102, 109, 111, 164, 166, 173, 175, 229, 231, 236, 238]
private theorem finish0150Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0150Input0) = fromList finish0150Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0150 : finishSupport ⟨false, bits4 4⟩ support0754 = 1 • support0755 := by
  have hs : support0754 = fromList finish0150Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0150Chunk0]
  have hn : (finish0150Raw0 : Multiset ℕ) = 1 • (supportNumbers0755 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0755] using hm

private def finish0151Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 289, 291, 293, 295, 296, 298, 300, 302, 352, 354, 356, 358, 361, 363, 365, 367, 416, 418, 420, 422, 425, 427, 429, 431, 481, 483, 485, 487, 488, 490, 492, 494]
private def finish0151Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 33, 35, 37, 39, 40, 42, 44, 46, 96, 98, 100, 102, 105, 107, 109, 111, 160, 162, 164, 166, 169, 171, 173, 175, 225, 227, 229, 231, 232, 234, 236, 238]
private theorem finish0151Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0151Input0) = fromList finish0151Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0151Input1 : List ℕ := [513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 800, 802, 804, 806, 809, 811, 813, 815, 865, 867, 869, 871, 872, 874, 876, 878, 929, 931, 933, 935, 936, 938, 940, 942, 992, 994, 996, 998, 1001, 1003, 1005, 1007]
private def finish0151Raw1 : List ℕ := [1, 3, 5, 7, 8, 10, 12, 14, 64, 66, 68, 70, 73, 75, 77, 79, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 32, 34, 36, 38, 41, 43, 45, 47, 97, 99, 101, 103, 104, 106, 108, 110, 161, 163, 165, 167, 168, 170, 172, 174, 224, 226, 228, 230, 233, 235, 237, 239]
private theorem finish0151Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0151Input1) = fromList finish0151Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0151 : finishSupport ⟨true, bits4 4⟩ support0756 = 1 • support0527 := by
  have hs : support0756 = fromList finish0151Input0 + fromList finish0151Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0151Chunk0, finish0151Chunk1]
  have hn : (finish0151Raw0 : Multiset ℕ) + (finish0151Raw1 : Multiset ℕ) = 1 • (supportNumbers0527 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0527] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
