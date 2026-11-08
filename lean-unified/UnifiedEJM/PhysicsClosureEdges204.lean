import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0394Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private def finish0394Raw0 : List ℕ := [0, 2, 65, 67, 129, 131, 192, 194]
private theorem finish0394Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0394Input0) = fromList finish0394Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0394 : finishSupport ⟨false, bits4 4⟩ support0144 = 1 • support1185 := by
  have hs : support0144 = fromList finish0394Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0394Chunk0]
  have hn : (finish0394Raw0 : Multiset ℕ) = 1 • (supportNumbers1185 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1185] using hm

private def finish0395Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711]
private def finish0395Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 1, 3, 5, 7, 64, 66, 68, 70, 128, 130, 132, 134, 193, 195, 197, 199]
private theorem finish0395Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0395Input0) = fromList finish0395Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0395 : finishSupport ⟨true, bits4 4⟩ support0314 = 1 • support0229 := by
  have hs : support0314 = fromList finish0395Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0395Chunk0]
  have hn : (finish0395Raw0 : Multiset ℕ) = 1 • (supportNumbers0229 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0229] using hm

private def finish0396Input0 : List ℕ := [0, 4, 10, 14, 65, 69, 75, 79, 129, 133, 139, 143, 192, 196, 202, 206]
private def finish0396Raw0 : List ℕ := [0, 10, 65, 75, 129, 139, 192, 202]
private theorem finish0396Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0396Input0) = fromList finish0396Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0396 : finishSupport ⟨false, bits4 4⟩ support1186 = 1 • support1187 := by
  have hs : support1186 = fromList finish0396Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0396Chunk0]
  have hn : (finish0396Raw0 : Multiset ℕ) = 1 • (supportNumbers1187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1187] using hm

private def finish0397Input0 : List ℕ := [0, 4, 10, 14, 65, 69, 75, 79, 129, 133, 139, 143, 192, 196, 202, 206, 515, 519, 521, 525, 578, 582, 584, 588, 642, 646, 648, 652, 707, 711, 713, 717]
private def finish0397Raw0 : List ℕ := [0, 4, 10, 14, 65, 69, 75, 79, 129, 133, 139, 143, 192, 196, 202, 206, 3, 7, 9, 13, 66, 70, 72, 76, 130, 134, 136, 140, 195, 199, 201, 205]
private theorem finish0397Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0397Input0) = fromList finish0397Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0397 : finishSupport ⟨true, bits4 4⟩ support1188 = 1 • support0735 := by
  have hs : support1188 = fromList finish0397Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0397Chunk0]
  have hn : (finish0397Raw0 : Multiset ℕ) = 1 • (supportNumbers0735 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0735] using hm

private def finish0398Input0 : List ℕ := [0, 3, 4, 7, 9, 10, 13, 14, 65, 66, 69, 70, 72, 75, 76, 79, 129, 130, 133, 134, 136, 139, 140, 143, 192, 195, 196, 199, 201, 202, 205, 206]
private def finish0398Raw0 : List ℕ := [0, 3, 9, 10, 65, 66, 72, 75, 129, 130, 136, 139, 192, 195, 201, 202]
private theorem finish0398Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0398Input0) = fromList finish0398Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0398 : finishSupport ⟨false, bits4 4⟩ support0735 = 1 • support1070 := by
  have hs : support0735 = fromList finish0398Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0398Chunk0]
  have hn : (finish0398Raw0 : Multiset ℕ) = 1 • (supportNumbers1070 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1070] using hm

private def finish0399Input0 : List ℕ := [0, 3, 4, 7, 9, 10, 13, 14, 65, 66, 69, 70, 72, 75, 76, 79, 129, 130, 133, 134, 136, 139, 140, 143, 192, 195, 196, 199, 201, 202, 205, 206, 512, 515, 516, 519, 521, 522, 525, 526, 577, 578, 581, 582, 584, 587, 588, 591, 641, 642, 645, 646, 648, 651, 652, 655, 704, 707, 708, 711, 713, 714, 717, 718]
private def finish0399Raw0 : List ℕ := [0, 3, 4, 7, 9, 10, 13, 14, 65, 66, 69, 70, 72, 75, 76, 79, 129, 130, 133, 134, 136, 139, 140, 143, 192, 195, 196, 199, 201, 202, 205, 206, 0, 3, 4, 7, 9, 10, 13, 14, 65, 66, 69, 70, 72, 75, 76, 79, 129, 130, 133, 134, 136, 139, 140, 143, 192, 195, 196, 199, 201, 202, 205, 206]
private theorem finish0399Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0399Input0) = fromList finish0399Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0399 : finishSupport ⟨true, bits4 4⟩ support1191 = 2 • support0735 := by
  have hs : support1191 = fromList finish0399Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0399Chunk0]
  have hn : (finish0399Raw0 : Multiset ℕ) = 2 • (supportNumbers0735 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0735] using hm

private def finish0400Input0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 128, 129, 132, 133, 192, 193, 196, 197]
private def finish0400Raw0 : List ℕ := [0, 1, 64, 65, 128, 129, 192, 193]
private theorem finish0400Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0400Input0) = fromList finish0400Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0400 : finishSupport ⟨false, bits4 4⟩ support1193 = 1 • support1194 := by
  have hs : support1193 = fromList finish0400Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0400Chunk0]
  have hn : (finish0400Raw0 : Multiset ℕ) = 1 • (supportNumbers1194 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1194] using hm

private def finish0401Input0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 128, 129, 132, 133, 192, 193, 196, 197, 514, 515, 518, 519, 578, 579, 582, 583, 642, 643, 646, 647, 706, 707, 710, 711]
private def finish0401Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 128, 129, 132, 133, 192, 193, 196, 197, 2, 3, 6, 7, 66, 67, 70, 71, 130, 131, 134, 135, 194, 195, 198, 199]
private theorem finish0401Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0401Input0) = fromList finish0401Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0401 : finishSupport ⟨true, bits4 4⟩ support1195 = 1 • support0229 := by
  have hs : support1195 = fromList finish0401Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0401Chunk0]
  have hn : (finish0401Raw0 : Multiset ℕ) = 1 • (supportNumbers0229 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0229] using hm

private def finish0402Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 296, 297, 298, 299, 300, 301, 302, 303, 360, 361, 362, 363, 364, 365, 366, 367, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495]
private def finish0402Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 128, 129, 130, 131, 192, 193, 194, 195, 44, 45, 46, 47, 108, 109, 110, 111, 172, 173, 174, 175, 236, 237, 238, 239]
private theorem finish0402Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0402Input0) = fromList finish0402Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0402 : finishSupport ⟨false, bits4 4⟩ support1197 = 1 • support1198 := by
  have hs : support1197 = fromList finish0402Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0402Chunk0]
  have hn : (finish0402Raw0 : Multiset ℕ) = 1 • (supportNumbers1198 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1198] using hm

private def finish0403Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 296, 297, 298, 299, 300, 301, 302, 303, 360, 361, 362, 363, 364, 365, 366, 367, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495]
private def finish0403Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 40, 41, 42, 43, 44, 45, 46, 47, 104, 105, 106, 107, 108, 109, 110, 111, 168, 169, 170, 171, 172, 173, 174, 175, 232, 233, 234, 235, 236, 237, 238, 239]
private theorem finish0403Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0403Input0) = fromList finish0403Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0403Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 808, 809, 810, 811, 812, 813, 814, 815, 872, 873, 874, 875, 876, 877, 878, 879, 936, 937, 938, 939, 940, 941, 942, 943, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]
private def finish0403Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 40, 41, 42, 43, 44, 45, 46, 47, 104, 105, 106, 107, 108, 109, 110, 111, 168, 169, 170, 171, 172, 173, 174, 175, 232, 233, 234, 235, 236, 237, 238, 239]
private theorem finish0403Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0403Input1) = fromList finish0403Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0403 : finishSupport ⟨true, bits4 4⟩ support1199 = 2 • support0954 := by
  have hs : support1199 = fromList finish0403Input0 + fromList finish0403Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0403Chunk0, finish0403Chunk1]
  have hn : (finish0403Raw0 : Multiset ℕ) + (finish0403Raw1 : Multiset ℕ) = 2 • (supportNumbers0954 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0954] using hm

private def finish0404Input0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 130, 131, 134, 135, 194, 195, 198, 199]
private def finish0404Raw0 : List ℕ := [0, 1, 64, 65, 130, 131, 194, 195]
private theorem finish0404Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0404Input0) = fromList finish0404Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0404 : finishSupport ⟨false, bits4 4⟩ support1200 = 1 • support1201 := by
  have hs : support1200 = fromList finish0404Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0404Chunk0]
  have hn : (finish0404Raw0 : Multiset ℕ) = 1 • (supportNumbers1201 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1201] using hm

private def finish0405Input0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 130, 131, 134, 135, 194, 195, 198, 199, 514, 515, 518, 519, 578, 579, 582, 583, 640, 641, 644, 645, 704, 705, 708, 709]
private def finish0405Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 130, 131, 134, 135, 194, 195, 198, 199, 2, 3, 6, 7, 66, 67, 70, 71, 128, 129, 132, 133, 192, 193, 196, 197]
private theorem finish0405Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0405Input0) = fromList finish0405Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0405 : finishSupport ⟨true, bits4 4⟩ support1202 = 1 • support0229 := by
  have hs : support1202 = fromList finish0405Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0405Chunk0]
  have hn : (finish0405Raw0 : Multiset ℕ) = 1 • (supportNumbers0229 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0229] using hm

private def finish0406Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487]
private def finish0406Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 128, 129, 130, 131, 192, 193, 194, 195, 36, 37, 38, 39, 100, 101, 102, 103, 164, 165, 166, 167, 228, 229, 230, 231]
private theorem finish0406Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0406Input0) = fromList finish0406Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0406 : finishSupport ⟨false, bits4 4⟩ support1204 = 1 • support1205 := by
  have hs : support1204 = fromList finish0406Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0406Chunk0]
  have hn : (finish0406Raw0 : Multiset ℕ) = 1 • (supportNumbers1205 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1205] using hm

private def finish0407Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487]
private def finish0407Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 32, 33, 34, 35, 36, 37, 38, 39, 96, 97, 98, 99, 100, 101, 102, 103, 160, 161, 162, 163, 164, 165, 166, 167, 224, 225, 226, 227, 228, 229, 230, 231]
private theorem finish0407Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0407Input0) = fromList finish0407Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0407Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 800, 801, 802, 803, 804, 805, 806, 807, 864, 865, 866, 867, 868, 869, 870, 871, 928, 929, 930, 931, 932, 933, 934, 935, 992, 993, 994, 995, 996, 997, 998, 999]
private def finish0407Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 32, 33, 34, 35, 36, 37, 38, 39, 96, 97, 98, 99, 100, 101, 102, 103, 160, 161, 162, 163, 164, 165, 166, 167, 224, 225, 226, 227, 228, 229, 230, 231]
private theorem finish0407Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0407Input1) = fromList finish0407Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0407 : finishSupport ⟨true, bits4 4⟩ support1206 = 2 • support0913 := by
  have hs : support1206 = fromList finish0407Input0 + fromList finish0407Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0407Chunk0, finish0407Chunk1]
  have hn : (finish0407Raw0 : Multiset ℕ) + (finish0407Raw1 : Multiset ℕ) = 2 • (supportNumbers0913 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0913] using hm

private def finish0408Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 440, 441, 442, 443, 444, 445, 446, 447, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0408Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 188, 189, 190, 191, 252, 253, 254, 255]
private theorem finish0408Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0408Input0) = fromList finish0408Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0408 : finishSupport ⟨false, bits4 4⟩ support1208 = 1 • support1087 := by
  have hs : support1208 = fromList finish0408Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0408Chunk0]
  have hn : (finish0408Raw0 : Multiset ℕ) = 1 • (supportNumbers1087 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1087] using hm

private def finish0409Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 440, 441, 442, 443, 444, 445, 446, 447, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 952, 953, 954, 955, 956, 957, 958, 959, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def finish0409Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 184, 185, 186, 187, 188, 189, 190, 191, 248, 249, 250, 251, 252, 253, 254, 255, 0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 184, 185, 186, 187, 188, 189, 190, 191, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0409Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0409Input0) = fromList finish0409Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0409 : finishSupport ⟨true, bits4 4⟩ support1209 = 2 • support1210 := by
  have hs : support1209 = fromList finish0409Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0409Chunk0]
  have hn : (finish0409Raw0 : Multiset ℕ) = 2 • (supportNumbers1210 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1210] using hm

private def finish0410Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 416, 417, 418, 419, 420, 421, 422, 423, 440, 441, 442, 443, 444, 445, 446, 447, 480, 481, 482, 483, 484, 485, 486, 487, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0410Raw0 : List ℕ := [0, 1, 2, 3, 24, 25, 26, 27, 64, 65, 66, 67, 88, 89, 90, 91, 164, 165, 166, 167, 188, 189, 190, 191, 228, 229, 230, 231, 252, 253, 254, 255]
private theorem finish0410Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0410Input0) = fromList finish0410Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0410 : finishSupport ⟨false, bits4 4⟩ support1213 = 1 • support1214 := by
  have hs : support1213 = fromList finish0410Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0410Chunk0]
  have hn : (finish0410Raw0 : Multiset ℕ) = 1 • (supportNumbers1214 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1214] using hm

private def finish0411Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 416, 417, 418, 419, 420, 421, 422, 423, 440, 441, 442, 443, 444, 445, 446, 447, 480, 481, 482, 483, 484, 485, 486, 487, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0411Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 160, 161, 162, 163, 164, 165, 166, 167, 184, 185, 186, 187, 188, 189, 190, 191, 224, 225, 226, 227, 228, 229, 230, 231, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0411Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0411Input0) = fromList finish0411Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0411Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 928, 929, 930, 931, 932, 933, 934, 935, 952, 953, 954, 955, 956, 957, 958, 959, 992, 993, 994, 995, 996, 997, 998, 999, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def finish0411Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 160, 161, 162, 163, 164, 165, 166, 167, 184, 185, 186, 187, 188, 189, 190, 191, 224, 225, 226, 227, 228, 229, 230, 231, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0411Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0411Input1) = fromList finish0411Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0411 : finishSupport ⟨true, bits4 4⟩ support1215 = 2 • support1216 := by
  have hs : support1215 = fromList finish0411Input0 + fromList finish0411Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0411Chunk0, finish0411Chunk1]
  have hn : (finish0411Raw0 : Multiset ℕ) + (finish0411Raw1 : Multiset ℕ) = 2 • (supportNumbers1216 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1216] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
