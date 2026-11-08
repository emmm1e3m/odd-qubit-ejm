import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0152Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private def finish0152Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 64, 65, 66, 67, 72, 73, 74, 75, 128, 129, 130, 131, 136, 137, 138, 139, 192, 193, 194, 195, 200, 201, 202, 203]
private theorem finish0152Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0152Input0) = fromList finish0152Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0152 : finishSupport ⟨false, bits4 4⟩ support0148 = 1 • support0679 := by
  have hs : support0148 = fromList finish0152Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0152Chunk0]
  have hn : (finish0152Raw0 : Multiset ℕ) = 1 • (supportNumbers0679 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0679] using hm

private def finish0153Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private def finish0153Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem finish0153Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0153Input0) = fromList finish0153Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0153Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]
private def finish0153Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem finish0153Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0153Input1) = fromList finish0153Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0153 : finishSupport ⟨true, bits4 4⟩ support0149 = 2 • support0148 := by
  have hs : support0149 = fromList finish0153Input0 + fromList finish0153Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0153Chunk0, finish0153Chunk1]
  have hn : (finish0153Raw0 : Multiset ℕ) + (finish0153Raw1 : Multiset ℕ) = 2 • (supportNumbers0148 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0148] using hm

private def finish0154Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71]
private def finish0154Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67]
private theorem finish0154Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0154Input0) = fromList finish0154Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0154 : finishSupport ⟨false, bits4 4⟩ support0044 = 1 • support0682 := by
  have hs : support0044 = fromList finish0154Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0154Chunk0]
  have hn : (finish0154Raw0 : Multiset ℕ) = 1 • (supportNumbers0682 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0682] using hm

private def finish0155Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583]
private def finish0155Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71]
private theorem finish0155Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0155Input0) = fromList finish0155Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0155 : finishSupport ⟨true, bits4 4⟩ support0319 = 2 • support0044 := by
  have hs : support0319 = fromList finish0155Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0155Chunk0]
  have hn : (finish0155Raw0 : Multiset ℕ) = 2 • (supportNumbers0044 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0044] using hm

private def finish0156Input0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 154, 155, 158, 159, 218, 219, 222, 223]
private def finish0156Raw0 : List ℕ := [0, 1, 64, 65, 154, 155, 218, 219]
private theorem finish0156Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0156Input0) = fromList finish0156Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0156 : finishSupport ⟨false, bits4 4⟩ support0758 = 1 • support0759 := by
  have hs : support0758 = fromList finish0156Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0156Chunk0]
  have hn : (finish0156Raw0 : Multiset ℕ) = 1 • (supportNumbers0759 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0759] using hm

private def finish0157Input0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 154, 155, 158, 159, 218, 219, 222, 223, 514, 515, 518, 519, 578, 579, 582, 583, 664, 665, 668, 669, 728, 729, 732, 733]
private def finish0157Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 154, 155, 158, 159, 218, 219, 222, 223, 2, 3, 6, 7, 66, 67, 70, 71, 152, 153, 156, 157, 216, 217, 220, 221]
private theorem finish0157Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0157Input0) = fromList finish0157Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0157 : finishSupport ⟨true, bits4 4⟩ support0760 = 1 • support0151 := by
  have hs : support0760 = fromList finish0157Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0157Chunk0]
  have hn : (finish0157Raw0 : Multiset ℕ) = 1 • (supportNumbers0151 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0151] using hm

private def finish0158Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 440, 441, 442, 443, 444, 445, 446, 447, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0158Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 152, 153, 154, 155, 216, 217, 218, 219, 36, 37, 38, 39, 100, 101, 102, 103, 188, 189, 190, 191, 252, 253, 254, 255]
private theorem finish0158Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0158Input0) = fromList finish0158Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0158 : finishSupport ⟨false, bits4 4⟩ support0762 = 1 • support0763 := by
  have hs : support0762 = fromList finish0158Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0158Chunk0]
  have hn : (finish0158Raw0 : Multiset ℕ) = 1 • (supportNumbers0763 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0763] using hm

private def finish0159Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 440, 441, 442, 443, 444, 445, 446, 447, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0159Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 32, 33, 34, 35, 36, 37, 38, 39, 96, 97, 98, 99, 100, 101, 102, 103, 184, 185, 186, 187, 188, 189, 190, 191, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0159Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0159Input0) = fromList finish0159Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0159Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735, 800, 801, 802, 803, 804, 805, 806, 807, 864, 865, 866, 867, 868, 869, 870, 871, 952, 953, 954, 955, 956, 957, 958, 959, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def finish0159Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 32, 33, 34, 35, 36, 37, 38, 39, 96, 97, 98, 99, 100, 101, 102, 103, 184, 185, 186, 187, 188, 189, 190, 191, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0159Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0159Input1) = fromList finish0159Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0159 : finishSupport ⟨true, bits4 4⟩ support0764 = 2 • support0765 := by
  have hs : support0764 = fromList finish0159Input0 + fromList finish0159Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0159Chunk0, finish0159Chunk1]
  have hn : (finish0159Raw0 : Multiset ℕ) + (finish0159Raw1 : Multiset ℕ) = 2 • (supportNumbers0765 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0765] using hm

private def finish0160Input0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 136, 137, 140, 141, 200, 201, 204, 205]
private def finish0160Raw0 : List ℕ := [0, 1, 64, 65, 136, 137, 200, 201]
private theorem finish0160Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0160Input0) = fromList finish0160Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0160 : finishSupport ⟨false, bits4 4⟩ support0766 = 1 • support0767 := by
  have hs : support0766 = fromList finish0160Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0160Chunk0]
  have hn : (finish0160Raw0 : Multiset ℕ) = 1 • (supportNumbers0767 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0767] using hm

private def finish0161Input0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 136, 137, 140, 141, 200, 201, 204, 205, 514, 515, 518, 519, 578, 579, 582, 583, 650, 651, 654, 655, 714, 715, 718, 719]
private def finish0161Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 136, 137, 140, 141, 200, 201, 204, 205, 2, 3, 6, 7, 66, 67, 70, 71, 138, 139, 142, 143, 202, 203, 206, 207]
private theorem finish0161Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0161Input0) = fromList finish0161Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0161 : finishSupport ⟨true, bits4 4⟩ support0768 = 1 • support0088 := by
  have hs : support0768 = fromList finish0161Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0161Chunk0]
  have hn : (finish0161Raw0 : Multiset ℕ) = 1 • (supportNumbers0088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0088] using hm

private def finish0162Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 312, 313, 314, 315, 316, 317, 318, 319, 376, 377, 378, 379, 380, 381, 382, 383, 432, 433, 434, 435, 436, 437, 438, 439, 496, 497, 498, 499, 500, 501, 502, 503]
private def finish0162Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 136, 137, 138, 139, 200, 201, 202, 203, 60, 61, 62, 63, 124, 125, 126, 127, 180, 181, 182, 183, 244, 245, 246, 247]
private theorem finish0162Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0162Input0) = fromList finish0162Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0162 : finishSupport ⟨false, bits4 4⟩ support0770 = 1 • support0696 := by
  have hs : support0770 = fromList finish0162Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0162Chunk0]
  have hn : (finish0162Raw0 : Multiset ℕ) = 1 • (supportNumbers0696 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0696] using hm

private def finish0163Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 312, 313, 314, 315, 316, 317, 318, 319, 376, 377, 378, 379, 380, 381, 382, 383, 432, 433, 434, 435, 436, 437, 438, 439, 496, 497, 498, 499, 500, 501, 502, 503]
private def finish0163Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 56, 57, 58, 59, 60, 61, 62, 63, 120, 121, 122, 123, 124, 125, 126, 127, 176, 177, 178, 179, 180, 181, 182, 183, 240, 241, 242, 243, 244, 245, 246, 247]
private theorem finish0163Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0163Input0) = fromList finish0163Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0163Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 648, 649, 650, 651, 652, 653, 654, 655, 712, 713, 714, 715, 716, 717, 718, 719, 824, 825, 826, 827, 828, 829, 830, 831, 888, 889, 890, 891, 892, 893, 894, 895, 944, 945, 946, 947, 948, 949, 950, 951, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015]
private def finish0163Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 56, 57, 58, 59, 60, 61, 62, 63, 120, 121, 122, 123, 124, 125, 126, 127, 176, 177, 178, 179, 180, 181, 182, 183, 240, 241, 242, 243, 244, 245, 246, 247]
private theorem finish0163Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0163Input1) = fromList finish0163Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0163 : finishSupport ⟨true, bits4 4⟩ support0771 = 2 • support0772 := by
  have hs : support0771 = fromList finish0163Input0 + fromList finish0163Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0163Chunk0, finish0163Chunk1]
  have hn : (finish0163Raw0 : Multiset ℕ) + (finish0163Raw1 : Multiset ℕ) = 2 • (supportNumbers0772 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0772] using hm

private def finish0164Input0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 18, 19, 22, 23, 24, 25, 28, 29, 64, 65, 68, 69, 74, 75, 78, 79, 82, 83, 86, 87, 88, 89, 92, 93, 130, 131, 134, 135, 136, 137, 140, 141, 144, 145, 148, 149, 154, 155, 158, 159, 194, 195, 198, 199, 200, 201, 204, 205, 208, 209, 212, 213, 218, 219, 222, 223]
private def finish0164Raw0 : List ℕ := [0, 1, 10, 11, 18, 19, 24, 25, 64, 65, 74, 75, 82, 83, 88, 89, 130, 131, 136, 137, 144, 145, 154, 155, 194, 195, 200, 201, 208, 209, 218, 219]
private theorem finish0164Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0164Input0) = fromList finish0164Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0164 : finishSupport ⟨false, bits4 4⟩ support0773 = 1 • support0774 := by
  have hs : support0773 = fromList finish0164Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0164Chunk0]
  have hn : (finish0164Raw0 : Multiset ℕ) = 1 • (supportNumbers0774 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0774] using hm

private def finish0165Input0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 18, 19, 22, 23, 24, 25, 28, 29, 64, 65, 68, 69, 74, 75, 78, 79, 82, 83, 86, 87, 88, 89, 92, 93, 130, 131, 134, 135, 136, 137, 140, 141, 144, 145, 148, 149, 154, 155, 158, 159, 194, 195, 198, 199, 200, 201, 204, 205, 208, 209, 212, 213, 218, 219, 222, 223]
private def finish0165Raw0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 18, 19, 22, 23, 24, 25, 28, 29, 64, 65, 68, 69, 74, 75, 78, 79, 82, 83, 86, 87, 88, 89, 92, 93, 130, 131, 134, 135, 136, 137, 140, 141, 144, 145, 148, 149, 154, 155, 158, 159, 194, 195, 198, 199, 200, 201, 204, 205, 208, 209, 212, 213, 218, 219, 222, 223]
private theorem finish0165Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0165Input0) = fromList finish0165Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0165Input1 : List ℕ := [514, 515, 518, 519, 520, 521, 524, 525, 528, 529, 532, 533, 538, 539, 542, 543, 578, 579, 582, 583, 584, 585, 588, 589, 592, 593, 596, 597, 602, 603, 606, 607, 640, 641, 644, 645, 650, 651, 654, 655, 658, 659, 662, 663, 664, 665, 668, 669, 704, 705, 708, 709, 714, 715, 718, 719, 722, 723, 726, 727, 728, 729, 732, 733]
private def finish0165Raw1 : List ℕ := [2, 3, 6, 7, 8, 9, 12, 13, 16, 17, 20, 21, 26, 27, 30, 31, 66, 67, 70, 71, 72, 73, 76, 77, 80, 81, 84, 85, 90, 91, 94, 95, 128, 129, 132, 133, 138, 139, 142, 143, 146, 147, 150, 151, 152, 153, 156, 157, 192, 193, 196, 197, 202, 203, 206, 207, 210, 211, 214, 215, 216, 217, 220, 221]
private theorem finish0165Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0165Input1) = fromList finish0165Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0165 : finishSupport ⟨true, bits4 4⟩ support0775 = 1 • support0096 := by
  have hs : support0775 = fromList finish0165Input0 + fromList finish0165Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0165Chunk0, finish0165Chunk1]
  have hn : (finish0165Raw0 : Multiset ℕ) + (finish0165Raw1 : Multiset ℕ) = 1 • (supportNumbers0096 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0096] using hm

private def finish0166Input0 : List ℕ := [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85]
private def finish0166Raw0 : List ℕ := [0, 1, 16, 17, 64, 65, 80, 81]
private theorem finish0166Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0166Input0) = fromList finish0166Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0166 : finishSupport ⟨false, bits4 4⟩ support0777 = 1 • support0778 := by
  have hs : support0777 = fromList finish0166Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0166Chunk0]
  have hn : (finish0166Raw0 : Multiset ℕ) = 1 • (supportNumbers0778 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0778] using hm

private def finish0167Input0 : List ℕ := [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 514, 515, 518, 519, 530, 531, 534, 535, 578, 579, 582, 583, 594, 595, 598, 599]
private def finish0167Raw0 : List ℕ := [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 2, 3, 6, 7, 18, 19, 22, 23, 66, 67, 70, 71, 82, 83, 86, 87]
private theorem finish0167Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0167Input0) = fromList finish0167Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0167 : finishSupport ⟨true, bits4 4⟩ support0779 = 1 • support0092 := by
  have hs : support0779 = fromList finish0167Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0167Chunk0]
  have hn : (finish0167Raw0 : Multiset ℕ) = 1 • (supportNumbers0092 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0092] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
