import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0263Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366, 417, 419, 421, 423, 424, 426, 428, 430, 480, 482, 484, 486, 489, 491, 493, 495]
private def finish0263Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 32, 34, 36, 38, 41, 43, 45, 47, 97, 99, 101, 103, 104, 106, 108, 110, 161, 163, 165, 167, 168, 170, 172, 174, 224, 226, 228, 230, 233, 235, 237, 239]
private theorem finish0263Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0263Input0) = fromList finish0263Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0263Input1 : List ℕ := [513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 801, 803, 805, 807, 808, 810, 812, 814, 864, 866, 868, 870, 873, 875, 877, 879, 928, 930, 932, 934, 937, 939, 941, 943, 993, 995, 997, 999, 1000, 1002, 1004, 1006]
private def finish0263Raw1 : List ℕ := [1, 3, 5, 7, 8, 10, 12, 14, 64, 66, 68, 70, 73, 75, 77, 79, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 33, 35, 37, 39, 40, 42, 44, 46, 96, 98, 100, 102, 105, 107, 109, 111, 160, 162, 164, 166, 169, 171, 173, 175, 225, 227, 229, 231, 232, 234, 236, 238]
private theorem finish0263Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0263Input1) = fromList finish0263Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0263 : finishSupport ⟨true, bits4 4⟩ support0959 = 1 • support0527 := by
  have hs : support0959 = fromList finish0263Input0 + fromList finish0263Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0263Chunk0, finish0263Chunk1]
  have hn : (finish0263Raw0 : Multiset ℕ) + (finish0263Raw1 : Multiset ℕ) = 1 • (supportNumbers0527 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0527] using hm

private def finish0264Input0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77, 128, 129, 132, 133, 136, 137, 140, 141, 192, 193, 196, 197, 200, 201, 204, 205]
private def finish0264Raw0 : List ℕ := [0, 1, 8, 9, 64, 65, 72, 73, 128, 129, 136, 137, 192, 193, 200, 201]
private theorem finish0264Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0264Input0) = fromList finish0264Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0264 : finishSupport ⟨false, bits4 4⟩ support0960 = 1 • support0961 := by
  have hs : support0960 = fromList finish0264Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0264Chunk0]
  have hn : (finish0264Raw0 : Multiset ℕ) = 1 • (supportNumbers0961 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0961] using hm

private def finish0265Input0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77, 128, 129, 132, 133, 136, 137, 140, 141, 192, 193, 196, 197, 200, 201, 204, 205, 514, 515, 518, 519, 522, 523, 526, 527, 578, 579, 582, 583, 586, 587, 590, 591, 642, 643, 646, 647, 650, 651, 654, 655, 706, 707, 710, 711, 714, 715, 718, 719]
private def finish0265Raw0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77, 128, 129, 132, 133, 136, 137, 140, 141, 192, 193, 196, 197, 200, 201, 204, 205, 2, 3, 6, 7, 10, 11, 14, 15, 66, 67, 70, 71, 74, 75, 78, 79, 130, 131, 134, 135, 138, 139, 142, 143, 194, 195, 198, 199, 202, 203, 206, 207]
private theorem finish0265Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0265Input0) = fromList finish0265Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0265 : finishSupport ⟨true, bits4 4⟩ support0962 = 1 • support0148 := by
  have hs : support0962 = fromList finish0265Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0265Chunk0]
  have hn : (finish0265Raw0 : Multiset ℕ) = 1 • (supportNumbers0148 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0148] using hm

private def finish0266Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359]
private def finish0266Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 36, 37, 38, 39, 100, 101, 102, 103]
private theorem finish0266Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0266Input0) = fromList finish0266Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0266 : finishSupport ⟨false, bits4 4⟩ support0965 = 1 • support0966 := by
  have hs : support0965 = fromList finish0266Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0266Chunk0]
  have hn : (finish0266Raw0 : Multiset ℕ) = 1 • (supportNumbers0966 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0966] using hm

private def finish0267Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 800, 801, 802, 803, 804, 805, 806, 807, 864, 865, 866, 867, 868, 869, 870, 871]
private def finish0267Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 32, 33, 34, 35, 36, 37, 38, 39, 96, 97, 98, 99, 100, 101, 102, 103, 0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 32, 33, 34, 35, 36, 37, 38, 39, 96, 97, 98, 99, 100, 101, 102, 103]
private theorem finish0267Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0267Input0) = fromList finish0267Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0267 : finishSupport ⟨true, bits4 4⟩ support0967 = 2 • support0725 := by
  have hs : support0967 = fromList finish0267Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0267Chunk0]
  have hn : (finish0267Raw0 : Multiset ℕ) = 2 • (supportNumbers0725 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0725] using hm

private def finish0268Input0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 152, 153, 156, 157, 216, 217, 220, 221]
private def finish0268Raw0 : List ℕ := [0, 1, 64, 65, 152, 153, 216, 217]
private theorem finish0268Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0268Input0) = fromList finish0268Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0268 : finishSupport ⟨false, bits4 4⟩ support0968 = 1 • support0969 := by
  have hs : support0968 = fromList finish0268Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0268Chunk0]
  have hn : (finish0268Raw0 : Multiset ℕ) = 1 • (supportNumbers0969 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0969] using hm

private def finish0269Input0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 152, 153, 156, 157, 216, 217, 220, 221, 514, 515, 518, 519, 578, 579, 582, 583, 666, 667, 670, 671, 730, 731, 734, 735]
private def finish0269Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 152, 153, 156, 157, 216, 217, 220, 221, 2, 3, 6, 7, 66, 67, 70, 71, 154, 155, 158, 159, 218, 219, 222, 223]
private theorem finish0269Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0269Input0) = fromList finish0269Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0269 : finishSupport ⟨true, bits4 4⟩ support0970 = 1 • support0151 := by
  have hs : support0970 = fromList finish0269Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0269Chunk0]
  have hn : (finish0269Raw0 : Multiset ℕ) = 1 • (supportNumbers0151 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0151] using hm

private def finish0270Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0270Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 152, 153, 154, 155, 216, 217, 218, 219]
private theorem finish0270Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0270Input0) = fromList finish0270Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0270 : finishSupport ⟨false, bits4 4⟩ support0151 = 1 • support0971 := by
  have hs : support0151 = fromList finish0270Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0270Chunk0]
  have hn : (finish0270Raw0 : Multiset ℕ) = 1 • (supportNumbers0971 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0971] using hm

private def finish0271Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735]
private def finish0271Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem finish0271Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0271Input0) = fromList finish0271Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0271 : finishSupport ⟨true, bits4 4⟩ support0446 = 2 • support0151 := by
  have hs : support0446 = fromList finish0271Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0271Chunk0]
  have hn : (finish0271Raw0 : Multiset ℕ) = 2 • (supportNumbers0151 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0151] using hm

private def finish0272Input0 : List ℕ := [0, 1, 4, 5, 26, 27, 30, 31, 64, 65, 68, 69, 90, 91, 94, 95, 130, 131, 134, 135, 152, 153, 156, 157, 194, 195, 198, 199, 216, 217, 220, 221]
private def finish0272Raw0 : List ℕ := [0, 1, 26, 27, 64, 65, 90, 91, 130, 131, 152, 153, 194, 195, 216, 217]
private theorem finish0272Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0272Input0) = fromList finish0272Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0272 : finishSupport ⟨false, bits4 4⟩ support0972 = 1 • support0973 := by
  have hs : support0972 = fromList finish0272Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0272Chunk0]
  have hn : (finish0272Raw0 : Multiset ℕ) = 1 • (supportNumbers0973 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0973] using hm

private def finish0273Input0 : List ℕ := [0, 1, 4, 5, 26, 27, 30, 31, 64, 65, 68, 69, 90, 91, 94, 95, 130, 131, 134, 135, 152, 153, 156, 157, 194, 195, 198, 199, 216, 217, 220, 221, 514, 515, 518, 519, 536, 537, 540, 541, 578, 579, 582, 583, 600, 601, 604, 605, 640, 641, 644, 645, 666, 667, 670, 671, 704, 705, 708, 709, 730, 731, 734, 735]
private def finish0273Raw0 : List ℕ := [0, 1, 4, 5, 26, 27, 30, 31, 64, 65, 68, 69, 90, 91, 94, 95, 130, 131, 134, 135, 152, 153, 156, 157, 194, 195, 198, 199, 216, 217, 220, 221, 2, 3, 6, 7, 24, 25, 28, 29, 66, 67, 70, 71, 88, 89, 92, 93, 128, 129, 132, 133, 154, 155, 158, 159, 192, 193, 196, 197, 218, 219, 222, 223]
private theorem finish0273Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0273Input0) = fromList finish0273Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0273 : finishSupport ⟨true, bits4 4⟩ support0974 = 1 • support0326 := by
  have hs : support0974 = fromList finish0273Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0273Chunk0]
  have hn : (finish0273Raw0 : Multiset ℕ) = 1 • (supportNumbers0326 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0326] using hm

private def finish0274Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0274Raw0 : List ℕ := [0, 1, 2, 3, 24, 25, 26, 27, 64, 65, 66, 67, 88, 89, 90, 91, 128, 129, 130, 131, 152, 153, 154, 155, 192, 193, 194, 195, 216, 217, 218, 219]
private theorem finish0274Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0274Input0) = fromList finish0274Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0274Input1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 312, 313, 314, 315, 316, 317, 318, 319, 352, 353, 354, 355, 356, 357, 358, 359, 376, 377, 378, 379, 380, 381, 382, 383, 416, 417, 418, 419, 420, 421, 422, 423, 440, 441, 442, 443, 444, 445, 446, 447, 480, 481, 482, 483, 484, 485, 486, 487, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0274Raw1 : List ℕ := [36, 37, 38, 39, 60, 61, 62, 63, 100, 101, 102, 103, 124, 125, 126, 127, 164, 165, 166, 167, 188, 189, 190, 191, 228, 229, 230, 231, 252, 253, 254, 255]
private theorem finish0274Chunk1 : finishSupport ⟨false, bits4 4⟩ (fromList finish0274Input1) = fromList finish0274Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0274 : finishSupport ⟨false, bits4 4⟩ support0976 = 1 • support0977 := by
  have hs : support0976 = fromList finish0274Input0 + fromList finish0274Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0274Chunk0, finish0274Chunk1]
  have hn : (finish0274Raw0 : Multiset ℕ) + (finish0274Raw1 : Multiset ℕ) = 1 • (supportNumbers0977 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0977] using hm

private def finish0275Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0275Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem finish0275Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0275Input0) = fromList finish0275Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0275Input1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 312, 313, 314, 315, 316, 317, 318, 319, 352, 353, 354, 355, 356, 357, 358, 359, 376, 377, 378, 379, 380, 381, 382, 383, 416, 417, 418, 419, 420, 421, 422, 423, 440, 441, 442, 443, 444, 445, 446, 447, 480, 481, 482, 483, 484, 485, 486, 487, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0275Raw1 : List ℕ := [32, 33, 34, 35, 36, 37, 38, 39, 56, 57, 58, 59, 60, 61, 62, 63, 96, 97, 98, 99, 100, 101, 102, 103, 120, 121, 122, 123, 124, 125, 126, 127, 160, 161, 162, 163, 164, 165, 166, 167, 184, 185, 186, 187, 188, 189, 190, 191, 224, 225, 226, 227, 228, 229, 230, 231, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0275Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0275Input1) = fromList finish0275Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0275Input2 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735]
private def finish0275Raw2 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem finish0275Chunk2 : finishSupport ⟨true, bits4 4⟩ (fromList finish0275Input2) = fromList finish0275Raw2 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0275Input3 : List ℕ := [800, 801, 802, 803, 804, 805, 806, 807, 824, 825, 826, 827, 828, 829, 830, 831, 864, 865, 866, 867, 868, 869, 870, 871, 888, 889, 890, 891, 892, 893, 894, 895, 928, 929, 930, 931, 932, 933, 934, 935, 952, 953, 954, 955, 956, 957, 958, 959, 992, 993, 994, 995, 996, 997, 998, 999, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def finish0275Raw3 : List ℕ := [32, 33, 34, 35, 36, 37, 38, 39, 56, 57, 58, 59, 60, 61, 62, 63, 96, 97, 98, 99, 100, 101, 102, 103, 120, 121, 122, 123, 124, 125, 126, 127, 160, 161, 162, 163, 164, 165, 166, 167, 184, 185, 186, 187, 188, 189, 190, 191, 224, 225, 226, 227, 228, 229, 230, 231, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0275Chunk3 : finishSupport ⟨true, bits4 4⟩ (fromList finish0275Input3) = fromList finish0275Raw3 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0275 : finishSupport ⟨true, bits4 4⟩ support0978 = 2 • support0979 := by
  have hs : support0978 = fromList finish0275Input0 + fromList finish0275Input1 + fromList finish0275Input2 + fromList finish0275Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0275Chunk0, finish0275Chunk1, finish0275Chunk2, finish0275Chunk3]
  have hn : (finish0275Raw0 : Multiset ℕ) + (finish0275Raw1 : Multiset ℕ) + (finish0275Raw2 : Multiset ℕ) + (finish0275Raw3 : Multiset ℕ) = 2 • (supportNumbers0979 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0979] using hm

private def finish0276Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495]
private def finish0276Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 172, 173, 174, 175, 236, 237, 238, 239]
private theorem finish0276Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0276Input0) = fromList finish0276Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0276 : finishSupport ⟨false, bits4 4⟩ support0981 = 1 • support0982 := by
  have hs : support0981 = fromList finish0276Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0276Chunk0]
  have hn : (finish0276Raw0 : Multiset ℕ) = 1 • (supportNumbers0982 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0982] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
