import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0168Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 424, 425, 426, 427, 428, 429, 430, 431, 440, 441, 442, 443, 444, 445, 446, 447, 488, 489, 490, 491, 492, 493, 494, 495, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0168Raw0 : List ℕ := [0, 1, 2, 3, 16, 17, 18, 19, 64, 65, 66, 67, 80, 81, 82, 83, 172, 173, 174, 175, 188, 189, 190, 191, 236, 237, 238, 239, 252, 253, 254, 255]
private theorem finish0168Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0168Input0) = fromList finish0168Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0168 : finishSupport ⟨false, bits4 4⟩ support0781 = 1 • support0782 := by
  have hs : support0781 = fromList finish0168Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0168Chunk0]
  have hn : (finish0168Raw0 : Multiset ℕ) = 1 • (supportNumbers0782 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0782] using hm

private def finish0169Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 424, 425, 426, 427, 428, 429, 430, 431, 440, 441, 442, 443, 444, 445, 446, 447, 488, 489, 490, 491, 492, 493, 494, 495, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0169Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 168, 169, 170, 171, 172, 173, 174, 175, 184, 185, 186, 187, 188, 189, 190, 191, 232, 233, 234, 235, 236, 237, 238, 239, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0169Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0169Input0) = fromList finish0169Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0169Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599, 936, 937, 938, 939, 940, 941, 942, 943, 952, 953, 954, 955, 956, 957, 958, 959, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def finish0169Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 168, 169, 170, 171, 172, 173, 174, 175, 184, 185, 186, 187, 188, 189, 190, 191, 232, 233, 234, 235, 236, 237, 238, 239, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0169Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0169Input1) = fromList finish0169Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0169 : finishSupport ⟨true, bits4 4⟩ support0783 = 2 • support0784 := by
  have hs : support0783 = fromList finish0169Input0 + fromList finish0169Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0169Chunk0, finish0169Chunk1]
  have hn : (finish0169Raw0 : Multiset ℕ) + (finish0169Raw1 : Multiset ℕ) = 2 • (supportNumbers0784 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0784] using hm

private def finish0170Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0170Raw0 : List ℕ := [0, 1, 2, 3, 16, 17, 18, 19, 64, 65, 66, 67, 80, 81, 82, 83, 136, 137, 138, 139, 152, 153, 154, 155, 200, 201, 202, 203, 216, 217, 218, 219]
private theorem finish0170Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0170Input0) = fromList finish0170Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0170 : finishSupport ⟨false, bits4 4⟩ support0048 = 1 • support0785 := by
  have hs : support0048 = fromList finish0170Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0170Chunk0]
  have hn : (finish0170Raw0 : Multiset ℕ) = 1 • (supportNumbers0785 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0785] using hm

private def finish0171Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0171Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem finish0171Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0171Input0) = fromList finish0171Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0171Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599, 648, 649, 650, 651, 652, 653, 654, 655, 664, 665, 666, 667, 668, 669, 670, 671, 712, 713, 714, 715, 716, 717, 718, 719, 728, 729, 730, 731, 732, 733, 734, 735]
private def finish0171Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem finish0171Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0171Input1) = fromList finish0171Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0171 : finishSupport ⟨true, bits4 4⟩ support0049 = 2 • support0048 := by
  have hs : support0049 = fromList finish0171Input0 + fromList finish0171Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0171Chunk0, finish0171Chunk1]
  have hn : (finish0171Raw0 : Multiset ℕ) + (finish0171Raw1 : Multiset ℕ) = 2 • (supportNumbers0048 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0048] using hm

private def finish0172Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0172Raw0 : List ℕ := [0, 1, 2, 3, 16, 17, 18, 19, 64, 65, 66, 67, 80, 81, 82, 83, 136, 137, 138, 139, 152, 153, 154, 155, 200, 201, 202, 203, 216, 217, 218, 219]
private theorem finish0172Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0172Input0) = fromList finish0172Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0172Input1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 304, 305, 306, 307, 308, 309, 310, 311, 352, 353, 354, 355, 356, 357, 358, 359, 368, 369, 370, 371, 372, 373, 374, 375, 424, 425, 426, 427, 428, 429, 430, 431, 440, 441, 442, 443, 444, 445, 446, 447, 488, 489, 490, 491, 492, 493, 494, 495, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0172Raw1 : List ℕ := [36, 37, 38, 39, 52, 53, 54, 55, 100, 101, 102, 103, 116, 117, 118, 119, 172, 173, 174, 175, 188, 189, 190, 191, 236, 237, 238, 239, 252, 253, 254, 255]
private theorem finish0172Chunk1 : finishSupport ⟨false, bits4 4⟩ (fromList finish0172Input1) = fromList finish0172Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0172 : finishSupport ⟨false, bits4 4⟩ support0787 = 1 • support0788 := by
  have hs : support0787 = fromList finish0172Input0 + fromList finish0172Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0172Chunk0, finish0172Chunk1]
  have hn : (finish0172Raw0 : Multiset ℕ) + (finish0172Raw1 : Multiset ℕ) = 1 • (supportNumbers0788 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0788] using hm

private def finish0173Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0173Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem finish0173Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0173Input0) = fromList finish0173Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0173Input1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 304, 305, 306, 307, 308, 309, 310, 311, 352, 353, 354, 355, 356, 357, 358, 359, 368, 369, 370, 371, 372, 373, 374, 375, 424, 425, 426, 427, 428, 429, 430, 431, 440, 441, 442, 443, 444, 445, 446, 447, 488, 489, 490, 491, 492, 493, 494, 495, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0173Raw1 : List ℕ := [32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55, 96, 97, 98, 99, 100, 101, 102, 103, 112, 113, 114, 115, 116, 117, 118, 119, 168, 169, 170, 171, 172, 173, 174, 175, 184, 185, 186, 187, 188, 189, 190, 191, 232, 233, 234, 235, 236, 237, 238, 239, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0173Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0173Input1) = fromList finish0173Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0173Input2 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599, 648, 649, 650, 651, 652, 653, 654, 655, 664, 665, 666, 667, 668, 669, 670, 671, 712, 713, 714, 715, 716, 717, 718, 719, 728, 729, 730, 731, 732, 733, 734, 735]
private def finish0173Raw2 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem finish0173Chunk2 : finishSupport ⟨true, bits4 4⟩ (fromList finish0173Input2) = fromList finish0173Raw2 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0173Input3 : List ℕ := [800, 801, 802, 803, 804, 805, 806, 807, 816, 817, 818, 819, 820, 821, 822, 823, 864, 865, 866, 867, 868, 869, 870, 871, 880, 881, 882, 883, 884, 885, 886, 887, 936, 937, 938, 939, 940, 941, 942, 943, 952, 953, 954, 955, 956, 957, 958, 959, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def finish0173Raw3 : List ℕ := [32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55, 96, 97, 98, 99, 100, 101, 102, 103, 112, 113, 114, 115, 116, 117, 118, 119, 168, 169, 170, 171, 172, 173, 174, 175, 184, 185, 186, 187, 188, 189, 190, 191, 232, 233, 234, 235, 236, 237, 238, 239, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0173Chunk3 : finishSupport ⟨true, bits4 4⟩ (fromList finish0173Input3) = fromList finish0173Raw3 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0173 : finishSupport ⟨true, bits4 4⟩ support0789 = 2 • support0790 := by
  have hs : support0789 = fromList finish0173Input0 + fromList finish0173Input1 + fromList finish0173Input2 + fromList finish0173Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0173Chunk0, finish0173Chunk1, finish0173Chunk2, finish0173Chunk3]
  have hn : (finish0173Raw0 : Multiset ℕ) + (finish0173Raw1 : Multiset ℕ) + (finish0173Raw2 : Multiset ℕ) + (finish0173Raw3 : Multiset ℕ) = 2 • (supportNumbers0790 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0790] using hm

private def finish0174Input0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29, 64, 65, 68, 69, 72, 73, 76, 77, 80, 81, 84, 85, 88, 89, 92, 93, 128, 129, 132, 133, 136, 137, 140, 141, 144, 145, 148, 149, 152, 153, 156, 157, 192, 193, 196, 197, 200, 201, 204, 205, 208, 209, 212, 213, 216, 217, 220, 221]
private def finish0174Raw0 : List ℕ := [0, 1, 8, 9, 16, 17, 24, 25, 64, 65, 72, 73, 80, 81, 88, 89, 128, 129, 136, 137, 144, 145, 152, 153, 192, 193, 200, 201, 208, 209, 216, 217]
private theorem finish0174Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0174Input0) = fromList finish0174Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0174 : finishSupport ⟨false, bits4 4⟩ support0791 = 1 • support0792 := by
  have hs : support0791 = fromList finish0174Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0174Chunk0]
  have hn : (finish0174Raw0 : Multiset ℕ) = 1 • (supportNumbers0792 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0792] using hm

private def finish0175Input0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29, 64, 65, 68, 69, 72, 73, 76, 77, 80, 81, 84, 85, 88, 89, 92, 93, 128, 129, 132, 133, 136, 137, 140, 141, 144, 145, 148, 149, 152, 153, 156, 157, 192, 193, 196, 197, 200, 201, 204, 205, 208, 209, 212, 213, 216, 217, 220, 221]
private def finish0175Raw0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29, 64, 65, 68, 69, 72, 73, 76, 77, 80, 81, 84, 85, 88, 89, 92, 93, 128, 129, 132, 133, 136, 137, 140, 141, 144, 145, 148, 149, 152, 153, 156, 157, 192, 193, 196, 197, 200, 201, 204, 205, 208, 209, 212, 213, 216, 217, 220, 221]
private theorem finish0175Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0175Input0) = fromList finish0175Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0175Input1 : List ℕ := [514, 515, 518, 519, 522, 523, 526, 527, 530, 531, 534, 535, 538, 539, 542, 543, 578, 579, 582, 583, 586, 587, 590, 591, 594, 595, 598, 599, 602, 603, 606, 607, 642, 643, 646, 647, 650, 651, 654, 655, 658, 659, 662, 663, 666, 667, 670, 671, 706, 707, 710, 711, 714, 715, 718, 719, 722, 723, 726, 727, 730, 731, 734, 735]
private def finish0175Raw1 : List ℕ := [2, 3, 6, 7, 10, 11, 14, 15, 18, 19, 22, 23, 26, 27, 30, 31, 66, 67, 70, 71, 74, 75, 78, 79, 82, 83, 86, 87, 90, 91, 94, 95, 130, 131, 134, 135, 138, 139, 142, 143, 146, 147, 150, 151, 154, 155, 158, 159, 194, 195, 198, 199, 202, 203, 206, 207, 210, 211, 214, 215, 218, 219, 222, 223]
private theorem finish0175Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0175Input1) = fromList finish0175Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0175 : finishSupport ⟨true, bits4 4⟩ support0793 = 1 • support0096 := by
  have hs : support0793 = fromList finish0175Input0 + fromList finish0175Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0175Chunk0, finish0175Chunk1]
  have hn : (finish0175Raw0 : Multiset ℕ) + (finish0175Raw1 : Multiset ℕ) = 1 • (supportNumbers0096 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0096] using hm

private def finish0176Input0 : List ℕ := [0, 130]
private def finish0176Raw0 : List ℕ := [0, 130]
private theorem finish0176Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0176Input0) = fromList finish0176Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0176 : finishSupport ⟨false, bits4 4⟩ support0795 = 1 • support0795 := by
  have hs : support0795 = fromList finish0176Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0176Chunk0]
  have hn : (finish0176Raw0 : Multiset ℕ) = 1 • (supportNumbers0795 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0795] using hm

private def finish0177Input0 : List ℕ := [0, 130, 578, 704]
private def finish0177Raw0 : List ℕ := [0, 130, 66, 192]
private theorem finish0177Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0177Input0) = fromList finish0177Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0177 : finishSupport ⟨true, bits4 4⟩ support0796 = 1 • support0797 := by
  have hs : support0796 = fromList finish0177Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0177Chunk0]
  have hn : (finish0177Raw0 : Multiset ℕ) = 1 • (supportNumbers0797 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0797] using hm

private def finish0178Input0 : List ℕ := [0, 2, 128, 130, 288, 290, 416, 418]
private def finish0178Raw0 : List ℕ := [0, 2, 128, 130]
private theorem finish0178Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0178Input0) = fromList finish0178Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0178 : finishSupport ⟨false, bits4 4⟩ support0799 = 1 • support0252 := by
  have hs : support0799 = fromList finish0178Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0178Chunk0]
  have hn : (finish0178Raw0 : Multiset ℕ) = 1 • (supportNumbers0252 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0252] using hm

private def finish0179Input0 : List ℕ := [0, 2, 128, 130, 288, 290, 416, 418, 576, 578, 704, 706, 864, 866, 992, 994]
private def finish0179Raw0 : List ℕ := [0, 2, 128, 130, 32, 34, 160, 162, 64, 66, 192, 194, 96, 98, 224, 226]
private theorem finish0179Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0179Input0) = fromList finish0179Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0179 : finishSupport ⟨true, bits4 4⟩ support0800 = 1 • support0801 := by
  have hs : support0800 = fromList finish0179Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0179Chunk0]
  have hn : (finish0179Raw0 : Multiset ℕ) = 1 • (supportNumbers0801 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0801] using hm

private def finish0180Input0 : List ℕ := [0, 2, 424, 426]
private def finish0180Raw0 : List ℕ := [0, 2]
private theorem finish0180Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0180Input0) = fromList finish0180Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0180 : finishSupport ⟨false, bits4 4⟩ support0803 = 1 • support0008 := by
  have hs : support0803 = fromList finish0180Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0180Chunk0]
  have hn : (finish0180Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
