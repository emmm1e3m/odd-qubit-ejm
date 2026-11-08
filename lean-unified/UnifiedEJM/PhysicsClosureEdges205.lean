import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0412Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0412Raw0 : List ℕ := [0, 1, 2, 3, 24, 25, 26, 27, 64, 65, 66, 67, 88, 89, 90, 91, 128, 129, 130, 131, 152, 153, 154, 155, 192, 193, 194, 195, 216, 217, 218, 219]
private theorem finish0412Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0412Input0) = fromList finish0412Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0412 : finishSupport ⟨false, bits4 4⟩ support0326 = 1 • support1217 := by
  have hs : support0326 = fromList finish0412Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0412Chunk0]
  have hn : (finish0412Raw0 : Multiset ℕ) = 1 • (supportNumbers1217 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1217] using hm

private def finish0413Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0413Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem finish0413Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0413Input0) = fromList finish0413Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0413Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735]
private def finish0413Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem finish0413Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0413Input1) = fromList finish0413Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0413 : finishSupport ⟨true, bits4 4⟩ support0327 = 2 • support0326 := by
  have hs : support0327 = fromList finish0413Input0 + fromList finish0413Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0413Chunk0, finish0413Chunk1]
  have hn : (finish0413Raw0 : Multiset ℕ) + (finish0413Raw1 : Multiset ℕ) = 2 • (supportNumbers0326 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0326] using hm

private def finish0414Input0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 64, 65, 68, 69, 74, 75, 78, 79]
private def finish0414Raw0 : List ℕ := [0, 1, 10, 11, 64, 65, 74, 75]
private theorem finish0414Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0414Input0) = fromList finish0414Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0414 : finishSupport ⟨false, bits4 4⟩ support1219 = 1 • support1220 := by
  have hs : support1219 = fromList finish0414Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0414Chunk0]
  have hn : (finish0414Raw0 : Multiset ℕ) = 1 • (supportNumbers1220 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1220] using hm

private def finish0415Input0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 64, 65, 68, 69, 74, 75, 78, 79, 514, 515, 518, 519, 520, 521, 524, 525, 578, 579, 582, 583, 584, 585, 588, 589]
private def finish0415Raw0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 64, 65, 68, 69, 74, 75, 78, 79, 2, 3, 6, 7, 8, 9, 12, 13, 66, 67, 70, 71, 72, 73, 76, 77]
private theorem finish0415Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0415Input0) = fromList finish0415Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0415 : finishSupport ⟨true, bits4 4⟩ support1221 = 1 • support0222 := by
  have hs : support1221 = fromList finish0415Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0415Chunk0]
  have hn : (finish0415Raw0 : Multiset ℕ) = 1 • (supportNumbers0222 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0222] using hm

private def finish0416Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]
private def finish0416Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 64, 65, 66, 67, 72, 73, 74, 75, 36, 37, 38, 39, 44, 45, 46, 47, 100, 101, 102, 103, 108, 109, 110, 111]
private theorem finish0416Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0416Input0) = fromList finish0416Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0416 : finishSupport ⟨false, bits4 4⟩ support1223 = 1 • support1224 := by
  have hs : support1223 = fromList finish0416Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0416Chunk0]
  have hn : (finish0416Raw0 : Multiset ℕ) = 1 • (supportNumbers1224 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1224] using hm

private def finish0417Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]
private def finish0417Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]
private theorem finish0417Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0417Input0) = fromList finish0417Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0417Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]
private def finish0417Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]
private theorem finish0417Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0417Input1) = fromList finish0417Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0417 : finishSupport ⟨true, bits4 4⟩ support1225 = 2 • support0938 := by
  have hs : support1225 = fromList finish0417Input0 + fromList finish0417Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0417Chunk0, finish0417Chunk1]
  have hn : (finish0417Raw0 : Multiset ℕ) + (finish0417Raw1 : Multiset ℕ) = 2 • (supportNumbers0938 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0938] using hm

private def finish0418Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 304, 305, 306, 307, 308, 309, 310, 311, 368, 369, 370, 371, 372, 373, 374, 375, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495]
private def finish0418Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 152, 153, 154, 155, 216, 217, 218, 219, 52, 53, 54, 55, 116, 117, 118, 119, 172, 173, 174, 175, 236, 237, 238, 239]
private theorem finish0418Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0418Input0) = fromList finish0418Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0418 : finishSupport ⟨false, bits4 4⟩ support1227 = 1 • support1228 := by
  have hs : support1227 = fromList finish0418Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0418Chunk0]
  have hn : (finish0418Raw0 : Multiset ℕ) = 1 • (supportNumbers1228 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1228] using hm

private def finish0419Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 304, 305, 306, 307, 308, 309, 310, 311, 368, 369, 370, 371, 372, 373, 374, 375, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495]
private def finish0419Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 48, 49, 50, 51, 52, 53, 54, 55, 112, 113, 114, 115, 116, 117, 118, 119, 168, 169, 170, 171, 172, 173, 174, 175, 232, 233, 234, 235, 236, 237, 238, 239]
private theorem finish0419Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0419Input0) = fromList finish0419Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0419Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735, 816, 817, 818, 819, 820, 821, 822, 823, 880, 881, 882, 883, 884, 885, 886, 887, 936, 937, 938, 939, 940, 941, 942, 943, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]
private def finish0419Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 48, 49, 50, 51, 52, 53, 54, 55, 112, 113, 114, 115, 116, 117, 118, 119, 168, 169, 170, 171, 172, 173, 174, 175, 232, 233, 234, 235, 236, 237, 238, 239]
private theorem finish0419Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0419Input1) = fromList finish0419Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0419 : finishSupport ⟨true, bits4 4⟩ support1229 = 2 • support1230 := by
  have hs : support1229 = fromList finish0419Input0 + fromList finish0419Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0419Chunk0, finish0419Chunk1]
  have hn : (finish0419Raw0 : Multiset ℕ) + (finish0419Raw1 : Multiset ℕ) = 2 • (supportNumbers1230 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1230] using hm

private def finish0420Input0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 144, 145, 148, 149, 208, 209, 212, 213]
private def finish0420Raw0 : List ℕ := [0, 1, 64, 65, 144, 145, 208, 209]
private theorem finish0420Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0420Input0) = fromList finish0420Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0420 : finishSupport ⟨false, bits4 4⟩ support1231 = 1 • support1232 := by
  have hs : support1231 = fromList finish0420Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0420Chunk0]
  have hn : (finish0420Raw0 : Multiset ℕ) = 1 • (supportNumbers1232 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1232] using hm

private def finish0421Input0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 144, 145, 148, 149, 208, 209, 212, 213, 514, 515, 518, 519, 578, 579, 582, 583, 658, 659, 662, 663, 722, 723, 726, 727]
private def finish0421Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 144, 145, 148, 149, 208, 209, 212, 213, 2, 3, 6, 7, 66, 67, 70, 71, 146, 147, 150, 151, 210, 211, 214, 215]
private theorem finish0421Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0421Input0) = fromList finish0421Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0421 : finishSupport ⟨true, bits4 4⟩ support1233 = 1 • support0241 := by
  have hs : support1233 = fromList finish0421Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0421Chunk0]
  have hn : (finish0421Raw0 : Multiset ℕ) = 1 • (supportNumbers0241 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0241] using hm

private def finish0422Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 296, 297, 298, 299, 300, 301, 302, 303, 360, 361, 362, 363, 364, 365, 366, 367, 440, 441, 442, 443, 444, 445, 446, 447, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0422Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 144, 145, 146, 147, 208, 209, 210, 211, 44, 45, 46, 47, 108, 109, 110, 111, 188, 189, 190, 191, 252, 253, 254, 255]
private theorem finish0422Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0422Input0) = fromList finish0422Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0422 : finishSupport ⟨false, bits4 4⟩ support1235 = 1 • support1236 := by
  have hs : support1235 = fromList finish0422Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0422Chunk0]
  have hn : (finish0422Raw0 : Multiset ℕ) = 1 • (supportNumbers1236 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1236] using hm

private def finish0423Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 296, 297, 298, 299, 300, 301, 302, 303, 360, 361, 362, 363, 364, 365, 366, 367, 440, 441, 442, 443, 444, 445, 446, 447, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0423Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 40, 41, 42, 43, 44, 45, 46, 47, 104, 105, 106, 107, 108, 109, 110, 111, 184, 185, 186, 187, 188, 189, 190, 191, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0423Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0423Input0) = fromList finish0423Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0423Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 656, 657, 658, 659, 660, 661, 662, 663, 720, 721, 722, 723, 724, 725, 726, 727, 808, 809, 810, 811, 812, 813, 814, 815, 872, 873, 874, 875, 876, 877, 878, 879, 952, 953, 954, 955, 956, 957, 958, 959, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def finish0423Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 40, 41, 42, 43, 44, 45, 46, 47, 104, 105, 106, 107, 108, 109, 110, 111, 184, 185, 186, 187, 188, 189, 190, 191, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0423Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0423Input1) = fromList finish0423Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0423 : finishSupport ⟨true, bits4 4⟩ support1237 = 2 • support1238 := by
  have hs : support1237 = fromList finish0423Input0 + fromList finish0423Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0423Chunk0, finish0423Chunk1]
  have hn : (finish0423Raw0 : Multiset ℕ) + (finish0423Raw1 : Multiset ℕ) = 2 • (supportNumbers1238 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1238] using hm

private def finish0424Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0424Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 64, 65, 66, 67, 72, 73, 74, 75, 144, 145, 146, 147, 152, 153, 154, 155, 208, 209, 210, 211, 216, 217, 218, 219]
private theorem finish0424Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0424Input0) = fromList finish0424Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0424 : finishSupport ⟨false, bits4 4⟩ support0157 = 1 • support1239 := by
  have hs : support0157 = fromList finish0424Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0424Chunk0]
  have hn : (finish0424Raw0 : Multiset ℕ) = 1 • (supportNumbers1239 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1239] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
