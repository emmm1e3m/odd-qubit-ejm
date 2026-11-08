import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0025Input0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 514, 515, 518, 519, 538, 539, 542, 543, 578, 579, 582, 583, 602, 603, 606, 607]
private def finish0025Raw0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 2, 3, 6, 7, 26, 27, 30, 31, 66, 67, 70, 71, 90, 91, 94, 95]
private theorem finish0025Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0025Input0) = fromList finish0025Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0025 : finishSupport ⟨true, bits4 4⟩ support0530 = 1 • support0020 := by
  have hs : support0530 = fromList finish0025Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0025Chunk0]
  have hn : (finish0025Raw0 : Multiset ℕ) = 1 • (supportNumbers0020 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0020] using hm

private def finish0026Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375]
private def finish0026Raw0 : List ℕ := [0, 1, 2, 3, 24, 25, 26, 27, 64, 65, 66, 67, 88, 89, 90, 91, 44, 45, 46, 47, 52, 53, 54, 55, 108, 109, 110, 111, 116, 117, 118, 119]
private theorem finish0026Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0026Input0) = fromList finish0026Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0026 : finishSupport ⟨false, bits4 4⟩ support0532 = 1 • support0533 := by
  have hs : support0532 = fromList finish0026Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0026Chunk0]
  have hn : (finish0026Raw0 : Multiset ℕ) = 1 • (supportNumbers0533 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0533] using hm

private def finish0027Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375]
private def finish0027Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]
private theorem finish0027Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0027Input0) = fromList finish0027Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0027Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887]
private def finish0027Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]
private theorem finish0027Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0027Input1) = fromList finish0027Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0027 : finishSupport ⟨true, bits4 4⟩ support0534 = 2 • support0535 := by
  have hs : support0534 = fromList finish0027Input0 + fromList finish0027Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0027Chunk0, finish0027Chunk1]
  have hn : (finish0027Raw0 : Multiset ℕ) + (finish0027Raw1 : Multiset ℕ) = 2 • (supportNumbers0535 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0535] using hm

private def finish0028Input0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29, 64, 65, 68, 69, 72, 73, 76, 77, 80, 81, 84, 85, 88, 89, 92, 93, 130, 131, 134, 135, 138, 139, 142, 143, 146, 147, 150, 151, 154, 155, 158, 159, 194, 195, 198, 199, 202, 203, 206, 207, 210, 211, 214, 215, 218, 219, 222, 223]
private def finish0028Raw0 : List ℕ := [0, 1, 8, 9, 16, 17, 24, 25, 64, 65, 72, 73, 80, 81, 88, 89, 130, 131, 138, 139, 146, 147, 154, 155, 194, 195, 202, 203, 210, 211, 218, 219]
private theorem finish0028Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0028Input0) = fromList finish0028Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0028 : finishSupport ⟨false, bits4 4⟩ support0536 = 1 • support0537 := by
  have hs : support0536 = fromList finish0028Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0028Chunk0]
  have hn : (finish0028Raw0 : Multiset ℕ) = 1 • (supportNumbers0537 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0537] using hm

private def finish0029Input0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29, 64, 65, 68, 69, 72, 73, 76, 77, 80, 81, 84, 85, 88, 89, 92, 93, 130, 131, 134, 135, 138, 139, 142, 143, 146, 147, 150, 151, 154, 155, 158, 159, 194, 195, 198, 199, 202, 203, 206, 207, 210, 211, 214, 215, 218, 219, 222, 223]
private def finish0029Raw0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29, 64, 65, 68, 69, 72, 73, 76, 77, 80, 81, 84, 85, 88, 89, 92, 93, 130, 131, 134, 135, 138, 139, 142, 143, 146, 147, 150, 151, 154, 155, 158, 159, 194, 195, 198, 199, 202, 203, 206, 207, 210, 211, 214, 215, 218, 219, 222, 223]
private theorem finish0029Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0029Input0) = fromList finish0029Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0029Input1 : List ℕ := [514, 515, 518, 519, 522, 523, 526, 527, 530, 531, 534, 535, 538, 539, 542, 543, 578, 579, 582, 583, 586, 587, 590, 591, 594, 595, 598, 599, 602, 603, 606, 607, 640, 641, 644, 645, 648, 649, 652, 653, 656, 657, 660, 661, 664, 665, 668, 669, 704, 705, 708, 709, 712, 713, 716, 717, 720, 721, 724, 725, 728, 729, 732, 733]
private def finish0029Raw1 : List ℕ := [2, 3, 6, 7, 10, 11, 14, 15, 18, 19, 22, 23, 26, 27, 30, 31, 66, 67, 70, 71, 74, 75, 78, 79, 82, 83, 86, 87, 90, 91, 94, 95, 128, 129, 132, 133, 136, 137, 140, 141, 144, 145, 148, 149, 152, 153, 156, 157, 192, 193, 196, 197, 200, 201, 204, 205, 208, 209, 212, 213, 216, 217, 220, 221]
private theorem finish0029Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0029Input1) = fromList finish0029Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0029 : finishSupport ⟨true, bits4 4⟩ support0538 = 1 • support0096 := by
  have hs : support0538 = fromList finish0029Input0 + fromList finish0029Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0029Chunk0, finish0029Chunk1]
  have hn : (finish0029Raw0 : Multiset ℕ) + (finish0029Raw1 : Multiset ℕ) = 1 • (supportNumbers0096 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0096] using hm

private def finish0030Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def finish0030Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27, 64, 65, 66, 67, 72, 73, 74, 75, 80, 81, 82, 83, 88, 89, 90, 91]
private theorem finish0030Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0030Input0) = fromList finish0030Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0030Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0030Raw1 : List ℕ := [128, 129, 130, 131, 136, 137, 138, 139, 144, 145, 146, 147, 152, 153, 154, 155, 192, 193, 194, 195, 200, 201, 202, 203, 208, 209, 210, 211, 216, 217, 218, 219]
private theorem finish0030Chunk1 : finishSupport ⟨false, bits4 4⟩ (fromList finish0030Input1) = fromList finish0030Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0030Input2 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]
private def finish0030Raw2 : List ℕ := [36, 37, 38, 39, 44, 45, 46, 47, 52, 53, 54, 55, 60, 61, 62, 63, 100, 101, 102, 103, 108, 109, 110, 111, 116, 117, 118, 119, 124, 125, 126, 127]
private theorem finish0030Chunk2 : finishSupport ⟨false, bits4 4⟩ (fromList finish0030Input2) = fromList finish0030Raw2 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0030Input3 : List ℕ := [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0030Raw3 : List ℕ := [164, 165, 166, 167, 172, 173, 174, 175, 180, 181, 182, 183, 188, 189, 190, 191, 228, 229, 230, 231, 236, 237, 238, 239, 244, 245, 246, 247, 252, 253, 254, 255]
private theorem finish0030Chunk3 : finishSupport ⟨false, bits4 4⟩ (fromList finish0030Input3) = fromList finish0030Raw3 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0030 : finishSupport ⟨false, bits4 4⟩ support0540 = 1 • support0541 := by
  have hs : support0540 = fromList finish0030Input0 + fromList finish0030Input1 + fromList finish0030Input2 + fromList finish0030Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0030Chunk0, finish0030Chunk1, finish0030Chunk2, finish0030Chunk3]
  have hn : (finish0030Raw0 : Multiset ℕ) + (finish0030Raw1 : Multiset ℕ) + (finish0030Raw2 : Multiset ℕ) + (finish0030Raw3 : Multiset ℕ) = 1 • (supportNumbers0541 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0541] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
