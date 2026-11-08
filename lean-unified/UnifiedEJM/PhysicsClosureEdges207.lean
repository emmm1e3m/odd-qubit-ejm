import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0434Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def finish0434Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27, 64, 65, 66, 67, 72, 73, 74, 75, 80, 81, 82, 83, 88, 89, 90, 91]
private theorem finish0434Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0434Input0) = fromList finish0434Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0434Input1 : List ℕ := [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0434Raw1 : List ℕ := [164, 165, 166, 167, 172, 173, 174, 175, 180, 181, 182, 183, 188, 189, 190, 191, 228, 229, 230, 231, 236, 237, 238, 239, 244, 245, 246, 247, 252, 253, 254, 255]
private theorem finish0434Chunk1 : finishSupport ⟨false, bits4 4⟩ (fromList finish0434Input1) = fromList finish0434Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0434 : finishSupport ⟨false, bits4 4⟩ support1255 = 1 • support1256 := by
  have hs : support1255 = fromList finish0434Input0 + fromList finish0434Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0434Chunk0, finish0434Chunk1]
  have hn : (finish0434Raw0 : Multiset ℕ) + (finish0434Raw1 : Multiset ℕ) = 1 • (supportNumbers1256 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1256] using hm

private def finish0435Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def finish0435Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem finish0435Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0435Input0) = fromList finish0435Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0435Input1 : List ℕ := [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0435Raw1 : List ℕ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0435Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0435Input1) = fromList finish0435Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0435Input2 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]
private def finish0435Raw2 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem finish0435Chunk2 : finishSupport ⟨true, bits4 4⟩ (fromList finish0435Input2) = fromList finish0435Raw2 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0435Input3 : List ℕ := [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def finish0435Raw3 : List ℕ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0435Chunk3 : finishSupport ⟨true, bits4 4⟩ (fromList finish0435Input3) = fromList finish0435Raw3 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0435 : finishSupport ⟨true, bits4 4⟩ support1257 = 2 • support1258 := by
  have hs : support1257 = fromList finish0435Input0 + fromList finish0435Input1 + fromList finish0435Input2 + fromList finish0435Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0435Chunk0, finish0435Chunk1, finish0435Chunk2, finish0435Chunk3]
  have hn : (finish0435Raw0 : Multiset ℕ) + (finish0435Raw1 : Multiset ℕ) + (finish0435Raw2 : Multiset ℕ) + (finish0435Raw3 : Multiset ℕ) = 2 • (supportNumbers1258 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1258] using hm

private def finish0436Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private def finish0436Raw0 : List ℕ := [0, 1, 2, 3, 16, 17, 18, 19, 64, 65, 66, 67, 80, 81, 82, 83, 128, 129, 130, 131, 144, 145, 146, 147, 192, 193, 194, 195, 208, 209, 210, 211]
private theorem finish0436Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0436Input0) = fromList finish0436Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0436 : finishSupport ⟨false, bits4 4⟩ support0164 = 1 • support1259 := by
  have hs : support0164 = fromList finish0436Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0436Chunk0]
  have hn : (finish0436Raw0 : Multiset ℕ) = 1 • (supportNumbers1259 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1259] using hm

private def finish0437Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private def finish0437Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem finish0437Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0437Input0) = fromList finish0437Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0437Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599, 640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727]
private def finish0437Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem finish0437Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0437Input1) = fromList finish0437Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0437 : finishSupport ⟨true, bits4 4⟩ support0343 = 2 • support0164 := by
  have hs : support0343 = fromList finish0437Input0 + fromList finish0437Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0437Chunk0, finish0437Chunk1]
  have hn : (finish0437Raw0 : Multiset ℕ) + (finish0437Raw1 : Multiset ℕ) = 2 • (supportNumbers0164 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0164] using hm

private def finish0438Input0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 16, 17, 20, 21, 26, 27, 30, 31, 64, 65, 68, 69, 74, 75, 78, 79, 80, 81, 84, 85, 90, 91, 94, 95, 128, 129, 132, 133, 138, 139, 142, 143, 144, 145, 148, 149, 154, 155, 158, 159, 192, 193, 196, 197, 202, 203, 206, 207, 208, 209, 212, 213, 218, 219, 222, 223]
private def finish0438Raw0 : List ℕ := [0, 1, 10, 11, 16, 17, 26, 27, 64, 65, 74, 75, 80, 81, 90, 91, 128, 129, 138, 139, 144, 145, 154, 155, 192, 193, 202, 203, 208, 209, 218, 219]
private theorem finish0438Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0438Input0) = fromList finish0438Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0438 : finishSupport ⟨false, bits4 4⟩ support1260 = 1 • support1261 := by
  have hs : support1260 = fromList finish0438Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0438Chunk0]
  have hn : (finish0438Raw0 : Multiset ℕ) = 1 • (supportNumbers1261 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1261] using hm

private def finish0439Input0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 16, 17, 20, 21, 26, 27, 30, 31, 64, 65, 68, 69, 74, 75, 78, 79, 80, 81, 84, 85, 90, 91, 94, 95, 128, 129, 132, 133, 138, 139, 142, 143, 144, 145, 148, 149, 154, 155, 158, 159, 192, 193, 196, 197, 202, 203, 206, 207, 208, 209, 212, 213, 218, 219, 222, 223]
private def finish0439Raw0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 16, 17, 20, 21, 26, 27, 30, 31, 64, 65, 68, 69, 74, 75, 78, 79, 80, 81, 84, 85, 90, 91, 94, 95, 128, 129, 132, 133, 138, 139, 142, 143, 144, 145, 148, 149, 154, 155, 158, 159, 192, 193, 196, 197, 202, 203, 206, 207, 208, 209, 212, 213, 218, 219, 222, 223]
private theorem finish0439Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0439Input0) = fromList finish0439Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0439Input1 : List ℕ := [514, 515, 518, 519, 520, 521, 524, 525, 530, 531, 534, 535, 536, 537, 540, 541, 578, 579, 582, 583, 584, 585, 588, 589, 594, 595, 598, 599, 600, 601, 604, 605, 642, 643, 646, 647, 648, 649, 652, 653, 658, 659, 662, 663, 664, 665, 668, 669, 706, 707, 710, 711, 712, 713, 716, 717, 722, 723, 726, 727, 728, 729, 732, 733]
private def finish0439Raw1 : List ℕ := [2, 3, 6, 7, 8, 9, 12, 13, 18, 19, 22, 23, 24, 25, 28, 29, 66, 67, 70, 71, 72, 73, 76, 77, 82, 83, 86, 87, 88, 89, 92, 93, 130, 131, 134, 135, 136, 137, 140, 141, 146, 147, 150, 151, 152, 153, 156, 157, 194, 195, 198, 199, 200, 201, 204, 205, 210, 211, 214, 215, 216, 217, 220, 221]
private theorem finish0439Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0439Input1) = fromList finish0439Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0439 : finishSupport ⟨true, bits4 4⟩ support1262 = 1 • support0096 := by
  have hs : support1262 = fromList finish0439Input0 + fromList finish0439Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0439Chunk0, finish0439Chunk1]
  have hn : (finish0439Raw0 : Multiset ℕ) + (finish0439Raw1 : Multiset ℕ) = 1 • (supportNumbers0096 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0096] using hm

private def finish0440Input0 : List ℕ := [0, 128]
private def finish0440Raw0 : List ℕ := [0, 128]
private theorem finish0440Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0440Input0) = fromList finish0440Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0440 : finishSupport ⟨false, bits4 4⟩ support1265 = 1 • support1265 := by
  have hs : support1265 = fromList finish0440Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0440Chunk0]
  have hn : (finish0440Raw0 : Multiset ℕ) = 1 • (supportNumbers1265 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1265] using hm

private def finish0441Input0 : List ℕ := [0, 128, 578, 706]
private def finish0441Raw0 : List ℕ := [0, 128, 66, 194]
private theorem finish0441Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0441Input0) = fromList finish0441Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0441 : finishSupport ⟨true, bits4 4⟩ support1266 = 1 • support1267 := by
  have hs : support1266 = fromList finish0441Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0441Chunk0]
  have hn : (finish0441Raw0 : Multiset ℕ) = 1 • (supportNumbers1267 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1267] using hm

private def finish0442Input0 : List ℕ := [0, 8, 130, 138]
private def finish0442Raw0 : List ℕ := [0, 8, 130, 138]
private theorem finish0442Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0442Input0) = fromList finish0442Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0442 : finishSupport ⟨false, bits4 4⟩ support1269 = 1 • support1269 := by
  have hs : support1269 = fromList finish0442Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0442Chunk0]
  have hn : (finish0442Raw0 : Multiset ℕ) = 1 • (supportNumbers1269 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1269] using hm

private def finish0443Input0 : List ℕ := [0, 8, 130, 138, 578, 586, 704, 712]
private def finish0443Raw0 : List ℕ := [0, 8, 130, 138, 66, 74, 192, 200]
private theorem finish0443Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0443Input0) = fromList finish0443Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0443 : finishSupport ⟨true, bits4 4⟩ support1270 = 1 • support1271 := by
  have hs : support1270 = fromList finish0443Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0443Chunk0]
  have hn : (finish0443Raw0 : Multiset ℕ) = 1 • (supportNumbers1271 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1271] using hm

private def finish0444Input0 : List ℕ := [0, 2, 128, 130, 296, 298, 424, 426]
private def finish0444Raw0 : List ℕ := [0, 2, 128, 130]
private theorem finish0444Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0444Input0) = fromList finish0444Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0444 : finishSupport ⟨false, bits4 4⟩ support1275 = 1 • support0252 := by
  have hs : support1275 = fromList finish0444Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0444Chunk0]
  have hn : (finish0444Raw0 : Multiset ℕ) = 1 • (supportNumbers0252 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0252] using hm

private def finish0445Input0 : List ℕ := [0, 2, 128, 130, 296, 298, 424, 426, 576, 578, 704, 706, 872, 874, 1000, 1002]
private def finish0445Raw0 : List ℕ := [0, 2, 128, 130, 40, 42, 168, 170, 64, 66, 192, 194, 104, 106, 232, 234]
private theorem finish0445Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0445Input0) = fromList finish0445Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0445 : finishSupport ⟨true, bits4 4⟩ support1276 = 1 • support1277 := by
  have hs : support1276 = fromList finish0445Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0445Chunk0]
  have hn : (finish0445Raw0 : Multiset ℕ) = 1 • (supportNumbers1277 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1277] using hm

private def finish0446Input0 : List ℕ := [0, 2, 297, 299]
private def finish0446Raw0 : List ℕ := [0, 2]
private theorem finish0446Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0446Input0) = fromList finish0446Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0446 : finishSupport ⟨false, bits4 4⟩ support1279 = 1 • support0008 := by
  have hs : support1279 = fromList finish0446Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0446Chunk0]
  have hn : (finish0446Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def finish0447Input0 : List ℕ := [0, 2, 297, 299, 576, 578, 873, 875]
private def finish0447Raw0 : List ℕ := [0, 2, 41, 43, 64, 66, 105, 107]
private theorem finish0447Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0447Input0) = fromList finish0447Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0447 : finishSupport ⟨true, bits4 4⟩ support1280 = 1 • support1281 := by
  have hs : support1280 = fromList finish0447Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0447Chunk0]
  have hn : (finish0447Raw0 : Multiset ℕ) = 1 • (supportNumbers1281 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1281] using hm

private def finish0448Input0 : List ℕ := [0, 2, 137, 139, 297, 299, 416, 418]
private def finish0448Raw0 : List ℕ := [0, 2, 137, 139]
private theorem finish0448Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0448Input0) = fromList finish0448Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0448 : finishSupport ⟨false, bits4 4⟩ support1284 = 1 • support0026 := by
  have hs : support1284 = fromList finish0448Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0448Chunk0]
  have hn : (finish0448Raw0 : Multiset ℕ) = 1 • (supportNumbers0026 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0026] using hm

private def finish0449Input0 : List ℕ := [0, 2, 137, 139, 297, 299, 416, 418, 576, 578, 713, 715, 873, 875, 992, 994]
private def finish0449Raw0 : List ℕ := [0, 2, 137, 139, 41, 43, 160, 162, 64, 66, 201, 203, 105, 107, 224, 226]
private theorem finish0449Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0449Input0) = fromList finish0449Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0449 : finishSupport ⟨true, bits4 4⟩ support1285 = 1 • support1286 := by
  have hs : support1285 = fromList finish0449Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0449Chunk0]
  have hn : (finish0449Raw0 : Multiset ℕ) = 1 • (supportNumbers1286 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1286] using hm

private def finish0450Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139]
private def finish0450Raw0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139]
private theorem finish0450Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0450Input0) = fromList finish0450Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0450 : finishSupport ⟨false, bits4 4⟩ support0351 = 1 • support0351 := by
  have hs : support0351 = fromList finish0450Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0450Chunk0]
  have hn : (finish0450Raw0 : Multiset ℕ) = 1 • (supportNumbers0351 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0351] using hm

private def finish0451Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 576, 578, 585, 587, 704, 706, 713, 715]
private def finish0451Raw0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 64, 66, 73, 75, 192, 194, 201, 203]
private theorem finish0451Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0451Input0) = fromList finish0451Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0451 : finishSupport ⟨true, bits4 4⟩ support1287 = 1 • support1288 := by
  have hs : support1287 = fromList finish0451Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0451Chunk0]
  have hn : (finish0451Raw0 : Multiset ℕ) = 1 • (supportNumbers1288 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1288] using hm

private def finish0452Input0 : List ℕ := [0, 2, 9, 11, 417, 419, 424, 426]
private def finish0452Raw0 : List ℕ := [0, 2, 9, 11]
private theorem finish0452Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0452Input0) = fromList finish0452Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0452 : finishSupport ⟨false, bits4 4⟩ support1291 = 1 • support0175 := by
  have hs : support1291 = fromList finish0452Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0452Chunk0]
  have hn : (finish0452Raw0 : Multiset ℕ) = 1 • (supportNumbers0175 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0175] using hm

private def finish0453Input0 : List ℕ := [0, 2, 9, 11, 417, 419, 424, 426, 576, 578, 585, 587, 993, 995, 1000, 1002]
private def finish0453Raw0 : List ℕ := [0, 2, 9, 11, 161, 163, 168, 170, 64, 66, 73, 75, 225, 227, 232, 234]
private theorem finish0453Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0453Input0) = fromList finish0453Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0453 : finishSupport ⟨true, bits4 4⟩ support1292 = 1 • support1293 := by
  have hs : support1292 = fromList finish0453Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0453Chunk0]
  have hn : (finish0453Raw0 : Multiset ℕ) = 1 • (supportNumbers1293 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1293] using hm

private def finish0454Input0 : List ℕ := [0, 1, 2, 3, 296, 297, 298, 299]
private def finish0454Raw0 : List ℕ := [0, 1, 2, 3]
private theorem finish0454Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0454Input0) = fromList finish0454Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0454 : finishSupport ⟨false, bits4 4⟩ support1295 = 1 • support0030 := by
  have hs : support1295 = fromList finish0454Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0454Chunk0]
  have hn : (finish0454Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def finish0455Input0 : List ℕ := [0, 1, 2, 3, 296, 297, 298, 299, 576, 577, 578, 579, 872, 873, 874, 875]
private def finish0455Raw0 : List ℕ := [0, 1, 2, 3, 40, 41, 42, 43, 64, 65, 66, 67, 104, 105, 106, 107]
private theorem finish0455Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0455Input0) = fromList finish0455Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0455 : finishSupport ⟨true, bits4 4⟩ support1296 = 1 • support1297 := by
  have hs : support1296 = fromList finish0455Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0455Chunk0]
  have hn : (finish0455Raw0 : Multiset ℕ) = 1 • (supportNumbers1297 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1297] using hm

private def finish0456Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private def finish0456Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem finish0456Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0456Input0) = fromList finish0456Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0456 : finishSupport ⟨false, bits4 4⟩ support0180 = 1 • support0180 := by
  have hs : support0180 = fromList finish0456Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0456Chunk0]
  have hn : (finish0456Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def finish0457Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 576, 577, 578, 579, 584, 585, 586, 587]
private def finish0457Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 64, 65, 66, 67, 72, 73, 74, 75]
private theorem finish0457Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0457Input0) = fromList finish0457Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0457 : finishSupport ⟨true, bits4 4⟩ support1298 = 1 • support1299 := by
  have hs : support1298 = fromList finish0457Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0457Chunk0]
  have hn : (finish0457Raw0 : Multiset ℕ) = 1 • (supportNumbers1299 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1299] using hm

private def finish0458Input0 : List ℕ := [0, 2, 129, 131, 288, 290, 417, 419]
private def finish0458Raw0 : List ℕ := [0, 2, 129, 131]
private theorem finish0458Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0458Input0) = fromList finish0458Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0458 : finishSupport ⟨false, bits4 4⟩ support1302 = 1 • support0110 := by
  have hs : support1302 = fromList finish0458Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0458Chunk0]
  have hn : (finish0458Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm

private def finish0459Input0 : List ℕ := [0, 2, 129, 131, 288, 290, 417, 419, 576, 578, 705, 707, 864, 866, 993, 995]
private def finish0459Raw0 : List ℕ := [0, 2, 129, 131, 32, 34, 161, 163, 64, 66, 193, 195, 96, 98, 225, 227]
private theorem finish0459Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0459Input0) = fromList finish0459Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0459 : finishSupport ⟨true, bits4 4⟩ support1303 = 1 • support1304 := by
  have hs : support1303 = fromList finish0459Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0459Chunk0]
  have hn : (finish0459Raw0 : Multiset ℕ) = 1 • (supportNumbers1304 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1304] using hm

private def finish0460Input0 : List ℕ := [0, 8, 129, 137]
private def finish0460Raw0 : List ℕ := [0, 8, 129, 137]
private theorem finish0460Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0460Input0) = fromList finish0460Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0460 : finishSupport ⟨false, bits4 4⟩ support1305 = 1 • support1305 := by
  have hs : support1305 = fromList finish0460Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0460Chunk0]
  have hn : (finish0460Raw0 : Multiset ℕ) = 1 • (supportNumbers1305 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1305] using hm

private def finish0461Input0 : List ℕ := [0, 8, 129, 137, 578, 586, 707, 715]
private def finish0461Raw0 : List ℕ := [0, 8, 129, 137, 66, 74, 195, 203]
private theorem finish0461Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0461Input0) = fromList finish0461Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0461 : finishSupport ⟨true, bits4 4⟩ support1306 = 1 • support1307 := by
  have hs : support1306 = fromList finish0461Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0461Chunk0]
  have hn : (finish0461Raw0 : Multiset ℕ) = 1 • (supportNumbers1307 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1307] using hm

private def finish0462Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private def finish0462Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private theorem finish0462Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0462Input0) = fromList finish0462Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0462 : finishSupport ⟨false, bits4 4⟩ support0268 = 1 • support0268 := by
  have hs : support0268 = fromList finish0462Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0462Chunk0]
  have hn : (finish0462Raw0 : Multiset ℕ) = 1 • (supportNumbers0268 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0268] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
