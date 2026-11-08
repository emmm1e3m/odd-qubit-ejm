import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0277Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 936, 937, 938, 939, 940, 941, 942, 943, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]
private def finish0277Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 168, 169, 170, 171, 172, 173, 174, 175, 232, 233, 234, 235, 236, 237, 238, 239, 0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 168, 169, 170, 171, 172, 173, 174, 175, 232, 233, 234, 235, 236, 237, 238, 239]
private theorem finish0277Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0277Input0) = fromList finish0277Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0277 : finishSupport ⟨true, bits4 4⟩ support0983 = 2 • support0744 := by
  have hs : support0983 = fromList finish0277Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0277Chunk0]
  have hn : (finish0277Raw0 : Multiset ℕ) = 2 • (supportNumbers0744 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0744] using hm

private def finish0278Input0 : List ℕ := [0, 1, 4, 5, 18, 19, 22, 23, 64, 65, 68, 69, 82, 83, 86, 87, 136, 137, 140, 141, 154, 155, 158, 159, 200, 201, 204, 205, 218, 219, 222, 223]
private def finish0278Raw0 : List ℕ := [0, 1, 18, 19, 64, 65, 82, 83, 136, 137, 154, 155, 200, 201, 218, 219]
private theorem finish0278Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0278Input0) = fromList finish0278Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0278 : finishSupport ⟨false, bits4 4⟩ support0984 = 1 • support0985 := by
  have hs : support0984 = fromList finish0278Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0278Chunk0]
  have hn : (finish0278Raw0 : Multiset ℕ) = 1 • (supportNumbers0985 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0985] using hm

private def finish0279Input0 : List ℕ := [0, 1, 4, 5, 18, 19, 22, 23, 64, 65, 68, 69, 82, 83, 86, 87, 136, 137, 140, 141, 154, 155, 158, 159, 200, 201, 204, 205, 218, 219, 222, 223, 514, 515, 518, 519, 528, 529, 532, 533, 578, 579, 582, 583, 592, 593, 596, 597, 650, 651, 654, 655, 664, 665, 668, 669, 714, 715, 718, 719, 728, 729, 732, 733]
private def finish0279Raw0 : List ℕ := [0, 1, 4, 5, 18, 19, 22, 23, 64, 65, 68, 69, 82, 83, 86, 87, 136, 137, 140, 141, 154, 155, 158, 159, 200, 201, 204, 205, 218, 219, 222, 223, 2, 3, 6, 7, 16, 17, 20, 21, 66, 67, 70, 71, 80, 81, 84, 85, 138, 139, 142, 143, 152, 153, 156, 157, 202, 203, 206, 207, 216, 217, 220, 221]
private theorem finish0279Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0279Input0) = fromList finish0279Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0279 : finishSupport ⟨true, bits4 4⟩ support0986 = 1 • support0048 := by
  have hs : support0986 = fromList finish0279Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0279Chunk0]
  have hn : (finish0279Raw0 : Multiset ℕ) = 1 • (supportNumbers0048 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0048] using hm

private def finish0280Input0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77, 144, 145, 148, 149, 152, 153, 156, 157, 208, 209, 212, 213, 216, 217, 220, 221]
private def finish0280Raw0 : List ℕ := [0, 1, 8, 9, 64, 65, 72, 73, 144, 145, 152, 153, 208, 209, 216, 217]
private theorem finish0280Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0280Input0) = fromList finish0280Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0280 : finishSupport ⟨false, bits4 4⟩ support0988 = 1 • support0989 := by
  have hs : support0988 = fromList finish0280Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0280Chunk0]
  have hn : (finish0280Raw0 : Multiset ℕ) = 1 • (supportNumbers0989 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0989] using hm

private def finish0281Input0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77, 144, 145, 148, 149, 152, 153, 156, 157, 208, 209, 212, 213, 216, 217, 220, 221, 514, 515, 518, 519, 522, 523, 526, 527, 578, 579, 582, 583, 586, 587, 590, 591, 658, 659, 662, 663, 666, 667, 670, 671, 722, 723, 726, 727, 730, 731, 734, 735]
private def finish0281Raw0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77, 144, 145, 148, 149, 152, 153, 156, 157, 208, 209, 212, 213, 216, 217, 220, 221, 2, 3, 6, 7, 10, 11, 14, 15, 66, 67, 70, 71, 74, 75, 78, 79, 146, 147, 150, 151, 154, 155, 158, 159, 210, 211, 214, 215, 218, 219, 222, 223]
private theorem finish0281Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0281Input0) = fromList finish0281Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0281 : finishSupport ⟨true, bits4 4⟩ support0990 = 1 • support0157 := by
  have hs : support0990 = fromList finish0281Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0281Chunk0]
  have hn : (finish0281Raw0 : Multiset ℕ) = 1 • (supportNumbers0157 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0157] using hm

private def finish0282Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0282Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 64, 65, 66, 67, 72, 73, 74, 75, 144, 145, 146, 147, 152, 153, 154, 155, 208, 209, 210, 211, 216, 217, 218, 219]
private theorem finish0282Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0282Input0) = fromList finish0282Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0282Input1 : List ℕ := [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]
private def finish0282Raw1 : List ℕ := [52, 53, 54, 55, 60, 61, 62, 63, 116, 117, 118, 119, 124, 125, 126, 127, 164, 165, 166, 167, 172, 173, 174, 175, 228, 229, 230, 231, 236, 237, 238, 239]
private theorem finish0282Chunk1 : finishSupport ⟨false, bits4 4⟩ (fromList finish0282Input1) = fromList finish0282Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0282 : finishSupport ⟨false, bits4 4⟩ support0992 = 1 • support0993 := by
  have hs : support0992 = fromList finish0282Input0 + fromList finish0282Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0282Chunk0, finish0282Chunk1]
  have hn : (finish0282Raw0 : Multiset ℕ) + (finish0282Raw1 : Multiset ℕ) = 1 • (supportNumbers0993 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0993] using hm

private def finish0283Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0283Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem finish0283Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0283Input0) = fromList finish0283Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0283Input1 : List ℕ := [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]
private def finish0283Raw1 : List ℕ := [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]
private theorem finish0283Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0283Input1) = fromList finish0283Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0283Input2 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]
private def finish0283Raw2 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem finish0283Chunk2 : finishSupport ⟨true, bits4 4⟩ (fromList finish0283Input2) = fromList finish0283Raw2 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0283Input3 : List ℕ := [816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]
private def finish0283Raw3 : List ℕ := [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]
private theorem finish0283Chunk3 : finishSupport ⟨true, bits4 4⟩ (fromList finish0283Input3) = fromList finish0283Raw3 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0283 : finishSupport ⟨true, bits4 4⟩ support0994 = 2 • support0995 := by
  have hs : support0994 = fromList finish0283Input0 + fromList finish0283Input1 + fromList finish0283Input2 + fromList finish0283Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0283Chunk0, finish0283Chunk1, finish0283Chunk2, finish0283Chunk3]
  have hn : (finish0283Raw0 : Multiset ℕ) + (finish0283Raw1 : Multiset ℕ) + (finish0283Raw2 : Multiset ℕ) + (finish0283Raw3 : Multiset ℕ) = 2 • (supportNumbers0995 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0995] using hm

private def finish0284Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private def finish0284Raw0 : List ℕ := [0, 1, 2, 3, 16, 17, 18, 19, 64, 65, 66, 67, 80, 81, 82, 83]
private theorem finish0284Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0284Input0) = fromList finish0284Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0284 : finishSupport ⟨false, bits4 4⟩ support0092 = 1 • support0996 := by
  have hs : support0092 = fromList finish0284Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0284Chunk0]
  have hn : (finish0284Raw0 : Multiset ℕ) = 1 • (supportNumbers0996 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0996] using hm

private def finish0285Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599]
private def finish0285Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private theorem finish0285Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0285Input0) = fromList finish0285Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0285 : finishSupport ⟨true, bits4 4⟩ support0413 = 2 • support0092 := by
  have hs : support0413 = fromList finish0285Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0285Chunk0]
  have hn : (finish0285Raw0 : Multiset ℕ) = 2 • (supportNumbers0092 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0092] using hm

private def finish0286Input0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 16, 17, 20, 21, 26, 27, 30, 31, 64, 65, 68, 69, 74, 75, 78, 79, 80, 81, 84, 85, 90, 91, 94, 95]
private def finish0286Raw0 : List ℕ := [0, 1, 10, 11, 16, 17, 26, 27, 64, 65, 74, 75, 80, 81, 90, 91]
private theorem finish0286Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0286Input0) = fromList finish0286Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0286 : finishSupport ⟨false, bits4 4⟩ support0997 = 1 • support0998 := by
  have hs : support0997 = fromList finish0286Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0286Chunk0]
  have hn : (finish0286Raw0 : Multiset ℕ) = 1 • (supportNumbers0998 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0998] using hm

private def finish0287Input0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 16, 17, 20, 21, 26, 27, 30, 31, 64, 65, 68, 69, 74, 75, 78, 79, 80, 81, 84, 85, 90, 91, 94, 95, 514, 515, 518, 519, 520, 521, 524, 525, 530, 531, 534, 535, 536, 537, 540, 541, 578, 579, 582, 583, 584, 585, 588, 589, 594, 595, 598, 599, 600, 601, 604, 605]
private def finish0287Raw0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 16, 17, 20, 21, 26, 27, 30, 31, 64, 65, 68, 69, 74, 75, 78, 79, 80, 81, 84, 85, 90, 91, 94, 95, 2, 3, 6, 7, 8, 9, 12, 13, 18, 19, 22, 23, 24, 25, 28, 29, 66, 67, 70, 71, 72, 73, 76, 77, 82, 83, 86, 87, 88, 89, 92, 93]
private theorem finish0287Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0287Input0) = fromList finish0287Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0287 : finishSupport ⟨true, bits4 4⟩ support0999 = 1 • support0246 := by
  have hs : support0999 = fromList finish0287Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0287Chunk0]
  have hn : (finish0287Raw0 : Multiset ℕ) = 1 • (supportNumbers0246 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0246] using hm

private def finish0288Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def finish0288Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27, 64, 65, 66, 67, 72, 73, 74, 75, 80, 81, 82, 83, 88, 89, 90, 91]
private theorem finish0288Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0288Input0) = fromList finish0288Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0288Input1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]
private def finish0288Raw1 : List ℕ := [36, 37, 38, 39, 44, 45, 46, 47, 52, 53, 54, 55, 60, 61, 62, 63, 100, 101, 102, 103, 108, 109, 110, 111, 116, 117, 118, 119, 124, 125, 126, 127]
private theorem finish0288Chunk1 : finishSupport ⟨false, bits4 4⟩ (fromList finish0288Input1) = fromList finish0288Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0288 : finishSupport ⟨false, bits4 4⟩ support1001 = 1 • support1002 := by
  have hs : support1001 = fromList finish0288Input0 + fromList finish0288Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0288Chunk0, finish0288Chunk1]
  have hn : (finish0288Raw0 : Multiset ℕ) + (finish0288Raw1 : Multiset ℕ) = 1 • (supportNumbers1002 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1002] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
