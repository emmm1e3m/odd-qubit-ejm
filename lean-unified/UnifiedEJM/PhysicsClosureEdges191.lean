import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0059Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 576, 577, 578, 579, 584, 585, 586, 587, 596, 597, 598, 599, 604, 605, 606, 607, 704, 705, 706, 707, 712, 713, 714, 715, 724, 725, 726, 727, 732, 733, 734, 735]
private def finish0059Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 64, 65, 66, 67, 72, 73, 74, 75, 84, 85, 86, 87, 92, 93, 94, 95, 192, 193, 194, 195, 200, 201, 202, 203, 212, 213, 214, 215, 220, 221, 222, 223]
private theorem finish0059Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0059Input0) = fromList finish0059Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0059 : finishSupport ⟨true, bits4 4⟩ support0591 = 1 • support0592 := by
  have hs : support0591 = fromList finish0059Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0059Chunk0]
  have hn : (finish0059Raw0 : Multiset ℕ) = 1 • (supportNumbers0592 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0592] using hm

private def finish0060Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private def finish0060Raw0 : List ℕ := [0, 2, 65, 67]
private theorem finish0060Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0060Input0) = fromList finish0060Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0060 : finishSupport ⟨false, bits4 4⟩ support0016 = 1 • support0594 := by
  have hs : support0016 = fromList finish0060Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0060Chunk0]
  have hn : (finish0060Raw0 : Multiset ℕ) = 1 • (supportNumbers0594 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0594] using hm

private def finish0061Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 513, 515, 517, 519, 576, 578, 580, 582]
private def finish0061Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 1, 3, 5, 7, 64, 66, 68, 70]
private theorem finish0061Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0061Input0) = fromList finish0061Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0061 : finishSupport ⟨true, bits4 4⟩ support0595 = 1 • support0044 := by
  have hs : support0595 = fromList finish0061Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0061Chunk0]
  have hn : (finish0061Raw0 : Multiset ℕ) = 1 • (supportNumbers0044 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0044] using hm

private def finish0062Input0 : List ℕ := [0, 4, 65, 69, 138, 142, 203, 207]
private def finish0062Raw0 : List ℕ := [0, 65, 138, 203]
private theorem finish0062Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0062Input0) = fromList finish0062Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0062 : finishSupport ⟨false, bits4 4⟩ support0596 = 1 • support0597 := by
  have hs : support0596 = fromList finish0062Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0062Chunk0]
  have hn : (finish0062Raw0 : Multiset ℕ) = 1 • (supportNumbers0597 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0597] using hm

private def finish0063Input0 : List ℕ := [0, 4, 65, 69, 138, 142, 203, 207, 515, 519, 578, 582, 649, 653, 712, 716]
private def finish0063Raw0 : List ℕ := [0, 4, 65, 69, 138, 142, 203, 207, 3, 7, 66, 70, 137, 141, 200, 204]
private theorem finish0063Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0063Input0) = fromList finish0063Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0063 : finishSupport ⟨true, bits4 4⟩ support0598 = 1 • support0599 := by
  have hs : support0598 = fromList finish0063Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0063Chunk0]
  have hn : (finish0063Raw0 : Multiset ℕ) = 1 • (supportNumbers0599 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0599] using hm

private def finish0064Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 288, 290, 292, 294, 353, 355, 357, 359, 424, 426, 428, 430, 489, 491, 493, 495]
private def finish0064Raw0 : List ℕ := [0, 2, 65, 67, 136, 138, 201, 203, 36, 38, 101, 103, 172, 174, 237, 239]
private theorem finish0064Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0064Input0) = fromList finish0064Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0064 : finishSupport ⟨false, bits4 4⟩ support0601 = 1 • support0602 := by
  have hs : support0601 = fromList finish0064Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0064Chunk0]
  have hn : (finish0064Raw0 : Multiset ℕ) = 1 • (supportNumbers0602 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0602] using hm

private def finish0065Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 288, 290, 292, 294, 353, 355, 357, 359, 424, 426, 428, 430, 489, 491, 493, 495, 513, 515, 517, 519, 576, 578, 580, 582, 649, 651, 653, 655, 712, 714, 716, 718, 801, 803, 805, 807, 864, 866, 868, 870, 937, 939, 941, 943, 1000, 1002, 1004, 1006]
private def finish0065Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 32, 34, 36, 38, 97, 99, 101, 103, 168, 170, 172, 174, 233, 235, 237, 239, 1, 3, 5, 7, 64, 66, 68, 70, 137, 139, 141, 143, 200, 202, 204, 206, 33, 35, 37, 39, 96, 98, 100, 102, 169, 171, 173, 175, 232, 234, 236, 238]
private theorem finish0065Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0065Input0) = fromList finish0065Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0065 : finishSupport ⟨true, bits4 4⟩ support0603 = 1 • support0604 := by
  have hs : support0603 = fromList finish0065Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0065Chunk0]
  have hn : (finish0065Raw0 : Multiset ℕ) = 1 • (supportNumbers0604 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0604] using hm

private def finish0066Input0 : List ℕ := [0, 4, 65, 69, 137, 141, 200, 204]
private def finish0066Raw0 : List ℕ := [0, 65, 137, 200]
private theorem finish0066Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0066Input0) = fromList finish0066Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0066 : finishSupport ⟨false, bits4 4⟩ support0605 = 1 • support0606 := by
  have hs : support0605 = fromList finish0066Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0066Chunk0]
  have hn : (finish0066Raw0 : Multiset ℕ) = 1 • (supportNumbers0606 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0606] using hm

private def finish0067Input0 : List ℕ := [0, 4, 65, 69, 137, 141, 200, 204, 515, 519, 578, 582, 650, 654, 715, 719]
private def finish0067Raw0 : List ℕ := [0, 4, 65, 69, 137, 141, 200, 204, 3, 7, 66, 70, 138, 142, 203, 207]
private theorem finish0067Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0067Input0) = fromList finish0067Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0067 : finishSupport ⟨true, bits4 4⟩ support0607 = 1 • support0599 := by
  have hs : support0607 = fromList finish0067Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0067Chunk0]
  have hn : (finish0067Raw0 : Multiset ℕ) = 1 • (supportNumbers0599 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0599] using hm

private def finish0068Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 296, 298, 300, 302, 361, 363, 365, 367, 417, 419, 421, 423, 480, 482, 484, 486]
private def finish0068Raw0 : List ℕ := [0, 2, 65, 67, 137, 139, 200, 202, 44, 46, 109, 111, 165, 167, 228, 230]
private theorem finish0068Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0068Input0) = fromList finish0068Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0068 : finishSupport ⟨false, bits4 4⟩ support0609 = 1 • support0610 := by
  have hs : support0609 = fromList finish0068Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0068Chunk0]
  have hn : (finish0068Raw0 : Multiset ℕ) = 1 • (supportNumbers0610 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0610] using hm

private def finish0069Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 296, 298, 300, 302, 361, 363, 365, 367, 417, 419, 421, 423, 480, 482, 484, 486, 513, 515, 517, 519, 576, 578, 580, 582, 648, 650, 652, 654, 713, 715, 717, 719, 809, 811, 813, 815, 872, 874, 876, 878, 928, 930, 932, 934, 993, 995, 997, 999]
private def finish0069Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 40, 42, 44, 46, 105, 107, 109, 111, 161, 163, 165, 167, 224, 226, 228, 230, 1, 3, 5, 7, 64, 66, 68, 70, 136, 138, 140, 142, 201, 203, 205, 207, 41, 43, 45, 47, 104, 106, 108, 110, 160, 162, 164, 166, 225, 227, 229, 231]
private theorem finish0069Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0069Input0) = fromList finish0069Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0069 : finishSupport ⟨true, bits4 4⟩ support0611 = 1 • support0612 := by
  have hs : support0611 = fromList finish0069Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0069Chunk0]
  have hn : (finish0069Raw0 : Multiset ℕ) = 1 • (supportNumbers0612 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0612] using hm

private def finish0070Input0 : List ℕ := [0, 3, 4, 7, 8, 11, 12, 15, 65, 66, 69, 70, 73, 74, 77, 78, 129, 130, 133, 134, 137, 138, 141, 142, 192, 195, 196, 199, 200, 203, 204, 207]
private def finish0070Raw0 : List ℕ := [0, 3, 8, 11, 65, 66, 73, 74, 129, 130, 137, 138, 192, 195, 200, 203]
private theorem finish0070Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0070Input0) = fromList finish0070Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0070 : finishSupport ⟨false, bits4 4⟩ support0613 = 1 • support0562 := by
  have hs : support0613 = fromList finish0070Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0070Chunk0]
  have hn : (finish0070Raw0 : Multiset ℕ) = 1 • (supportNumbers0562 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0562] using hm

private def finish0071Input0 : List ℕ := [0, 3, 4, 7, 8, 11, 12, 15, 65, 66, 69, 70, 73, 74, 77, 78, 129, 130, 133, 134, 137, 138, 141, 142, 192, 195, 196, 199, 200, 203, 204, 207, 512, 515, 516, 519, 520, 523, 524, 527, 577, 578, 581, 582, 585, 586, 589, 590, 641, 642, 645, 646, 649, 650, 653, 654, 704, 707, 708, 711, 712, 715, 716, 719]
private def finish0071Raw0 : List ℕ := [0, 3, 4, 7, 8, 11, 12, 15, 65, 66, 69, 70, 73, 74, 77, 78, 129, 130, 133, 134, 137, 138, 141, 142, 192, 195, 196, 199, 200, 203, 204, 207, 0, 3, 4, 7, 8, 11, 12, 15, 65, 66, 69, 70, 73, 74, 77, 78, 129, 130, 133, 134, 137, 138, 141, 142, 192, 195, 196, 199, 200, 203, 204, 207]
private theorem finish0071Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0071Input0) = fromList finish0071Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0071 : finishSupport ⟨true, bits4 4⟩ support0614 = 2 • support0613 := by
  have hs : support0614 = fromList finish0071Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0071Chunk0]
  have hn : (finish0071Raw0 : Multiset ℕ) = 2 • (supportNumbers0613 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0613] using hm

private def finish0072Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private def finish0072Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 64, 65, 66, 67, 72, 73, 74, 75, 128, 129, 130, 131, 136, 137, 138, 139, 192, 193, 194, 195, 200, 201, 202, 203]
private theorem finish0072Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0072Input0) = fromList finish0072Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0072Input1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]
private def finish0072Raw1 : List ℕ := [36, 37, 38, 39, 44, 45, 46, 47, 100, 101, 102, 103, 108, 109, 110, 111, 164, 165, 166, 167, 172, 173, 174, 175, 228, 229, 230, 231, 236, 237, 238, 239]
private theorem finish0072Chunk1 : finishSupport ⟨false, bits4 4⟩ (fromList finish0072Input1) = fromList finish0072Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0072 : finishSupport ⟨false, bits4 4⟩ support0616 = 1 • support0617 := by
  have hs : support0616 = fromList finish0072Input0 + fromList finish0072Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0072Chunk0, finish0072Chunk1]
  have hn : (finish0072Raw0 : Multiset ℕ) + (finish0072Raw1 : Multiset ℕ) = 1 • (supportNumbers0617 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0617] using hm

private def finish0073Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private def finish0073Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem finish0073Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0073Input0) = fromList finish0073Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0073Input1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]
private def finish0073Raw1 : List ℕ := [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]
private theorem finish0073Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0073Input1) = fromList finish0073Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0073Input2 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]
private def finish0073Raw2 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem finish0073Chunk2 : finishSupport ⟨true, bits4 4⟩ (fromList finish0073Input2) = fromList finish0073Raw2 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0073Input3 : List ℕ := [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]
private def finish0073Raw3 : List ℕ := [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]
private theorem finish0073Chunk3 : finishSupport ⟨true, bits4 4⟩ (fromList finish0073Input3) = fromList finish0073Raw3 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0073 : finishSupport ⟨true, bits4 4⟩ support0618 = 2 • support0527 := by
  have hs : support0618 = fromList finish0073Input0 + fromList finish0073Input1 + fromList finish0073Input2 + fromList finish0073Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0073Chunk0, finish0073Chunk1, finish0073Chunk2, finish0073Chunk3]
  have hn : (finish0073Raw0 : Multiset ℕ) + (finish0073Raw1 : Multiset ℕ) + (finish0073Raw2 : Multiset ℕ) + (finish0073Raw3 : Multiset ℕ) = 2 • (supportNumbers0527 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0527] using hm

private def finish0074Input0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69]
private def finish0074Raw0 : List ℕ := [0, 1, 64, 65]
private theorem finish0074Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0074Input0) = fromList finish0074Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0074 : finishSupport ⟨false, bits4 4⟩ support0619 = 1 • support0620 := by
  have hs : support0619 = fromList finish0074Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0074Chunk0]
  have hn : (finish0074Raw0 : Multiset ℕ) = 1 • (supportNumbers0620 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0620] using hm

private def finish0075Input0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 514, 515, 518, 519, 578, 579, 582, 583]
private def finish0075Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 2, 3, 6, 7, 66, 67, 70, 71]
private theorem finish0075Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0075Input0) = fromList finish0075Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0075 : finishSupport ⟨true, bits4 4⟩ support0621 = 1 • support0044 := by
  have hs : support0621 = fromList finish0075Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0075Chunk0]
  have hn : (finish0075Raw0 : Multiset ℕ) = 1 • (supportNumbers0044 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0044] using hm

private def finish0076Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 312, 313, 314, 315, 316, 317, 318, 319, 376, 377, 378, 379, 380, 381, 382, 383]
private def finish0076Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 60, 61, 62, 63, 124, 125, 126, 127]
private theorem finish0076Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0076Input0) = fromList finish0076Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0076 : finishSupport ⟨false, bits4 4⟩ support0623 = 1 • support0573 := by
  have hs : support0623 = fromList finish0076Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0076Chunk0]
  have hn : (finish0076Raw0 : Multiset ℕ) = 1 • (supportNumbers0573 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0573] using hm

private def finish0077Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 312, 313, 314, 315, 316, 317, 318, 319, 376, 377, 378, 379, 380, 381, 382, 383, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 824, 825, 826, 827, 828, 829, 830, 831, 888, 889, 890, 891, 892, 893, 894, 895]
private def finish0077Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 56, 57, 58, 59, 60, 61, 62, 63, 120, 121, 122, 123, 124, 125, 126, 127, 0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 56, 57, 58, 59, 60, 61, 62, 63, 120, 121, 122, 123, 124, 125, 126, 127]
private theorem finish0077Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0077Input0) = fromList finish0077Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0077 : finishSupport ⟨true, bits4 4⟩ support0624 = 2 • support0625 := by
  have hs : support0624 = fromList finish0077Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0077Chunk0]
  have hn : (finish0077Raw0 : Multiset ℕ) = 2 • (supportNumbers0625 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0625] using hm

private def finish0078Input0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 138, 139, 142, 143, 146, 147, 150, 151, 202, 203, 206, 207, 210, 211, 214, 215]
private def finish0078Raw0 : List ℕ := [0, 1, 24, 25, 64, 65, 88, 89, 138, 139, 146, 147, 202, 203, 210, 211]
private theorem finish0078Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0078Input0) = fromList finish0078Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0078 : finishSupport ⟨false, bits4 4⟩ support0626 = 1 • support0627 := by
  have hs : support0626 = fromList finish0078Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0078Chunk0]
  have hn : (finish0078Raw0 : Multiset ℕ) = 1 • (supportNumbers0627 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0627] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
