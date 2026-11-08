import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0509Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 417, 419, 421, 423, 424, 426, 428, 430, 480, 482, 484, 486, 489, 491, 493, 495, 513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 928, 930, 932, 934, 937, 939, 941, 943, 993, 995, 997, 999, 1000, 1002, 1004, 1006]
private def finish0509Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 161, 163, 165, 167, 168, 170, 172, 174, 224, 226, 228, 230, 233, 235, 237, 239, 1, 3, 5, 7, 8, 10, 12, 14, 64, 66, 68, 70, 73, 75, 77, 79, 160, 162, 164, 166, 169, 171, 173, 175, 225, 227, 229, 231, 232, 234, 236, 238]
private theorem finish0509Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0509Input0) = fromList finish0509Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0509 : finishSupport ⟨true, bits4 4⟩ support1401 = 1 • support0927 := by
  have hs : support1401 = fromList finish0509Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0509Chunk0]
  have hn : (finish0509Raw0 : Multiset ℕ) = 1 • (supportNumbers0927 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0927] using hm

private def finish0510Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 296, 297, 298, 299, 300, 301, 302, 303, 360, 361, 362, 363, 364, 365, 366, 367]
private def finish0510Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 44, 45, 46, 47, 108, 109, 110, 111]
private theorem finish0510Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0510Input0) = fromList finish0510Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0510 : finishSupport ⟨false, bits4 4⟩ support1403 = 1 • support1404 := by
  have hs : support1403 = fromList finish0510Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0510Chunk0]
  have hn : (finish0510Raw0 : Multiset ℕ) = 1 • (supportNumbers1404 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1404] using hm

private def finish0511Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 296, 297, 298, 299, 300, 301, 302, 303, 360, 361, 362, 363, 364, 365, 366, 367, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 808, 809, 810, 811, 812, 813, 814, 815, 872, 873, 874, 875, 876, 877, 878, 879]
private def finish0511Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 40, 41, 42, 43, 44, 45, 46, 47, 104, 105, 106, 107, 108, 109, 110, 111, 0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 40, 41, 42, 43, 44, 45, 46, 47, 104, 105, 106, 107, 108, 109, 110, 111]
private theorem finish0511Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0511Input0) = fromList finish0511Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0511 : finishSupport ⟨true, bits4 4⟩ support1405 = 2 • support0518 := by
  have hs : support1405 = fromList finish0511Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0511Chunk0]
  have hn : (finish0511Raw0 : Multiset ℕ) = 2 • (supportNumbers0518 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0518] using hm

private def finish0512Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
private def finish0512Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 64, 65, 66, 67, 72, 73, 74, 75]
private theorem finish0512Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0512Input0) = fromList finish0512Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0512 : finishSupport ⟨false, bits4 4⟩ support0222 = 1 • support1299 := by
  have hs : support0222 = fromList finish0512Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0512Chunk0]
  have hn : (finish0512Raw0 : Multiset ℕ) = 1 • (supportNumbers1299 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1299] using hm

private def finish0513Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]
private def finish0513Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
private theorem finish0513Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0513Input0) = fromList finish0513Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0513 : finishSupport ⟨true, bits4 4⟩ support0223 = 2 • support0222 := by
  have hs : support0223 = fromList finish0513Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0513Chunk0]
  have hn : (finish0513Raw0 : Multiset ℕ) = 2 • (supportNumbers0222 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0222] using hm

private def finish0514Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 288, 290, 292, 294, 353, 355, 357, 359, 417, 419, 421, 423, 480, 482, 484, 486]
private def finish0514Raw0 : List ℕ := [0, 2, 65, 67, 129, 131, 192, 194, 36, 38, 101, 103, 165, 167, 228, 230]
private theorem finish0514Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0514Input0) = fromList finish0514Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0514 : finishSupport ⟨false, bits4 4⟩ support1408 = 1 • support1409 := by
  have hs : support1408 = fromList finish0514Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0514Chunk0]
  have hn : (finish0514Raw0 : Multiset ℕ) = 1 • (supportNumbers1409 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1409] using hm

private def finish0515Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 288, 290, 292, 294, 353, 355, 357, 359, 417, 419, 421, 423, 480, 482, 484, 486, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 801, 803, 805, 807, 864, 866, 868, 870, 928, 930, 932, 934, 993, 995, 997, 999]
private def finish0515Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 32, 34, 36, 38, 97, 99, 101, 103, 161, 163, 165, 167, 224, 226, 228, 230, 1, 3, 5, 7, 64, 66, 68, 70, 128, 130, 132, 134, 193, 195, 197, 199, 33, 35, 37, 39, 96, 98, 100, 102, 160, 162, 164, 166, 225, 227, 229, 231]
private theorem finish0515Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0515Input0) = fromList finish0515Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0515 : finishSupport ⟨true, bits4 4⟩ support1410 = 1 • support0913 := by
  have hs : support1410 = fromList finish0515Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0515Chunk0]
  have hn : (finish0515Raw0 : Multiset ℕ) = 1 • (supportNumbers0913 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0913] using hm

private def finish0516Input0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 129, 133, 137, 141, 192, 196, 200, 204]
private def finish0516Raw0 : List ℕ := [0, 8, 65, 73, 129, 137, 192, 200]
private theorem finish0516Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0516Input0) = fromList finish0516Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0516 : finishSupport ⟨false, bits4 4⟩ support1411 = 1 • support1412 := by
  have hs : support1411 = fromList finish0516Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0516Chunk0]
  have hn : (finish0516Raw0 : Multiset ℕ) = 1 • (supportNumbers1412 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1412] using hm

private def finish0517Input0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 129, 133, 137, 141, 192, 196, 200, 204, 515, 519, 523, 527, 578, 582, 586, 590, 642, 646, 650, 654, 707, 711, 715, 719]
private def finish0517Raw0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 129, 133, 137, 141, 192, 196, 200, 204, 3, 7, 11, 15, 66, 70, 74, 78, 130, 134, 138, 142, 195, 199, 203, 207]
private theorem finish0517Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0517Input0) = fromList finish0517Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0517 : finishSupport ⟨true, bits4 4⟩ support1413 = 1 • support0613 := by
  have hs : support1413 = fromList finish0517Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0517Chunk0]
  have hn : (finish0517Raw0 : Multiset ℕ) = 1 • (supportNumbers0613 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0613] using hm

private def finish0518Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private def finish0518Raw0 : List ℕ := [0, 2, 8, 10, 65, 67, 73, 75, 129, 131, 137, 139, 192, 194, 200, 202]
private theorem finish0518Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0518Input0) = fromList finish0518Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0518 : finishSupport ⟨false, bits4 4⟩ support0315 = 1 • support1414 := by
  have hs : support0315 = fromList finish0518Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0518Chunk0]
  have hn : (finish0518Raw0 : Multiset ℕ) = 1 • (supportNumbers1414 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1414] using hm

private def finish0519Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719]
private def finish0519Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 1, 3, 5, 7, 9, 11, 13, 15, 64, 66, 68, 70, 72, 74, 76, 78, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private theorem finish0519Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0519Input0) = fromList finish0519Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0519 : finishSupport ⟨true, bits4 4⟩ support0398 = 1 • support0148 := by
  have hs : support0398 = fromList finish0519Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0519Chunk0]
  have hn : (finish0519Raw0 : Multiset ℕ) = 1 • (supportNumbers0148 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0148] using hm

private def finish0520Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 289, 291, 293, 295, 297, 299, 301, 303, 352, 354, 356, 358, 360, 362, 364, 366, 416, 418, 420, 422, 424, 426, 428, 430, 481, 483, 485, 487, 489, 491, 493, 495]
private def finish0520Raw0 : List ℕ := [0, 2, 8, 10, 65, 67, 73, 75, 129, 131, 137, 139, 192, 194, 200, 202, 37, 39, 45, 47, 100, 102, 108, 110, 164, 166, 172, 174, 229, 231, 237, 239]
private theorem finish0520Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0520Input0) = fromList finish0520Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0520 : finishSupport ⟨false, bits4 4⟩ support1416 = 1 • support1417 := by
  have hs : support1416 = fromList finish0520Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0520Chunk0]
  have hn : (finish0520Raw0 : Multiset ℕ) = 1 • (supportNumbers1417 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1417] using hm

private def finish0521Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 289, 291, 293, 295, 297, 299, 301, 303, 352, 354, 356, 358, 360, 362, 364, 366, 416, 418, 420, 422, 424, 426, 428, 430, 481, 483, 485, 487, 489, 491, 493, 495]
private def finish0521Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 33, 35, 37, 39, 41, 43, 45, 47, 96, 98, 100, 102, 104, 106, 108, 110, 160, 162, 164, 166, 168, 170, 172, 174, 225, 227, 229, 231, 233, 235, 237, 239]
private theorem finish0521Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0521Input0) = fromList finish0521Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0521Input1 : List ℕ := [513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 800, 802, 804, 806, 808, 810, 812, 814, 865, 867, 869, 871, 873, 875, 877, 879, 929, 931, 933, 935, 937, 939, 941, 943, 992, 994, 996, 998, 1000, 1002, 1004, 1006]
private def finish0521Raw1 : List ℕ := [1, 3, 5, 7, 9, 11, 13, 15, 64, 66, 68, 70, 72, 74, 76, 78, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 32, 34, 36, 38, 40, 42, 44, 46, 97, 99, 101, 103, 105, 107, 109, 111, 161, 163, 165, 167, 169, 171, 173, 175, 224, 226, 228, 230, 232, 234, 236, 238]
private theorem finish0521Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0521Input1) = fromList finish0521Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0521 : finishSupport ⟨true, bits4 4⟩ support1418 = 1 • support0527 := by
  have hs : support1418 = fromList finish0521Input0 + fromList finish0521Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0521Chunk0, finish0521Chunk1]
  have hn : (finish0521Raw0 : Multiset ℕ) + (finish0521Raw1 : Multiset ℕ) = 1 • (supportNumbers0527 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0527] using hm

private def finish0522Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private def finish0522Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 128, 129, 130, 131, 192, 193, 194, 195]
private theorem finish0522Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0522Input0) = fromList finish0522Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0522 : finishSupport ⟨false, bits4 4⟩ support0229 = 1 • support1315 := by
  have hs : support0229 = fromList finish0522Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0522Chunk0]
  have hn : (finish0522Raw0 : Multiset ℕ) = 1 • (supportNumbers1315 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1315] using hm

private def finish0523Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711]
private def finish0523Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem finish0523Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0523Input0) = fromList finish0523Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0523 : finishSupport ⟨true, bits4 4⟩ support0401 = 2 • support0229 := by
  have hs : support0401 = fromList finish0523Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0523Chunk0]
  have hn : (finish0523Raw0 : Multiset ℕ) = 2 • (supportNumbers0229 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0229] using hm

private def finish0524Input0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 64, 65, 68, 69, 74, 75, 78, 79, 128, 129, 132, 133, 138, 139, 142, 143, 192, 193, 196, 197, 202, 203, 206, 207]
private def finish0524Raw0 : List ℕ := [0, 1, 10, 11, 64, 65, 74, 75, 128, 129, 138, 139, 192, 193, 202, 203]
private theorem finish0524Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0524Input0) = fromList finish0524Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0524 : finishSupport ⟨false, bits4 4⟩ support1419 = 1 • support1420 := by
  have hs : support1419 = fromList finish0524Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0524Chunk0]
  have hn : (finish0524Raw0 : Multiset ℕ) = 1 • (supportNumbers1420 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1420] using hm

private def finish0525Input0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 64, 65, 68, 69, 74, 75, 78, 79, 128, 129, 132, 133, 138, 139, 142, 143, 192, 193, 196, 197, 202, 203, 206, 207, 514, 515, 518, 519, 520, 521, 524, 525, 578, 579, 582, 583, 584, 585, 588, 589, 642, 643, 646, 647, 648, 649, 652, 653, 706, 707, 710, 711, 712, 713, 716, 717]
private def finish0525Raw0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 64, 65, 68, 69, 74, 75, 78, 79, 128, 129, 132, 133, 138, 139, 142, 143, 192, 193, 196, 197, 202, 203, 206, 207, 2, 3, 6, 7, 8, 9, 12, 13, 66, 67, 70, 71, 72, 73, 76, 77, 130, 131, 134, 135, 136, 137, 140, 141, 194, 195, 198, 199, 200, 201, 204, 205]
private theorem finish0525Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0525Input0) = fromList finish0525Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0525 : finishSupport ⟨true, bits4 4⟩ support1421 = 1 • support0148 := by
  have hs : support1421 = fromList finish0525Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0525Chunk0]
  have hn : (finish0525Raw0 : Multiset ℕ) = 1 • (supportNumbers0148 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0148] using hm

private def finish0526Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487]
private def finish0526Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 164, 165, 166, 167, 228, 229, 230, 231]
private theorem finish0526Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0526Input0) = fromList finish0526Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0526 : finishSupport ⟨false, bits4 4⟩ support1424 = 1 • support1425 := by
  have hs : support1424 = fromList finish0526Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0526Chunk0]
  have hn : (finish0526Raw0 : Multiset ℕ) = 1 • (supportNumbers1425 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1425] using hm

private def finish0527Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 928, 929, 930, 931, 932, 933, 934, 935, 992, 993, 994, 995, 996, 997, 998, 999]
private def finish0527Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 160, 161, 162, 163, 164, 165, 166, 167, 224, 225, 226, 227, 228, 229, 230, 231, 0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 160, 161, 162, 163, 164, 165, 166, 167, 224, 225, 226, 227, 228, 229, 230, 231]
private theorem finish0527Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0527Input0) = fromList finish0527Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0527 : finishSupport ⟨true, bits4 4⟩ support1426 = 2 • support1144 := by
  have hs : support1426 = fromList finish0527Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0527Chunk0]
  have hn : (finish0527Raw0 : Multiset ℕ) = 2 • (supportNumbers1144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1144] using hm

private def finish0528Input0 : List ℕ := [0, 1, 4, 5, 26, 27, 30, 31, 64, 65, 68, 69, 90, 91, 94, 95]
private def finish0528Raw0 : List ℕ := [0, 1, 26, 27, 64, 65, 90, 91]
private theorem finish0528Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0528Input0) = fromList finish0528Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0528 : finishSupport ⟨false, bits4 4⟩ support1428 = 1 • support1429 := by
  have hs : support1428 = fromList finish0528Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0528Chunk0]
  have hn : (finish0528Raw0 : Multiset ℕ) = 1 • (supportNumbers1429 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1429] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
