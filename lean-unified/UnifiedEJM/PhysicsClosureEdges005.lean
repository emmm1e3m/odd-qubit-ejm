import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0133Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition0133Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 392, 776, 394, 778, 396, 780, 398, 782, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition0133Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0133Input0) = fromList transition0133Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0133 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0017 = 1 • support0039 := by
  have hs : support0017 = fromList transition0133Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0133Chunk0]
  have hn : (transition0133Raw0 : Multiset ℕ) = 1 • (supportNumbers0039 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0039] using hm

private def transition0134Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition0134Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition0134Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0134Input0) = fromList transition0134Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0134 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0017 = 1 • support0038 := by
  have hs : support0017 = fromList transition0134Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0134Chunk0]
  have hn : (transition0134Raw0 : Multiset ℕ) = 1 • (supportNumbers0038 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0038] using hm

private def transition0135Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition0135Raw0 : List ℕ := [0, 4, 65, 69, 138, 142, 203, 207]
private theorem transition0135Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0135Input0) = fromList transition0135Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0135 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0038 = 1 • support0596 := by
  have hs : support0038 = fromList transition0135Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0135Chunk0]
  have hn : (transition0135Raw0 : Multiset ℕ) = 1 • (supportNumbers0596 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0596] using hm

private def transition0136Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition0136Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 712, 138, 716, 142, 649, 203, 653, 207]
private theorem transition0136Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0136Input0) = fromList transition0136Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0136 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0038 = 1 • support0598 := by
  have hs : support0038 = fromList transition0136Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0136Chunk0]
  have hn : (transition0136Raw0 : Multiset ℕ) = 1 • (supportNumbers0598 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0598] using hm

private def transition0137Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition0137Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 392, 936, 394, 938, 396, 940, 398, 942, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition0137Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0137Input0) = fromList transition0137Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0137 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0017 = 1 • support0600 := by
  have hs : support0017 = fromList transition0137Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0137Chunk0]
  have hn : (transition0137Raw0 : Multiset ℕ) = 1 • (supportNumbers0600 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0600] using hm

private def transition0138Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 392, 394, 396, 398, 457, 459, 461, 463, 544, 546, 548, 550, 609, 611, 613, 615, 936, 938, 940, 942, 1001, 1003, 1005, 1007]
private def transition0138Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 288, 290, 292, 294, 353, 355, 357, 359, 424, 426, 428, 430, 489, 491, 493, 495]
private theorem transition0138Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0138Input0) = fromList transition0138Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0138 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0600 = 1 • support0601 := by
  have hs : support0600 = fromList transition0138Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0138Chunk0]
  have hn : (transition0138Raw0 : Multiset ℕ) = 1 • (supportNumbers0601 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0601] using hm

private def transition0139Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 392, 394, 396, 398, 457, 459, 461, 463, 544, 546, 548, 550, 609, 611, 613, 615, 936, 938, 940, 942, 1001, 1003, 1005, 1007]
private def transition0139Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 136, 712, 138, 714, 140, 716, 142, 718, 201, 649, 203, 651, 205, 653, 207, 655, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition0139Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0139Input0) = fromList transition0139Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0139 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0600 = 1 • support0603 := by
  have hs : support0600 = fromList transition0139Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0139Chunk0]
  have hn : (transition0139Raw0 : Multiset ℕ) = 1 • (supportNumbers0603 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0603] using hm

private def transition0140Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition0140Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition0140Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0140Input0) = fromList transition0140Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0140 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0018 = 1 • support0040 := by
  have hs : support0018 = fromList transition0140Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0140Chunk0]
  have hn : (transition0140Raw0 : Multiset ℕ) = 1 • (supportNumbers0040 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0040] using hm

private def transition0141Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition0141Raw0 : List ℕ := [0, 2, 4, 6, 648, 650, 652, 654, 65, 67, 69, 71, 713, 715, 717, 719, 513, 515, 517, 519, 137, 139, 141, 143, 576, 578, 580, 582, 200, 202, 204, 206]
private theorem transition0141Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0141Input0) = fromList transition0141Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0141 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0018 = 1 • support0041 := by
  have hs : support0018 = fromList transition0141Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0141Chunk0]
  have hn : (transition0141Raw0 : Multiset ℕ) = 1 • (supportNumbers0041 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0041] using hm

private def transition0142Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition0142Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition0142Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0142Input0) = fromList transition0142Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0142 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0018 = 1 • support0040 := by
  have hs : support0018 = fromList transition0142Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0142Chunk0]
  have hn : (transition0142Raw0 : Multiset ℕ) = 1 • (supportNumbers0040 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0040] using hm

private def transition0143Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private def transition0143Raw0 : List ℕ := [0, 4, 65, 69, 137, 141, 200, 204]
private theorem transition0143Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0143Input0) = fromList transition0143Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0143 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0040 = 1 • support0605 := by
  have hs : support0040 = fromList transition0143Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0143Chunk0]
  have hn : (transition0143Raw0 : Multiset ℕ) = 1 • (supportNumbers0605 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0605] using hm

private def transition0144Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private def transition0144Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 137, 715, 141, 719, 200, 650, 204, 654]
private theorem transition0144Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0144Input0) = fromList transition0144Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0144 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0040 = 1 • support0607 := by
  have hs : support0040 = fromList transition0144Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0144Chunk0]
  have hn : (transition0144Raw0 : Multiset ℕ) = 1 • (supportNumbers0607 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0607] using hm

private def transition0145Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition0145Raw0 : List ℕ := [0, 2, 4, 6, 552, 554, 556, 558, 65, 67, 69, 71, 617, 619, 621, 623, 673, 675, 677, 679, 137, 139, 141, 143, 736, 738, 740, 742, 200, 202, 204, 206]
private theorem transition0145Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0145Input0) = fromList transition0145Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0145 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0018 = 1 • support0608 := by
  have hs : support0018 = fromList transition0145Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0145Chunk0]
  have hn : (transition0145Raw0 : Multiset ℕ) = 1 • (supportNumbers0608 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0608] using hm

private def transition0146Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 552, 554, 556, 558, 617, 619, 621, 623, 673, 675, 677, 679, 736, 738, 740, 742]
private def transition0146Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 296, 298, 300, 302, 361, 363, 365, 367, 417, 419, 421, 423, 480, 482, 484, 486]
private theorem transition0146Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0146Input0) = fromList transition0146Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0146 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0608 = 1 • support0609 := by
  have hs : support0608 = fromList transition0146Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0146Chunk0]
  have hn : (transition0146Raw0 : Multiset ℕ) = 1 • (supportNumbers0609 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0609] using hm

private def transition0147Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 552, 554, 556, 558, 617, 619, 621, 623, 673, 675, 677, 679, 736, 738, 740, 742]
private def transition0147Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 137, 713, 139, 715, 141, 717, 143, 719, 200, 648, 202, 650, 204, 652, 206, 654, 296, 872, 298, 874, 300, 876, 302, 878, 361, 809, 363, 811, 365, 813, 367, 815, 417, 993, 419, 995, 421, 997, 423, 999, 480, 928, 482, 930, 484, 932, 486, 934]
private theorem transition0147Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0147Input0) = fromList transition0147Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0147 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0608 = 1 • support0611 := by
  have hs : support0608 = fromList transition0147Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0147Chunk0]
  have hn : (transition0147Raw0 : Multiset ℕ) = 1 • (supportNumbers0611 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0611] using hm

private def transition0148Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 769, 771, 773, 775, 777, 779, 781, 783, 832, 834, 836, 838, 840, 842, 844, 846]
private def transition0148Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334]
private theorem transition0148Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0148Input0) = fromList transition0148Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0148 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0019 = 1 • support0042 := by
  have hs : support0019 = fromList transition0148Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0148Chunk0]
  have hn : (transition0148Raw0 : Multiset ℕ) = 1 • (supportNumbers0042 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0042] using hm

private def transition0149Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 769, 771, 773, 775, 777, 779, 781, 783, 832, 834, 836, 838, 840, 842, 844, 846]
private def transition0149Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 129, 513, 131, 515, 133, 517, 135, 519, 137, 521, 139, 523, 141, 525, 143, 527, 192, 576, 194, 578, 196, 580, 198, 582, 200, 584, 202, 586, 204, 588, 206, 590, 384, 768, 386, 770, 388, 772, 390, 774, 392, 776, 394, 778, 396, 780, 398, 782, 449, 833, 451, 835, 453, 837, 455, 839, 457, 841, 459, 843, 461, 845, 463, 847, 257, 897, 259, 899, 261, 901, 263, 903, 265, 905, 267, 907, 269, 909, 271, 911, 320, 960, 322, 962, 324, 964, 326, 966, 328, 968, 330, 970, 332, 972, 334, 974]
private theorem transition0149Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0149Input0) = fromList transition0149Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0149 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0019 = 1 • support0043 := by
  have hs : support0019 = fromList transition0149Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0149Chunk0]
  have hn : (transition0149Raw0 : Multiset ℕ) = 1 • (supportNumbers0043 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0043] using hm

private def transition0150Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 769, 771, 773, 775, 777, 779, 781, 783, 832, 834, 836, 838, 840, 842, 844, 846]
private def transition0150Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334]
private theorem transition0150Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0150Input0) = fromList transition0150Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0150 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0019 = 1 • support0042 := by
  have hs : support0019 = fromList transition0150Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0150Chunk0]
  have hn : (transition0150Raw0 : Multiset ℕ) = 1 • (supportNumbers0042 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0042] using hm

private def transition0151Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition0151Raw0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 129, 133, 137, 141, 192, 196, 200, 204, 3, 7, 11, 15, 66, 70, 74, 78, 130, 134, 138, 142, 195, 199, 203, 207]
private theorem transition0151Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0151Input0) = fromList transition0151Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0151 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0042 = 1 • support0613 := by
  have hs : support0042 = fromList transition0151Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0151Chunk0]
  have hn : (transition0151Raw0 : Multiset ℕ) = 1 • (supportNumbers0613 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0613] using hm

private def transition0152Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition0152Raw0 : List ℕ := [0, 578, 4, 582, 8, 586, 12, 590, 65, 515, 69, 519, 73, 523, 77, 527, 129, 707, 133, 711, 137, 715, 141, 719, 192, 642, 196, 646, 200, 650, 204, 654, 577, 3, 581, 7, 585, 11, 589, 15, 512, 66, 516, 70, 520, 74, 524, 78, 704, 130, 708, 134, 712, 138, 716, 142, 641, 195, 645, 199, 649, 203, 653, 207]
private theorem transition0152Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0152Input0) = fromList transition0152Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0152 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0042 = 1 • support0614 := by
  have hs : support0042 = fromList transition0152Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0152Chunk0]
  have hn : (transition0152Raw0 : Multiset ℕ) = 1 • (supportNumbers0614 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0614] using hm

private def transition0153Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 769, 771, 773, 775, 777, 779, 781, 783, 832, 834, 836, 838, 840, 842, 844, 846]
private def transition0153Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623, 129, 673, 131, 675, 133, 677, 135, 679, 137, 681, 139, 683, 141, 685, 143, 687, 192, 736, 194, 738, 196, 740, 198, 742, 200, 744, 202, 746, 204, 748, 206, 750, 384, 928, 386, 930, 388, 932, 390, 934, 392, 936, 394, 938, 396, 940, 398, 942, 449, 993, 451, 995, 453, 997, 455, 999, 457, 1001, 459, 1003, 461, 1005, 463, 1007, 257, 801, 259, 803, 261, 805, 263, 807, 265, 809, 267, 811, 269, 813, 271, 815, 320, 864, 322, 866, 324, 868, 326, 870, 328, 872, 330, 874, 332, 876, 334, 878]
private theorem transition0153Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0153Input0) = fromList transition0153Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0153 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0019 = 1 • support0615 := by
  have hs : support0019 = fromList transition0153Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0153Chunk0]
  have hn : (transition0153Raw0 : Multiset ℕ) = 1 • (supportNumbers0615 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0615] using hm

private def transition0154Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition0154Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 1, 3, 5, 7, 9, 11, 13, 15, 64, 66, 68, 70, 72, 74, 76, 78, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private theorem transition0154Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0154Input0) = fromList transition0154Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0154Input1 : List ℕ := [544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623, 673, 675, 677, 679, 681, 683, 685, 687, 736, 738, 740, 742, 744, 746, 748, 750, 801, 803, 805, 807, 809, 811, 813, 815, 864, 866, 868, 870, 872, 874, 876, 878, 928, 930, 932, 934, 936, 938, 940, 942, 993, 995, 997, 999, 1001, 1003, 1005, 1007]
private def transition0154Raw1 : List ℕ := [288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367, 417, 419, 421, 423, 425, 427, 429, 431, 480, 482, 484, 486, 488, 490, 492, 494, 289, 291, 293, 295, 297, 299, 301, 303, 352, 354, 356, 358, 360, 362, 364, 366, 416, 418, 420, 422, 424, 426, 428, 430, 481, 483, 485, 487, 489, 491, 493, 495]
private theorem transition0154Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0154Input1) = fromList transition0154Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0154 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0615 = 1 • support0616 := by
  have hs : support0615 = fromList transition0154Input0 + fromList transition0154Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0154Chunk0, transition0154Chunk1]
  have hn : (transition0154Raw0 : Multiset ℕ) + (transition0154Raw1 : Multiset ℕ) = 1 • (supportNumbers0616 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0616] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
