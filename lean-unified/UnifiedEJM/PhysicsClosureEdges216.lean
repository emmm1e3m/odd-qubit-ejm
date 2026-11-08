import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0673Input0 : List ℕ := [0, 1, 4, 5, 18, 19, 22, 23, 64, 65, 68, 69, 82, 83, 86, 87, 130, 131, 134, 135, 144, 145, 148, 149, 194, 195, 198, 199, 208, 209, 212, 213, 514, 515, 518, 519, 528, 529, 532, 533, 578, 579, 582, 583, 592, 593, 596, 597, 640, 641, 644, 645, 658, 659, 662, 663, 704, 705, 708, 709, 722, 723, 726, 727]
private def finish0673Raw0 : List ℕ := [0, 1, 4, 5, 18, 19, 22, 23, 64, 65, 68, 69, 82, 83, 86, 87, 130, 131, 134, 135, 144, 145, 148, 149, 194, 195, 198, 199, 208, 209, 212, 213, 2, 3, 6, 7, 16, 17, 20, 21, 66, 67, 70, 71, 80, 81, 84, 85, 128, 129, 132, 133, 146, 147, 150, 151, 192, 193, 196, 197, 210, 211, 214, 215]
private theorem finish0673Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0673Input0) = fromList finish0673Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0673 : finishSupport ⟨true, bits4 4⟩ support1727 = 1 • support0164 := by
  have hs : support1727 = fromList finish0673Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0673Chunk0]
  have hn : (finish0673Raw0 : Multiset ℕ) = 1 • (supportNumbers0164 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0164] using hm

private def finish0674Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 312, 313, 314, 315, 316, 317, 318, 319, 376, 377, 378, 379, 380, 381, 382, 383, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495]
private def finish0674Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 144, 145, 146, 147, 208, 209, 210, 211, 60, 61, 62, 63, 124, 125, 126, 127, 172, 173, 174, 175, 236, 237, 238, 239]
private theorem finish0674Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0674Input0) = fromList finish0674Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0674 : finishSupport ⟨false, bits4 4⟩ support1730 = 1 • support1731 := by
  have hs : support1730 = fromList finish0674Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0674Chunk0]
  have hn : (finish0674Raw0 : Multiset ℕ) = 1 • (supportNumbers1731 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1731] using hm

private def finish0675Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 312, 313, 314, 315, 316, 317, 318, 319, 376, 377, 378, 379, 380, 381, 382, 383, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495]
private def finish0675Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 56, 57, 58, 59, 60, 61, 62, 63, 120, 121, 122, 123, 124, 125, 126, 127, 168, 169, 170, 171, 172, 173, 174, 175, 232, 233, 234, 235, 236, 237, 238, 239]
private theorem finish0675Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0675Input0) = fromList finish0675Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0675Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 656, 657, 658, 659, 660, 661, 662, 663, 720, 721, 722, 723, 724, 725, 726, 727, 824, 825, 826, 827, 828, 829, 830, 831, 888, 889, 890, 891, 892, 893, 894, 895, 936, 937, 938, 939, 940, 941, 942, 943, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]
private def finish0675Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 56, 57, 58, 59, 60, 61, 62, 63, 120, 121, 122, 123, 124, 125, 126, 127, 168, 169, 170, 171, 172, 173, 174, 175, 232, 233, 234, 235, 236, 237, 238, 239]
private theorem finish0675Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0675Input1) = fromList finish0675Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0675 : finishSupport ⟨true, bits4 4⟩ support1732 = 2 • support1733 := by
  have hs : support1732 = fromList finish0675Input0 + fromList finish0675Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0675Chunk0, finish0675Chunk1]
  have hn : (finish0675Raw0 : Multiset ℕ) + (finish0675Raw1 : Multiset ℕ) = 2 • (supportNumbers1733 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1733] using hm

private def finish0676Input0 : List ℕ := [0, 2, 9, 11, 416, 418, 425, 427]
private def finish0676Raw0 : List ℕ := [0, 2, 9, 11]
private theorem finish0676Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0676Input0) = fromList finish0676Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0676 : finishSupport ⟨false, bits4 4⟩ support1739 = 1 • support0175 := by
  have hs : support1739 = fromList finish0676Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0676Chunk0]
  have hn : (finish0676Raw0 : Multiset ℕ) = 1 • (supportNumbers0175 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0175] using hm

private def finish0677Input0 : List ℕ := [0, 2, 9, 11, 416, 418, 425, 427, 576, 578, 585, 587, 992, 994, 1001, 1003]
private def finish0677Raw0 : List ℕ := [0, 2, 9, 11, 160, 162, 169, 171, 64, 66, 73, 75, 224, 226, 233, 235]
private theorem finish0677Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0677Input0) = fromList finish0677Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0677 : finishSupport ⟨true, bits4 4⟩ support1740 = 1 • support1741 := by
  have hs : support1740 = fromList finish0677Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0677Chunk0]
  have hn : (finish0677Raw0 : Multiset ℕ) = 1 • (supportNumbers1741 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1741] using hm

private def finish0678Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 308, 309, 310, 311, 416, 417, 418, 419]
private def finish0678Raw0 : List ℕ := [0, 1, 2, 3, 52, 53, 54, 55]
private theorem finish0678Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0678Input0) = fromList finish0678Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0678 : finishSupport ⟨false, bits4 4⟩ support1747 = 1 • support0498 := by
  have hs : support1747 = fromList finish0678Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0678Chunk0]
  have hn : (finish0678Raw0 : Multiset ℕ) = 1 • (supportNumbers0498 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0498] using hm

private def finish0679Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 308, 309, 310, 311, 416, 417, 418, 419, 576, 577, 578, 579, 724, 725, 726, 727, 884, 885, 886, 887, 992, 993, 994, 995]
private def finish0679Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 52, 53, 54, 55, 160, 161, 162, 163, 64, 65, 66, 67, 212, 213, 214, 215, 116, 117, 118, 119, 224, 225, 226, 227]
private theorem finish0679Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0679Input0) = fromList finish0679Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0679 : finishSupport ⟨true, bits4 4⟩ support1748 = 1 • support1749 := by
  have hs : support1748 = fromList finish0679Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0679Chunk0]
  have hn : (finish0679Raw0 : Multiset ℕ) = 1 • (supportNumbers1749 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1749] using hm

private def finish0680Input0 : List ℕ := [0, 1, 10, 11, 148, 149, 158, 159]
private def finish0680Raw0 : List ℕ := [0, 1, 10, 11]
private theorem finish0680Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0680Input0) = fromList finish0680Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0680 : finishSupport ⟨false, bits4 4⟩ support1750 = 1 • support0885 := by
  have hs : support1750 = fromList finish0680Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0680Chunk0]
  have hn : (finish0680Raw0 : Multiset ℕ) = 1 • (supportNumbers0885 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0885] using hm

private def finish0681Input0 : List ℕ := [0, 1, 10, 11, 148, 149, 158, 159, 578, 579, 584, 585, 726, 727, 732, 733]
private def finish0681Raw0 : List ℕ := [0, 1, 10, 11, 148, 149, 158, 159, 66, 67, 72, 73, 214, 215, 220, 221]
private theorem finish0681Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0681Input0) = fromList finish0681Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0681 : finishSupport ⟨true, bits4 4⟩ support1751 = 1 • support1752 := by
  have hs : support1751 = fromList finish0681Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0681Chunk0]
  have hn : (finish0681Raw0 : Multiset ℕ) = 1 • (supportNumbers1752 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1752] using hm

private def finish0682Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 416, 418, 420, 422, 425, 427, 429, 431, 481, 483, 485, 487, 488, 490, 492, 494]
private def finish0682Raw0 : List ℕ := [0, 2, 9, 11, 65, 67, 72, 74, 164, 166, 173, 175, 229, 231, 236, 238]
private theorem finish0682Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0682Input0) = fromList finish0682Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0682 : finishSupport ⟨false, bits4 4⟩ support1755 = 1 • support1756 := by
  have hs : support1755 = fromList finish0682Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0682Chunk0]
  have hn : (finish0682Raw0 : Multiset ℕ) = 1 • (supportNumbers1756 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1756] using hm

private def finish0683Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 416, 418, 420, 422, 425, 427, 429, 431, 481, 483, 485, 487, 488, 490, 492, 494, 513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 929, 931, 933, 935, 936, 938, 940, 942, 992, 994, 996, 998, 1001, 1003, 1005, 1007]
private def finish0683Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 160, 162, 164, 166, 169, 171, 173, 175, 225, 227, 229, 231, 232, 234, 236, 238, 1, 3, 5, 7, 8, 10, 12, 14, 64, 66, 68, 70, 73, 75, 77, 79, 161, 163, 165, 167, 168, 170, 172, 174, 224, 226, 228, 230, 233, 235, 237, 239]
private theorem finish0683Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0683Input0) = fromList finish0683Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0683 : finishSupport ⟨true, bits4 4⟩ support1757 = 1 • support0927 := by
  have hs : support1757 = fromList finish0683Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0683Chunk0]
  have hn : (finish0683Raw0 : Multiset ℕ) = 1 • (supportNumbers0927 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0927] using hm

private def finish0684Input0 : List ℕ := [0, 4, 11, 15, 65, 69, 74, 78, 128, 132, 139, 143, 193, 197, 202, 206]
private def finish0684Raw0 : List ℕ := [0, 11, 65, 74, 128, 139, 193, 202]
private theorem finish0684Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0684Input0) = fromList finish0684Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0684 : finishSupport ⟨false, bits4 4⟩ support1758 = 1 • support1759 := by
  have hs : support1758 = fromList finish0684Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0684Chunk0]
  have hn : (finish0684Raw0 : Multiset ℕ) = 1 • (supportNumbers1759 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1759] using hm

private def finish0685Input0 : List ℕ := [0, 4, 11, 15, 65, 69, 74, 78, 128, 132, 139, 143, 193, 197, 202, 206, 515, 519, 520, 524, 578, 582, 585, 589, 643, 647, 648, 652, 706, 710, 713, 717]
private def finish0685Raw0 : List ℕ := [0, 4, 11, 15, 65, 69, 74, 78, 128, 132, 139, 143, 193, 197, 202, 206, 3, 7, 8, 12, 66, 70, 73, 77, 131, 135, 136, 140, 194, 198, 201, 205]
private theorem finish0685Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0685Input0) = fromList finish0685Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0685 : finishSupport ⟨true, bits4 4⟩ support1760 = 1 • support0522 := by
  have hs : support1760 = fromList finish0685Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0685Chunk0]
  have hn : (finish0685Raw0 : Multiset ℕ) = 1 • (supportNumbers0522 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0522] using hm

private def finish0686Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 304, 305, 306, 307, 308, 309, 310, 311, 368, 369, 370, 371, 372, 373, 374, 375, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487]
private def finish0686Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 144, 145, 146, 147, 208, 209, 210, 211, 52, 53, 54, 55, 116, 117, 118, 119, 164, 165, 166, 167, 228, 229, 230, 231]
private theorem finish0686Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0686Input0) = fromList finish0686Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0686 : finishSupport ⟨false, bits4 4⟩ support1766 = 1 • support1767 := by
  have hs : support1766 = fromList finish0686Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0686Chunk0]
  have hn : (finish0686Raw0 : Multiset ℕ) = 1 • (supportNumbers1767 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1767] using hm

private def finish0687Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 304, 305, 306, 307, 308, 309, 310, 311, 368, 369, 370, 371, 372, 373, 374, 375, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487]
private def finish0687Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 48, 49, 50, 51, 52, 53, 54, 55, 112, 113, 114, 115, 116, 117, 118, 119, 160, 161, 162, 163, 164, 165, 166, 167, 224, 225, 226, 227, 228, 229, 230, 231]
private theorem finish0687Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0687Input0) = fromList finish0687Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0687Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 656, 657, 658, 659, 660, 661, 662, 663, 720, 721, 722, 723, 724, 725, 726, 727, 816, 817, 818, 819, 820, 821, 822, 823, 880, 881, 882, 883, 884, 885, 886, 887, 928, 929, 930, 931, 932, 933, 934, 935, 992, 993, 994, 995, 996, 997, 998, 999]
private def finish0687Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 48, 49, 50, 51, 52, 53, 54, 55, 112, 113, 114, 115, 116, 117, 118, 119, 160, 161, 162, 163, 164, 165, 166, 167, 224, 225, 226, 227, 228, 229, 230, 231]
private theorem finish0687Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0687Input1) = fromList finish0687Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0687 : finishSupport ⟨true, bits4 4⟩ support1768 = 2 • support1769 := by
  have hs : support1768 = fromList finish0687Input0 + fromList finish0687Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0687Chunk0, finish0687Chunk1]
  have hn : (finish0687Raw0 : Multiset ℕ) + (finish0687Raw1 : Multiset ℕ) = 2 • (supportNumbers1769 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1769] using hm

private def finish0688Input0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 64, 65, 68, 69, 74, 75, 78, 79, 144, 145, 148, 149, 154, 155, 158, 159, 208, 209, 212, 213, 218, 219, 222, 223]
private def finish0688Raw0 : List ℕ := [0, 1, 10, 11, 64, 65, 74, 75, 144, 145, 154, 155, 208, 209, 218, 219]
private theorem finish0688Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0688Input0) = fromList finish0688Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0688 : finishSupport ⟨false, bits4 4⟩ support1770 = 1 • support1771 := by
  have hs : support1770 = fromList finish0688Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0688Chunk0]
  have hn : (finish0688Raw0 : Multiset ℕ) = 1 • (supportNumbers1771 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1771] using hm

private def finish0689Input0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 64, 65, 68, 69, 74, 75, 78, 79, 144, 145, 148, 149, 154, 155, 158, 159, 208, 209, 212, 213, 218, 219, 222, 223, 514, 515, 518, 519, 520, 521, 524, 525, 578, 579, 582, 583, 584, 585, 588, 589, 658, 659, 662, 663, 664, 665, 668, 669, 722, 723, 726, 727, 728, 729, 732, 733]
private def finish0689Raw0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 64, 65, 68, 69, 74, 75, 78, 79, 144, 145, 148, 149, 154, 155, 158, 159, 208, 209, 212, 213, 218, 219, 222, 223, 2, 3, 6, 7, 8, 9, 12, 13, 66, 67, 70, 71, 72, 73, 76, 77, 146, 147, 150, 151, 152, 153, 156, 157, 210, 211, 214, 215, 216, 217, 220, 221]
private theorem finish0689Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0689Input0) = fromList finish0689Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0689 : finishSupport ⟨true, bits4 4⟩ support1772 = 1 • support0157 := by
  have hs : support1772 = fromList finish0689Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0689Chunk0]
  have hn : (finish0689Raw0 : Multiset ℕ) = 1 • (supportNumbers0157 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0157] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
