import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1118Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1118Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 64, 65, 514, 515, 68, 69, 518, 519, 704, 705, 130, 131, 708, 709, 134, 135, 640, 641, 194, 195, 644, 645, 198, 199]
private theorem transition1118Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1118Input0) = fromList transition1118Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1118 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0231 = 1 • support1202 := by
  have hs : support0231 = fromList transition1118Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1118Chunk0]
  have hn : (transition1118Raw0 : Multiset ℕ) = 1 • (supportNumbers1202 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1202] using hm

private def transition1119Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711]
private def transition1119Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999]
private theorem transition1119Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1119Input0) = fromList transition1119Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1119 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0150 = 1 • support1203 := by
  have hs : support0150 = fromList transition1119Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1119Chunk0]
  have hn : (transition1119Raw0 : Multiset ℕ) = 1 • (supportNumbers1203 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1203] using hm

private def transition1120Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 928, 929, 930, 931, 932, 933, 934, 935, 992, 993, 994, 995, 996, 997, 998, 999]
private def transition1120Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487]
private theorem transition1120Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1120Input0) = fromList transition1120Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1120 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1203 = 1 • support1204 := by
  have hs : support1203 = fromList transition1120Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1120Chunk0]
  have hn : (transition1120Raw0 : Multiset ℕ) = 1 • (supportNumbers1204 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1204] using hm

private def transition1121Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 928, 929, 930, 931, 932, 933, 934, 935, 992, 993, 994, 995, 996, 997, 998, 999]
private def transition1121Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 128, 704, 129, 705, 130, 706, 131, 707, 132, 708, 133, 709, 134, 710, 135, 711, 192, 640, 193, 641, 194, 642, 195, 643, 196, 644, 197, 645, 198, 646, 199, 647, 288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 416, 992, 417, 993, 418, 994, 419, 995, 420, 996, 421, 997, 422, 998, 423, 999, 480, 928, 481, 929, 482, 930, 483, 931, 484, 932, 485, 933, 486, 934, 487, 935]
private theorem transition1121Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1121Input0) = fromList transition1121Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1121 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1203 = 1 • support1206 := by
  have hs : support1203 = fromList transition1121Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1121Chunk0]
  have hn : (transition1121Raw0 : Multiset ℕ) = 1 • (supportNumbers1206 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1206] using hm

private def transition1122Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1122Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71]
private theorem transition1122Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1122Input0) = fromList transition1122Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1122 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0151 = 1 • support0044 := by
  have hs : support0151 = fromList transition1122Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1122Chunk0]
  have hn : (transition1122Raw0 : Multiset ℕ) = 1 • (supportNumbers0044 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0044] using hm

private def transition1123Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1123Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 536, 537, 538, 539, 540, 541, 542, 543, 600, 601, 602, 603, 604, 605, 606, 607]
private theorem transition1123Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1123Input0) = fromList transition1123Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1123 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0151 = 1 • support0233 := by
  have hs : support0151 = fromList transition1123Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1123Chunk0]
  have hn : (transition1123Raw0 : Multiset ℕ) = 1 • (supportNumbers0233 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0233] using hm

private def transition1124Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1124Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71]
private theorem transition1124Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1124Input0) = fromList transition1124Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1124 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0151 = 1 • support0044 := by
  have hs : support0151 = fromList transition1124Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1124Chunk0]
  have hn : (transition1124Raw0 : Multiset ℕ) = 1 • (supportNumbers0044 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0044] using hm

private def transition1125Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1125Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 696, 697, 698, 699, 700, 701, 702, 703, 760, 761, 762, 763, 764, 765, 766, 767]
private theorem transition1125Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1125Input0) = fromList transition1125Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1125 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0151 = 1 • support1207 := by
  have hs : support0151 = fromList transition1125Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1125Chunk0]
  have hn : (transition1125Raw0 : Multiset ℕ) = 1 • (supportNumbers1207 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1207] using hm

private def transition1126Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 696, 697, 698, 699, 700, 701, 702, 703, 760, 761, 762, 763, 764, 765, 766, 767]
private def transition1126Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 440, 441, 442, 443, 444, 445, 446, 447, 504, 505, 506, 507, 508, 509, 510, 511]
private theorem transition1126Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1126Input0) = fromList transition1126Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1126 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1207 = 1 • support1208 := by
  have hs : support1207 = fromList transition1126Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1126Chunk0]
  have hn : (transition1126Raw0 : Multiset ℕ) = 1 • (supportNumbers1208 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1208] using hm

private def transition1127Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 696, 697, 698, 699, 700, 701, 702, 703, 760, 761, 762, 763, 764, 765, 766, 767]
private def transition1127Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 440, 1016, 441, 1017, 442, 1018, 443, 1019, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 504, 952, 505, 953, 506, 954, 507, 955, 508, 956, 509, 957, 510, 958, 511, 959]
private theorem transition1127Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1127Input0) = fromList transition1127Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1127 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1207 = 1 • support1209 := by
  have hs : support1207 = fromList transition1127Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1127Chunk0]
  have hn : (transition1127Raw0 : Multiset ℕ) = 1 • (supportNumbers1209 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1209] using hm

private def transition1128Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1128Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition1128Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1128Input0) = fromList transition1128Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1128 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0151 = 1 • support0151 := by
  have hs : support0151 = fromList transition1128Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1128Chunk0]
  have hn : (transition1128Raw0 : Multiset ℕ) = 1 • (supportNumbers0151 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0151] using hm

private def transition1129Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1129Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 152, 536, 153, 537, 154, 538, 155, 539, 156, 540, 157, 541, 158, 542, 159, 543, 216, 600, 217, 601, 218, 602, 219, 603, 220, 604, 221, 605, 222, 606, 223, 607]
private theorem transition1129Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1129Input0) = fromList transition1129Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1129 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0151 = 1 • support0234 := by
  have hs : support0151 = fromList transition1129Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1129Chunk0]
  have hn : (transition1129Raw0 : Multiset ℕ) = 1 • (supportNumbers0234 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0234] using hm

private def transition1130Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1130Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition1130Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1130Input0) = fromList transition1130Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1130 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0151 = 1 • support0151 := by
  have hs : support0151 = fromList transition1130Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1130Chunk0]
  have hn : (transition1130Raw0 : Multiset ℕ) = 1 • (supportNumbers0151 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0151] using hm

private def transition1131Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1131Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition1131Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1131Input0) = fromList transition1131Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1131 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0151 = 1 • support1211 := by
  have hs : support0151 = fromList transition1131Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1131Chunk0]
  have hn : (transition1131Raw0 : Multiset ℕ) = 1 • (supportNumbers1211 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1211] using hm

private def transition1132Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 696, 697, 698, 699, 700, 701, 702, 703, 760, 761, 762, 763, 764, 765, 766, 767]
private def transition1132Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 440, 441, 442, 443, 444, 445, 446, 447, 504, 505, 506, 507, 508, 509, 510, 511]
private theorem transition1132Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1132Input0) = fromList transition1132Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1132 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1211 = 1 • support0762 := by
  have hs : support1211 = fromList transition1132Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1132Chunk0]
  have hn : (transition1132Raw0 : Multiset ℕ) = 1 • (supportNumbers0762 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0762] using hm

private def transition1133Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 696, 697, 698, 699, 700, 701, 702, 703, 760, 761, 762, 763, 764, 765, 766, 767]
private def transition1133Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 152, 728, 153, 729, 154, 730, 155, 731, 156, 732, 157, 733, 158, 734, 159, 735, 216, 664, 217, 665, 218, 666, 219, 667, 220, 668, 221, 669, 222, 670, 223, 671, 288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 440, 1016, 441, 1017, 442, 1018, 443, 1019, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 504, 952, 505, 953, 506, 954, 507, 955, 508, 956, 509, 957, 510, 958, 511, 959]
private theorem transition1133Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1133Input0) = fromList transition1133Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1133 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1211 = 1 • support0764 := by
  have hs : support1211 = fromList transition1133Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1133Chunk0]
  have hn : (transition1133Raw0 : Multiset ℕ) = 1 • (supportNumbers0764 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0764] using hm

private def transition1134Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1134Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition1134Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1134Input0) = fromList transition1134Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1134 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0152 = 1 • support0020 := by
  have hs : support0152 = fromList transition1134Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1134Chunk0]
  have hn : (transition1134Raw0 : Multiset ℕ) = 1 • (supportNumbers0020 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0020] using hm

private def transition1135Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1135Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 536, 537, 538, 539, 540, 541, 542, 543, 600, 601, 602, 603, 604, 605, 606, 607, 24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583]
private theorem transition1135Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1135Input0) = fromList transition1135Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1135 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0152 = 1 • support0235 := by
  have hs : support0152 = fromList transition1135Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1135Chunk0]
  have hn : (transition1135Raw0 : Multiset ℕ) = 1 • (supportNumbers0235 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0235] using hm

private def transition1136Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1136Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition1136Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1136Input0) = fromList transition1136Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1136 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0152 = 1 • support0020 := by
  have hs : support0152 = fromList transition1136Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1136Chunk0]
  have hn : (transition1136Raw0 : Multiset ℕ) = 1 • (supportNumbers0020 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0020] using hm

private def transition1137Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1137Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 696, 697, 698, 699, 700, 701, 702, 703, 760, 761, 762, 763, 764, 765, 766, 767, 24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95, 672, 673, 674, 675, 676, 677, 678, 679, 736, 737, 738, 739, 740, 741, 742, 743]
private theorem transition1137Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1137Input0) = fromList transition1137Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1137 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0152 = 1 • support1212 := by
  have hs : support0152 = fromList transition1137Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1137Chunk0]
  have hn : (transition1137Raw0 : Multiset ℕ) = 1 • (supportNumbers1212 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1212] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
