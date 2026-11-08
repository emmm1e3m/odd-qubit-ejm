import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0365Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 576, 577, 578, 579, 596, 597, 598, 599, 704, 705, 706, 707, 724, 725, 726, 727]
private def finish0365Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 64, 65, 66, 67, 84, 85, 86, 87, 192, 193, 194, 195, 212, 213, 214, 215]
private theorem finish0365Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0365Input0) = fromList finish0365Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0365 : finishSupport ⟨true, bits4 4⟩ support1133 = 1 • support1134 := by
  have hs : support1133 = fromList finish0365Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0365Chunk0]
  have hn : (finish0365Raw0 : Multiset ℕ) = 1 • (supportNumbers1134 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1134] using hm

private def finish0366Input0 : List ℕ := [0, 1, 10, 11, 20, 21, 30, 31, 128, 129, 138, 139, 148, 149, 158, 159]
private def finish0366Raw0 : List ℕ := [0, 1, 10, 11, 128, 129, 138, 139]
private theorem finish0366Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0366Input0) = fromList finish0366Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0366 : finishSupport ⟨false, bits4 4⟩ support1135 = 1 • support1136 := by
  have hs : support1135 = fromList finish0366Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0366Chunk0]
  have hn : (finish0366Raw0 : Multiset ℕ) = 1 • (supportNumbers1136 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1136] using hm

private def finish0367Input0 : List ℕ := [0, 1, 10, 11, 20, 21, 30, 31, 128, 129, 138, 139, 148, 149, 158, 159, 578, 579, 584, 585, 598, 599, 604, 605, 706, 707, 712, 713, 726, 727, 732, 733]
private def finish0367Raw0 : List ℕ := [0, 1, 10, 11, 20, 21, 30, 31, 128, 129, 138, 139, 148, 149, 158, 159, 66, 67, 72, 73, 86, 87, 92, 93, 194, 195, 200, 201, 214, 215, 220, 221]
private theorem finish0367Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0367Input0) = fromList finish0367Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0367 : finishSupport ⟨true, bits4 4⟩ support1137 = 1 • support1138 := by
  have hs : support1137 = fromList finish0367Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0367Chunk0]
  have hn : (finish0367Raw0 : Multiset ℕ) = 1 • (supportNumbers1138 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1138] using hm

private def finish0368Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 416, 418, 420, 422, 481, 483, 485, 487]
private def finish0368Raw0 : List ℕ := [0, 2, 65, 67, 164, 166, 229, 231]
private theorem finish0368Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0368Input0) = fromList finish0368Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0368 : finishSupport ⟨false, bits4 4⟩ support1141 = 1 • support1142 := by
  have hs : support1141 = fromList finish0368Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0368Chunk0]
  have hn : (finish0368Raw0 : Multiset ℕ) = 1 • (supportNumbers1142 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1142] using hm

private def finish0369Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 416, 418, 420, 422, 481, 483, 485, 487, 513, 515, 517, 519, 576, 578, 580, 582, 929, 931, 933, 935, 992, 994, 996, 998]
private def finish0369Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 160, 162, 164, 166, 225, 227, 229, 231, 1, 3, 5, 7, 64, 66, 68, 70, 161, 163, 165, 167, 224, 226, 228, 230]
private theorem finish0369Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0369Input0) = fromList finish0369Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0369 : finishSupport ⟨true, bits4 4⟩ support1143 = 1 • support1144 := by
  have hs : support1143 = fromList finish0369Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0369Chunk0]
  have hn : (finish0369Raw0 : Multiset ℕ) = 1 • (supportNumbers1144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1144] using hm

private def finish0370Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private def finish0370Raw0 : List ℕ := [0, 2, 65, 67, 128, 130, 193, 195]
private theorem finish0370Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0370Input0) = fromList finish0370Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0370 : finishSupport ⟨false, bits4 4⟩ support0299 = 1 • support1145 := by
  have hs : support0299 = fromList finish0370Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0370Chunk0]
  have hn : (finish0370Raw0 : Multiset ℕ) = 1 • (supportNumbers1145 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1145] using hm

private def finish0371Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 513, 515, 517, 519, 576, 578, 580, 582, 641, 643, 645, 647, 704, 706, 708, 710]
private def finish0371Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 1, 3, 5, 7, 64, 66, 68, 70, 129, 131, 133, 135, 192, 194, 196, 198]
private theorem finish0371Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0371Input0) = fromList finish0371Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0371 : finishSupport ⟨true, bits4 4⟩ support1146 = 1 • support0229 := by
  have hs : support1146 = fromList finish0371Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0371Chunk0]
  have hn : (finish0371Raw0 : Multiset ℕ) = 1 • (supportNumbers0229 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0229] using hm

private def finish0372Input0 : List ℕ := [0, 4, 10, 14, 65, 69, 75, 79]
private def finish0372Raw0 : List ℕ := [0, 10, 65, 75]
private theorem finish0372Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0372Input0) = fromList finish0372Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0372 : finishSupport ⟨false, bits4 4⟩ support1148 = 1 • support1149 := by
  have hs : support1148 = fromList finish0372Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0372Chunk0]
  have hn : (finish0372Raw0 : Multiset ℕ) = 1 • (supportNumbers1149 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1149] using hm

private def finish0373Input0 : List ℕ := [0, 4, 10, 14, 65, 69, 75, 79, 515, 519, 521, 525, 578, 582, 584, 588]
private def finish0373Raw0 : List ℕ := [0, 4, 10, 14, 65, 69, 75, 79, 3, 7, 9, 13, 66, 70, 72, 76]
private theorem finish0373Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0373Input0) = fromList finish0373Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0373 : finishSupport ⟨true, bits4 4⟩ support1150 = 1 • support1151 := by
  have hs : support1150 = fromList finish0373Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0373Chunk0]
  have hn : (finish0373Raw0 : Multiset ℕ) = 1 • (supportNumbers1151 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1151] using hm

private def finish0374Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367]
private def finish0374Raw0 : List ℕ := [0, 2, 8, 10, 65, 67, 73, 75, 36, 38, 44, 46, 101, 103, 109, 111]
private theorem finish0374Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0374Input0) = fromList finish0374Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0374 : finishSupport ⟨false, bits4 4⟩ support1153 = 1 • support1154 := by
  have hs : support1153 = fromList finish0374Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0374Chunk0]
  have hn : (finish0374Raw0 : Multiset ℕ) = 1 • (supportNumbers1154 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1154] using hm

private def finish0375Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367, 513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 801, 803, 805, 807, 809, 811, 813, 815, 864, 866, 868, 870, 872, 874, 876, 878]
private def finish0375Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 32, 34, 36, 38, 40, 42, 44, 46, 97, 99, 101, 103, 105, 107, 109, 111, 1, 3, 5, 7, 9, 11, 13, 15, 64, 66, 68, 70, 72, 74, 76, 78, 33, 35, 37, 39, 41, 43, 45, 47, 96, 98, 100, 102, 104, 106, 108, 110]
private theorem finish0375Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0375Input0) = fromList finish0375Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0375 : finishSupport ⟨true, bits4 4⟩ support1155 = 1 • support0938 := by
  have hs : support1155 = fromList finish0375Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0375Chunk0]
  have hn : (finish0375Raw0 : Multiset ℕ) = 1 • (supportNumbers0938 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0938] using hm

private def finish0376Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private def finish0376Raw0 : List ℕ := [0, 2, 8, 10, 65, 67, 73, 75]
private theorem finish0376Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0376Input0) = fromList finish0376Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0376 : finishSupport ⟨false, bits4 4⟩ support0004 = 1 • support1156 := by
  have hs : support0004 = fromList finish0376Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0376Chunk0]
  have hn : (finish0376Raw0 : Multiset ℕ) = 1 • (supportNumbers1156 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1156] using hm

private def finish0377Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590]
private def finish0377Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 1, 3, 5, 7, 9, 11, 13, 15, 64, 66, 68, 70, 72, 74, 76, 78]
private theorem finish0377Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0377Input0) = fromList finish0377Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0377 : finishSupport ⟨true, bits4 4⟩ support1157 = 1 • support0222 := by
  have hs : support1157 = fromList finish0377Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0377Chunk0]
  have hn : (finish0377Raw0 : Multiset ℕ) = 1 • (supportNumbers0222 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0222] using hm

private def finish0378Input0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 128, 132, 136, 140, 193, 197, 201, 205]
private def finish0378Raw0 : List ℕ := [0, 8, 65, 73, 128, 136, 193, 201]
private theorem finish0378Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0378Input0) = fromList finish0378Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0378 : finishSupport ⟨false, bits4 4⟩ support1159 = 1 • support1160 := by
  have hs : support1159 = fromList finish0378Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0378Chunk0]
  have hn : (finish0378Raw0 : Multiset ℕ) = 1 • (supportNumbers1160 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1160] using hm

private def finish0379Input0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 128, 132, 136, 140, 193, 197, 201, 205, 515, 519, 523, 527, 578, 582, 586, 590, 643, 647, 651, 655, 706, 710, 714, 718]
private def finish0379Raw0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 128, 132, 136, 140, 193, 197, 201, 205, 3, 7, 11, 15, 66, 70, 74, 78, 131, 135, 139, 143, 194, 198, 202, 206]
private theorem finish0379Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0379Input0) = fromList finish0379Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0379 : finishSupport ⟨true, bits4 4⟩ support1161 = 1 • support0522 := by
  have hs : support1161 = fromList finish0379Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0379Chunk0]
  have hn : (finish0379Raw0 : Multiset ℕ) = 1 • (supportNumbers0522 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0522] using hm

private def finish0380Input0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76]
private def finish0380Raw0 : List ℕ := [0, 9, 65, 72]
private theorem finish0380Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0380Input0) = fromList finish0380Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0380 : finishSupport ⟨false, bits4 4⟩ support1163 = 1 • support1164 := by
  have hs : support1163 = fromList finish0380Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0380Chunk0]
  have hn : (finish0380Raw0 : Multiset ℕ) = 1 • (supportNumbers1164 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1164] using hm

private def finish0381Input0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 515, 519, 522, 526, 578, 582, 587, 591]
private def finish0381Raw0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 3, 7, 10, 14, 66, 70, 75, 79]
private theorem finish0381Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0381Input0) = fromList finish0381Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0381 : finishSupport ⟨true, bits4 4⟩ support1165 = 1 • support1151 := by
  have hs : support1165 = fromList finish0381Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0381Chunk0]
  have hn : (finish0381Raw0 : Multiset ℕ) = 1 • (supportNumbers1151 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1151] using hm

private def finish0382Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78]
private def finish0382Raw0 : List ℕ := [0, 2, 9, 11, 65, 67, 72, 74]
private theorem finish0382Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0382Input0) = fromList finish0382Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0382 : finishSupport ⟨false, bits4 4⟩ support0217 = 1 • support1166 := by
  have hs : support0217 = fromList finish0382Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0382Chunk0]
  have hn : (finish0382Raw0 : Multiset ℕ) = 1 • (supportNumbers1166 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1166] using hm

private def finish0383Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591]
private def finish0383Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 1, 3, 5, 7, 8, 10, 12, 14, 64, 66, 68, 70, 73, 75, 77, 79]
private theorem finish0383Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0383Input0) = fromList finish0383Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0383 : finishSupport ⟨true, bits4 4⟩ support0310 = 1 • support0222 := by
  have hs : support0310 = fromList finish0383Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0383Chunk0]
  have hn : (finish0383Raw0 : Multiset ℕ) = 1 • (supportNumbers0222 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0222] using hm

private def finish0384Input0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 130, 134, 139, 143, 195, 199, 202, 206]
private def finish0384Raw0 : List ℕ := [0, 9, 65, 72, 130, 139, 195, 202]
private theorem finish0384Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0384Input0) = fromList finish0384Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0384 : finishSupport ⟨false, bits4 4⟩ support1167 = 1 • support1168 := by
  have hs : support1167 = fromList finish0384Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0384Chunk0]
  have hn : (finish0384Raw0 : Multiset ℕ) = 1 • (supportNumbers1168 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1168] using hm

private def finish0385Input0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 130, 134, 139, 143, 195, 199, 202, 206, 515, 519, 522, 526, 578, 582, 587, 591, 641, 645, 648, 652, 704, 708, 713, 717]
private def finish0385Raw0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 130, 134, 139, 143, 195, 199, 202, 206, 3, 7, 10, 14, 66, 70, 75, 79, 129, 133, 136, 140, 192, 196, 201, 205]
private theorem finish0385Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0385Input0) = fromList finish0385Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0385 : finishSupport ⟨true, bits4 4⟩ support1169 = 1 • support0735 := by
  have hs : support1169 = fromList finish0385Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0385Chunk0]
  have hn : (finish0385Raw0 : Multiset ℕ) = 1 • (supportNumbers0735 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0735] using hm

private def finish0386Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366, 416, 418, 420, 422, 425, 427, 429, 431, 481, 483, 485, 487, 488, 490, 492, 494]
private def finish0386Raw0 : List ℕ := [0, 2, 9, 11, 65, 67, 72, 74, 128, 130, 137, 139, 193, 195, 200, 202, 36, 38, 45, 47, 101, 103, 108, 110, 164, 166, 173, 175, 229, 231, 236, 238]
private theorem finish0386Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0386Input0) = fromList finish0386Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0386 : finishSupport ⟨false, bits4 4⟩ support1171 = 1 • support1172 := by
  have hs : support1171 = fromList finish0386Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0386Chunk0]
  have hn : (finish0386Raw0 : Multiset ℕ) = 1 • (supportNumbers1172 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1172] using hm

private def finish0387Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366, 416, 418, 420, 422, 425, 427, 429, 431, 481, 483, 485, 487, 488, 490, 492, 494]
private def finish0387Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 32, 34, 36, 38, 41, 43, 45, 47, 97, 99, 101, 103, 104, 106, 108, 110, 160, 162, 164, 166, 169, 171, 173, 175, 225, 227, 229, 231, 232, 234, 236, 238]
private theorem finish0387Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0387Input0) = fromList finish0387Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0387Input1 : List ℕ := [513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 641, 643, 645, 647, 648, 650, 652, 654, 704, 706, 708, 710, 713, 715, 717, 719, 801, 803, 805, 807, 808, 810, 812, 814, 864, 866, 868, 870, 873, 875, 877, 879, 929, 931, 933, 935, 936, 938, 940, 942, 992, 994, 996, 998, 1001, 1003, 1005, 1007]
private def finish0387Raw1 : List ℕ := [1, 3, 5, 7, 8, 10, 12, 14, 64, 66, 68, 70, 73, 75, 77, 79, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 33, 35, 37, 39, 40, 42, 44, 46, 96, 98, 100, 102, 105, 107, 109, 111, 161, 163, 165, 167, 168, 170, 172, 174, 224, 226, 228, 230, 233, 235, 237, 239]
private theorem finish0387Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0387Input1) = fromList finish0387Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0387 : finishSupport ⟨true, bits4 4⟩ support1173 = 1 • support0527 := by
  have hs : support1173 = fromList finish0387Input0 + fromList finish0387Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0387Chunk0, finish0387Chunk1]
  have hn : (finish0387Raw0 : Multiset ℕ) + (finish0387Raw1 : Multiset ℕ) = 1 • (supportNumbers0527 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0527] using hm

private def finish0388Input0 : List ℕ := [0, 4, 11, 15, 65, 69, 74, 78, 131, 135, 136, 140, 194, 198, 201, 205]
private def finish0388Raw0 : List ℕ := [0, 11, 65, 74, 131, 136, 194, 201]
private theorem finish0388Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0388Input0) = fromList finish0388Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0388 : finishSupport ⟨false, bits4 4⟩ support1174 = 1 • support1175 := by
  have hs : support1174 = fromList finish0388Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0388Chunk0]
  have hn : (finish0388Raw0 : Multiset ℕ) = 1 • (supportNumbers1175 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1175] using hm

private def finish0389Input0 : List ℕ := [0, 4, 11, 15, 65, 69, 74, 78, 131, 135, 136, 140, 194, 198, 201, 205, 515, 519, 520, 524, 578, 582, 585, 589, 640, 644, 651, 655, 705, 709, 714, 718]
private def finish0389Raw0 : List ℕ := [0, 4, 11, 15, 65, 69, 74, 78, 131, 135, 136, 140, 194, 198, 201, 205, 3, 7, 8, 12, 66, 70, 73, 77, 128, 132, 139, 143, 193, 197, 202, 206]
private theorem finish0389Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0389Input0) = fromList finish0389Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0389 : finishSupport ⟨true, bits4 4⟩ support1176 = 1 • support0522 := by
  have hs : support1176 = fromList finish0389Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0389Chunk0]
  have hn : (finish0389Raw0 : Multiset ℕ) = 1 • (supportNumbers0522 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0522] using hm

private def finish0390Input0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77]
private def finish0390Raw0 : List ℕ := [0, 1, 8, 9, 64, 65, 72, 73]
private theorem finish0390Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0390Input0) = fromList finish0390Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0390 : finishSupport ⟨false, bits4 4⟩ support1178 = 1 • support1179 := by
  have hs : support1178 = fromList finish0390Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0390Chunk0]
  have hn : (finish0390Raw0 : Multiset ℕ) = 1 • (supportNumbers1179 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1179] using hm

private def finish0391Input0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77, 514, 515, 518, 519, 522, 523, 526, 527, 578, 579, 582, 583, 586, 587, 590, 591]
private def finish0391Raw0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77, 2, 3, 6, 7, 10, 11, 14, 15, 66, 67, 70, 71, 74, 75, 78, 79]
private theorem finish0391Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0391Input0) = fromList finish0391Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0391 : finishSupport ⟨true, bits4 4⟩ support1180 = 1 • support0222 := by
  have hs : support1180 = fromList finish0391Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0391Chunk0]
  have hn : (finish0391Raw0 : Multiset ℕ) = 1 • (supportNumbers0222 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0222] using hm

private def finish0392Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]
private def finish0392Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 64, 65, 66, 67, 72, 73, 74, 75, 164, 165, 166, 167, 172, 173, 174, 175, 228, 229, 230, 231, 236, 237, 238, 239]
private theorem finish0392Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0392Input0) = fromList finish0392Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0392 : finishSupport ⟨false, bits4 4⟩ support1182 = 1 • support1183 := by
  have hs : support1182 = fromList finish0392Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0392Chunk0]
  have hn : (finish0392Raw0 : Multiset ℕ) = 1 • (supportNumbers1183 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1183] using hm

private def finish0393Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]
private def finish0393Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]
private theorem finish0393Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0393Input0) = fromList finish0393Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0393Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]
private def finish0393Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]
private theorem finish0393Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0393Input1) = fromList finish0393Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0393 : finishSupport ⟨true, bits4 4⟩ support1184 = 2 • support0927 := by
  have hs : support1184 = fromList finish0393Input0 + fromList finish0393Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0393Chunk0, finish0393Chunk1]
  have hn : (finish0393Raw0 : Multiset ℕ) + (finish0393Raw1 : Multiset ℕ) = 2 • (supportNumbers0927 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0927] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
