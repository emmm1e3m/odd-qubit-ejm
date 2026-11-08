import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1013Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 264, 266, 268, 270, 329, 331, 333, 335, 544, 546, 548, 550, 609, 611, 613, 615, 808, 810, 812, 814, 873, 875, 877, 879]
private def transition1013Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 8, 584, 10, 586, 12, 588, 14, 590, 73, 521, 75, 523, 77, 525, 79, 527, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 296, 872, 298, 874, 300, 876, 302, 878, 361, 809, 363, 811, 365, 813, 367, 815]
private theorem transition1013Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1013Input0) = fromList transition1013Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1013 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1152 = 1 • support1155 := by
  have hs : support1152 = fromList transition1013Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1013Chunk0]
  have hn : (transition1013Raw0 : Multiset ℕ) = 1 • (supportNumbers1155 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1155] using hm

private def transition1014Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition1014Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition1014Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1014Input0) = fromList transition1014Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1014 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0135 = 1 • support0077 := by
  have hs : support0135 = fromList transition1014Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1014Chunk0]
  have hn : (transition1014Raw0 : Multiset ℕ) = 1 • (supportNumbers0077 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0077] using hm

private def transition1015Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition1015Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 136, 520, 138, 522, 140, 524, 142, 526, 201, 585, 203, 587, 205, 589, 207, 591, 264, 904, 266, 906, 268, 908, 270, 910, 329, 969, 331, 971, 333, 973, 335, 975, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839]
private theorem transition1015Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1015Input0) = fromList transition1015Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1015 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0135 = 1 • support0078 := by
  have hs : support0135 = fromList transition1015Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1015Chunk0]
  have hn : (transition1015Raw0 : Multiset ℕ) = 1 • (supportNumbers0078 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0078] using hm

private def transition1016Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition1016Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition1016Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1016Input0) = fromList transition1016Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1016 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0135 = 1 • support0077 := by
  have hs : support0135 = fromList transition1016Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1016Chunk0]
  have hn : (transition1016Raw0 : Multiset ℕ) = 1 • (supportNumbers0077 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0077] using hm

private def transition1017Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition1017Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 136, 680, 138, 682, 140, 684, 142, 686, 201, 745, 203, 747, 205, 749, 207, 751, 264, 808, 266, 810, 268, 812, 270, 814, 329, 873, 331, 875, 333, 877, 335, 879, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999]
private theorem transition1017Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1017Input0) = fromList transition1017Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1017 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0135 = 1 • support0736 := by
  have hs : support0135 = fromList transition1017Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1017Chunk0]
  have hn : (transition1017Raw0 : Multiset ℕ) = 1 • (supportNumbers0736 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0736] using hm

private def transition1018Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 512, 514, 516, 518, 520, 522, 524, 526, 577, 579, 581, 583, 585, 587, 589, 591]
private def transition1018Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335]
private theorem transition1018Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1018Input0) = fromList transition1018Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1018 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0136 = 1 • support0213 := by
  have hs : support0136 = fromList transition1018Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1018Chunk0]
  have hn : (transition1018Raw0 : Multiset ℕ) = 1 • (supportNumbers0213 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0213] using hm

private def transition1019Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 512, 514, 516, 518, 520, 522, 524, 526, 577, 579, 581, 583, 585, 587, 589, 591]
private def transition1019Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 256, 896, 258, 898, 260, 900, 262, 902, 264, 904, 266, 906, 268, 908, 270, 910, 321, 961, 323, 963, 325, 965, 327, 967, 329, 969, 331, 971, 333, 973, 335, 975]
private theorem transition1019Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1019Input0) = fromList transition1019Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1019 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0136 = 1 • support0214 := by
  have hs : support0136 = fromList transition1019Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1019Chunk0]
  have hn : (transition1019Raw0 : Multiset ℕ) = 1 • (supportNumbers0214 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0214] using hm

private def transition1020Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 512, 514, 516, 518, 520, 522, 524, 526, 577, 579, 581, 583, 585, 587, 589, 591]
private def transition1020Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335]
private theorem transition1020Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1020Input0) = fromList transition1020Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1020 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0136 = 1 • support0213 := by
  have hs : support0136 = fromList transition1020Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1020Chunk0]
  have hn : (transition1020Raw0 : Multiset ℕ) = 1 • (supportNumbers0213 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0213] using hm

private def transition1021Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335]
private def transition1021Raw0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 2, 6, 10, 14, 67, 71, 75, 79]
private theorem transition1021Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1021Input0) = fromList transition1021Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1021 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0213 = 1 • support0004 := by
  have hs : support0213 = fromList transition1021Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1021Chunk0]
  have hn : (transition1021Raw0 : Multiset ℕ) = 1 • (supportNumbers0004 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0004] using hm

private def transition1022Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335]
private def transition1022Raw0 : List ℕ := [0, 578, 4, 582, 8, 586, 12, 590, 65, 515, 69, 519, 73, 523, 77, 527, 576, 2, 580, 6, 584, 10, 588, 14, 513, 67, 517, 71, 521, 75, 525, 79]
private theorem transition1022Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1022Input0) = fromList transition1022Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1022 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0213 = 1 • support1157 := by
  have hs : support0213 = fromList transition1022Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1022Chunk0]
  have hn : (transition1022Raw0 : Multiset ℕ) = 1 • (supportNumbers1157 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1157] using hm

private def transition1023Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 512, 514, 516, 518, 520, 522, 524, 526, 577, 579, 581, 583, 585, 587, 589, 591]
private def transition1023Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623, 256, 800, 258, 802, 260, 804, 262, 806, 264, 808, 266, 810, 268, 812, 270, 814, 321, 865, 323, 867, 325, 869, 327, 871, 329, 873, 331, 875, 333, 877, 335, 879]
private theorem transition1023Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1023Input0) = fromList transition1023Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1023 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0136 = 1 • support1158 := by
  have hs : support0136 = fromList transition1023Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1023Chunk0]
  have hn : (transition1023Raw0 : Multiset ℕ) = 1 • (supportNumbers1158 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1158] using hm

private def transition1024Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623, 800, 802, 804, 806, 808, 810, 812, 814, 865, 867, 869, 871, 873, 875, 877, 879]
private def transition1024Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367, 288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367]
private theorem transition1024Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1024Input0) = fromList transition1024Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1024 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1158 = 2 • support1153 := by
  have hs : support1158 = fromList transition1024Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1024Chunk0]
  have hn : (transition1024Raw0 : Multiset ℕ) = 2 • (supportNumbers1153 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1153] using hm

private def transition1025Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623, 800, 802, 804, 806, 808, 810, 812, 814, 865, 867, 869, 871, 873, 875, 877, 879]
private def transition1025Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 288, 864, 290, 866, 292, 868, 294, 870, 296, 872, 298, 874, 300, 876, 302, 878, 353, 801, 355, 803, 357, 805, 359, 807, 361, 809, 363, 811, 365, 813, 367, 815, 288, 864, 290, 866, 292, 868, 294, 870, 296, 872, 298, 874, 300, 876, 302, 878, 353, 801, 355, 803, 357, 805, 359, 807, 361, 809, 363, 811, 365, 813, 367, 815]
private theorem transition1025Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1025Input0) = fromList transition1025Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1025 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1158 = 2 • support1155 := by
  have hs : support1158 = fromList transition1025Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1025Chunk0]
  have hn : (transition1025Raw0 : Multiset ℕ) = 2 • (supportNumbers1155 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1155] using hm

private def transition1026Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition1026Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 8, 10, 12, 14, 73, 75, 77, 79, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition1026Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1026Input0) = fromList transition1026Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1026 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0137 = 1 • support0215 := by
  have hs : support0137 = fromList transition1026Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1026Chunk0]
  have hn : (transition1026Raw0 : Multiset ℕ) = 1 • (supportNumbers0215 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0215] using hm

private def transition1027Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition1027Raw0 : List ℕ := [0, 2, 4, 6, 648, 650, 652, 654, 65, 67, 69, 71, 713, 715, 717, 719, 128, 130, 132, 134, 520, 522, 524, 526, 193, 195, 197, 199, 585, 587, 589, 591, 640, 642, 644, 646, 8, 10, 12, 14, 705, 707, 709, 711, 73, 75, 77, 79, 512, 514, 516, 518, 136, 138, 140, 142, 577, 579, 581, 583, 201, 203, 205, 207]
private theorem transition1027Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1027Input0) = fromList transition1027Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1027 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0137 = 1 • support0216 := by
  have hs : support0137 = fromList transition1027Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1027Chunk0]
  have hn : (transition1027Raw0 : Multiset ℕ) = 1 • (supportNumbers0216 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0216] using hm

private def transition1028Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition1028Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 8, 10, 12, 14, 73, 75, 77, 79, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition1028Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1028Input0) = fromList transition1028Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1028 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0137 = 1 • support0215 := by
  have hs : support0137 = fromList transition1028Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1028Chunk0]
  have hn : (transition1028Raw0 : Multiset ℕ) = 1 • (supportNumbers0215 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0215] using hm

private def transition1029Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private def transition1029Raw0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 128, 132, 136, 140, 193, 197, 201, 205]
private theorem transition1029Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1029Input0) = fromList transition1029Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1029 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0215 = 1 • support1159 := by
  have hs : support0215 = fromList transition1029Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1029Chunk0]
  have hn : (transition1029Raw0 : Multiset ℕ) = 1 • (supportNumbers1159 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1159] using hm

private def transition1030Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private def transition1030Raw0 : List ℕ := [0, 578, 4, 582, 8, 586, 12, 590, 65, 515, 69, 519, 73, 523, 77, 527, 128, 706, 132, 710, 136, 714, 140, 718, 193, 643, 197, 647, 201, 651, 205, 655]
private theorem transition1030Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1030Input0) = fromList transition1030Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1030 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0215 = 1 • support1161 := by
  have hs : support0215 = fromList transition1030Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1030Chunk0]
  have hn : (transition1030Raw0 : Multiset ℕ) = 1 • (supportNumbers1161 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1161] using hm

private def transition1031Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition1031Raw0 : List ℕ := [0, 2, 4, 6, 552, 554, 556, 558, 65, 67, 69, 71, 617, 619, 621, 623, 128, 130, 132, 134, 680, 682, 684, 686, 193, 195, 197, 199, 745, 747, 749, 751, 544, 546, 548, 550, 8, 10, 12, 14, 609, 611, 613, 615, 73, 75, 77, 79, 672, 674, 676, 678, 136, 138, 140, 142, 737, 739, 741, 743, 201, 203, 205, 207]
private theorem transition1031Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1031Input0) = fromList transition1031Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1031 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0137 = 1 • support1162 := by
  have hs : support0137 = fromList transition1031Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1031Chunk0]
  have hn : (transition1031Raw0 : Multiset ℕ) = 1 • (supportNumbers1162 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1162] using hm

private def transition1032Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623, 672, 674, 676, 678, 680, 682, 684, 686, 737, 739, 741, 743, 745, 747, 749, 751]
private def transition1032Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367, 416, 418, 420, 422, 424, 426, 428, 430, 481, 483, 485, 487, 489, 491, 493, 495]
private theorem transition1032Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1032Input0) = fromList transition1032Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1032 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1162 = 1 • support0737 := by
  have hs : support1162 = fromList transition1032Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1032Chunk0]
  have hn : (transition1032Raw0 : Multiset ℕ) = 1 • (supportNumbers0737 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0737] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
