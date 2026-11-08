import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1615Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]
private def transition1615Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 8, 648, 9, 649, 10, 650, 11, 651, 12, 652, 13, 653, 14, 654, 15, 655, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 72, 712, 73, 713, 74, 714, 75, 715, 76, 716, 77, 717, 78, 718, 79, 719, 256, 896, 257, 897, 258, 898, 259, 899, 260, 900, 261, 901, 262, 902, 263, 903, 264, 904, 265, 905, 266, 906, 267, 907, 268, 908, 269, 909, 270, 910, 271, 911, 320, 960, 321, 961, 322, 962, 323, 963, 324, 964, 325, 965, 326, 966, 327, 967, 328, 968, 329, 969, 330, 970, 331, 971, 332, 972, 333, 973, 334, 974, 335, 975]
private theorem transition1615Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1615Input0) = fromList transition1615Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1615 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0223 = 1 • support0313 := by
  have hs : support0223 = fromList transition1615Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1615Chunk0]
  have hn : (transition1615Raw0 : Multiset ℕ) = 1 • (supportNumbers0313 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0313] using hm

private def transition1616Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]
private def transition1616Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private theorem transition1616Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1616Input0) = fromList transition1616Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1616 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0223 = 1 • support0312 := by
  have hs : support0223 = fromList transition1616Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1616Chunk0]
  have hn : (transition1616Raw0 : Multiset ℕ) = 1 • (supportNumbers0312 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0312] using hm

private def transition1617Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private def transition1617Raw0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77, 2, 3, 6, 7, 10, 11, 14, 15, 66, 67, 70, 71, 74, 75, 78, 79]
private theorem transition1617Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1617Input0) = fromList transition1617Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1617 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0312 = 1 • support0222 := by
  have hs : support0312 = fromList transition1617Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1617Chunk0]
  have hn : (transition1617Raw0 : Multiset ℕ) = 1 • (supportNumbers0222 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0222] using hm

private def transition1618Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private def transition1618Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 8, 9, 586, 587, 12, 13, 590, 591, 64, 65, 514, 515, 68, 69, 518, 519, 72, 73, 522, 523, 76, 77, 526, 527, 576, 577, 2, 3, 580, 581, 6, 7, 584, 585, 10, 11, 588, 589, 14, 15, 512, 513, 66, 67, 516, 517, 70, 71, 520, 521, 74, 75, 524, 525, 78, 79]
private theorem transition1618Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1618Input0) = fromList transition1618Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1618 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0312 = 1 • support0223 := by
  have hs : support0312 = fromList transition1618Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1618Chunk0]
  have hn : (transition1618Raw0 : Multiset ℕ) = 1 • (supportNumbers0223 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0223] using hm

private def transition1619Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]
private def transition1619Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 8, 552, 9, 553, 10, 554, 11, 555, 12, 556, 13, 557, 14, 558, 15, 559, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 72, 616, 73, 617, 74, 618, 75, 619, 76, 620, 77, 621, 78, 622, 79, 623, 256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879]
private theorem transition1619Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1619Input0) = fromList transition1619Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1619 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0223 = 1 • support1406 := by
  have hs : support0223 = fromList transition1619Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1619Chunk0]
  have hn : (transition1619Raw0 : Multiset ℕ) = 1 • (supportNumbers1406 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1406] using hm

private def transition1620Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private def transition1620Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
private theorem transition1620Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1620Input0) = fromList transition1620Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1620Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]
private def transition1620Raw1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]
private theorem transition1620Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1620Input1) = fromList transition1620Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1620 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1406 = 2 • support1223 := by
  have hs : support1406 = fromList transition1620Input0 + fromList transition1620Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1620Chunk0, transition1620Chunk1]
  have hn : (transition1620Raw0 : Multiset ℕ) + (transition1620Raw1 : Multiset ℕ) = 2 • (supportNumbers1223 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1223] using hm

private def transition1621Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private def transition1621Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 8, 584, 9, 585, 10, 586, 11, 587, 12, 588, 13, 589, 14, 590, 15, 591, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 72, 520, 73, 521, 74, 522, 75, 523, 76, 524, 77, 525, 78, 526, 79, 527, 0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 8, 584, 9, 585, 10, 586, 11, 587, 12, 588, 13, 589, 14, 590, 15, 591, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 72, 520, 73, 521, 74, 522, 75, 523, 76, 524, 77, 525, 78, 526, 79, 527]
private theorem transition1621Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1621Input0) = fromList transition1621Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1621Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]
private def transition1621Raw1 : List ℕ := [288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 296, 872, 297, 873, 298, 874, 299, 875, 300, 876, 301, 877, 302, 878, 303, 879, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 360, 808, 361, 809, 362, 810, 363, 811, 364, 812, 365, 813, 366, 814, 367, 815, 288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 296, 872, 297, 873, 298, 874, 299, 875, 300, 876, 301, 877, 302, 878, 303, 879, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 360, 808, 361, 809, 362, 810, 363, 811, 364, 812, 365, 813, 366, 814, 367, 815]
private theorem transition1621Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1621Input1) = fromList transition1621Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1621 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1406 = 2 • support1225 := by
  have hs : support1406 = fromList transition1621Input0 + fromList transition1621Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1621Chunk0, transition1621Chunk1]
  have hn : (transition1621Raw0 : Multiset ℕ) + (transition1621Raw1 : Multiset ℕ) = 2 • (supportNumbers1225 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1225] using hm

private def transition1622Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private def transition1622Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private theorem transition1622Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1622Input0) = fromList transition1622Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1622 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0144 = 1 • support0144 := by
  have hs : support0144 = fromList transition1622Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1622Chunk0]
  have hn : (transition1622Raw0 : Multiset ℕ) = 1 • (supportNumbers0144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0144] using hm

private def transition1623Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private def transition1623Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 129, 513, 131, 515, 133, 517, 135, 519, 192, 576, 194, 578, 196, 580, 198, 582]
private theorem transition1623Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1623Input0) = fromList transition1623Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1623 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0144 = 1 • support0314 := by
  have hs : support0144 = fromList transition1623Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1623Chunk0]
  have hn : (transition1623Raw0 : Multiset ℕ) = 1 • (supportNumbers0314 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0314] using hm

private def transition1624Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private def transition1624Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private theorem transition1624Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1624Input0) = fromList transition1624Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1624 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0144 = 1 • support0144 := by
  have hs : support0144 = fromList transition1624Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1624Chunk0]
  have hn : (transition1624Raw0 : Multiset ℕ) = 1 • (supportNumbers0144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0144] using hm

private def transition1625Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private def transition1625Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 129, 673, 131, 675, 133, 677, 135, 679, 192, 736, 194, 738, 196, 740, 198, 742]
private theorem transition1625Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1625Input0) = fromList transition1625Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1625 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0144 = 1 • support1407 := by
  have hs : support0144 = fromList transition1625Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1625Chunk0]
  have hn : (transition1625Raw0 : Multiset ℕ) = 1 • (supportNumbers1407 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1407] using hm

private def transition1626Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 544, 546, 548, 550, 609, 611, 613, 615, 673, 675, 677, 679, 736, 738, 740, 742]
private def transition1626Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 288, 290, 292, 294, 353, 355, 357, 359, 417, 419, 421, 423, 480, 482, 484, 486]
private theorem transition1626Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1626Input0) = fromList transition1626Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1626 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1407 = 1 • support1408 := by
  have hs : support1407 = fromList transition1626Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1626Chunk0]
  have hn : (transition1626Raw0 : Multiset ℕ) = 1 • (supportNumbers1408 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1408] using hm

private def transition1627Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 544, 546, 548, 550, 609, 611, 613, 615, 673, 675, 677, 679, 736, 738, 740, 742]
private def transition1627Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 129, 705, 131, 707, 133, 709, 135, 711, 192, 640, 194, 642, 196, 644, 198, 646, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 417, 993, 419, 995, 421, 997, 423, 999, 480, 928, 482, 930, 484, 932, 486, 934]
private theorem transition1627Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1627Input0) = fromList transition1627Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1627 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1407 = 1 • support1410 := by
  have hs : support1407 = fromList transition1627Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1627Chunk0]
  have hn : (transition1627Raw0 : Multiset ℕ) = 1 • (supportNumbers1410 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1410] using hm

private def transition1628Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 264, 266, 268, 270, 329, 331, 333, 335, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition1628Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 8, 10, 12, 14, 73, 75, 77, 79, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition1628Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1628Input0) = fromList transition1628Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1628 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0224 = 1 • support0315 := by
  have hs : support0224 = fromList transition1628Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1628Chunk0]
  have hn : (transition1628Raw0 : Multiset ℕ) = 1 • (supportNumbers0315 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0315] using hm

private def transition1629Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 264, 266, 268, 270, 329, 331, 333, 335, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition1629Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 8, 10, 12, 14, 73, 75, 77, 79, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition1629Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1629Input0) = fromList transition1629Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1629 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0224 = 1 • support0315 := by
  have hs : support0224 = fromList transition1629Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1629Chunk0]
  have hn : (transition1629Raw0 : Multiset ℕ) = 1 • (supportNumbers0315 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0315] using hm

private def transition1630Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 264, 266, 268, 270, 329, 331, 333, 335, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition1630Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 8, 10, 12, 14, 73, 75, 77, 79, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition1630Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1630Input0) = fromList transition1630Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1630 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0224 = 1 • support0315 := by
  have hs : support0224 = fromList transition1630Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1630Chunk0]
  have hn : (transition1630Raw0 : Multiset ℕ) = 1 • (supportNumbers0315 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0315] using hm

private def transition1631Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private def transition1631Raw0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 129, 133, 137, 141, 192, 196, 200, 204]
private theorem transition1631Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1631Input0) = fromList transition1631Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1631 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0315 = 1 • support1411 := by
  have hs : support0315 = fromList transition1631Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1631Chunk0]
  have hn : (transition1631Raw0 : Multiset ℕ) = 1 • (supportNumbers1411 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1411] using hm

private def transition1632Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private def transition1632Raw0 : List ℕ := [0, 578, 4, 582, 8, 586, 12, 590, 65, 515, 69, 519, 73, 523, 77, 527, 129, 707, 133, 711, 137, 715, 141, 719, 192, 642, 196, 646, 200, 650, 204, 654]
private theorem transition1632Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1632Input0) = fromList transition1632Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1632 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0315 = 1 • support1413 := by
  have hs : support0315 = fromList transition1632Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1632Chunk0]
  have hn : (transition1632Raw0 : Multiset ℕ) = 1 • (supportNumbers1413 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1413] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
