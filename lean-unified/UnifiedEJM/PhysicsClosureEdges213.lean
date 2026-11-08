import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0614Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 312, 313, 314, 315, 316, 317, 318, 319, 376, 377, 378, 379, 380, 381, 382, 383, 440, 441, 442, 443, 444, 445, 446, 447, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0614Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 128, 129, 130, 131, 192, 193, 194, 195, 60, 61, 62, 63, 124, 125, 126, 127, 188, 189, 190, 191, 252, 253, 254, 255]
private theorem finish0614Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0614Input0) = fromList finish0614Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0614 : finishSupport ⟨false, bits4 4⟩ support1603 = 1 • support1526 := by
  have hs : support1603 = fromList finish0614Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0614Chunk0]
  have hn : (finish0614Raw0 : Multiset ℕ) = 1 • (supportNumbers1526 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1526] using hm

private def finish0615Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 312, 313, 314, 315, 316, 317, 318, 319, 376, 377, 378, 379, 380, 381, 382, 383, 440, 441, 442, 443, 444, 445, 446, 447, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0615Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 56, 57, 58, 59, 60, 61, 62, 63, 120, 121, 122, 123, 124, 125, 126, 127, 184, 185, 186, 187, 188, 189, 190, 191, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0615Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0615Input0) = fromList finish0615Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0615Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 824, 825, 826, 827, 828, 829, 830, 831, 888, 889, 890, 891, 892, 893, 894, 895, 952, 953, 954, 955, 956, 957, 958, 959, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def finish0615Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 56, 57, 58, 59, 60, 61, 62, 63, 120, 121, 122, 123, 124, 125, 126, 127, 184, 185, 186, 187, 188, 189, 190, 191, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0615Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0615Input1) = fromList finish0615Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0615 : finishSupport ⟨true, bits4 4⟩ support1604 = 2 • support1605 := by
  have hs : support1604 = fromList finish0615Input0 + fromList finish0615Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0615Chunk0, finish0615Chunk1]
  have hn : (finish0615Raw0 : Multiset ℕ) + (finish0615Raw1 : Multiset ℕ) = 2 • (supportNumbers1605 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1605] using hm

private def finish0616Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 296, 297, 298, 299, 300, 301, 302, 303, 360, 361, 362, 363, 364, 365, 366, 367, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487]
private def finish0616Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 136, 137, 138, 139, 200, 201, 202, 203, 44, 45, 46, 47, 108, 109, 110, 111, 164, 165, 166, 167, 228, 229, 230, 231]
private theorem finish0616Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0616Input0) = fromList finish0616Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0616 : finishSupport ⟨false, bits4 4⟩ support1607 = 1 • support1608 := by
  have hs : support1607 = fromList finish0616Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0616Chunk0]
  have hn : (finish0616Raw0 : Multiset ℕ) = 1 • (supportNumbers1608 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1608] using hm

private def finish0617Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 296, 297, 298, 299, 300, 301, 302, 303, 360, 361, 362, 363, 364, 365, 366, 367, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487]
private def finish0617Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 40, 41, 42, 43, 44, 45, 46, 47, 104, 105, 106, 107, 108, 109, 110, 111, 160, 161, 162, 163, 164, 165, 166, 167, 224, 225, 226, 227, 228, 229, 230, 231]
private theorem finish0617Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0617Input0) = fromList finish0617Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0617Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 648, 649, 650, 651, 652, 653, 654, 655, 712, 713, 714, 715, 716, 717, 718, 719, 808, 809, 810, 811, 812, 813, 814, 815, 872, 873, 874, 875, 876, 877, 878, 879, 928, 929, 930, 931, 932, 933, 934, 935, 992, 993, 994, 995, 996, 997, 998, 999]
private def finish0617Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 40, 41, 42, 43, 44, 45, 46, 47, 104, 105, 106, 107, 108, 109, 110, 111, 160, 161, 162, 163, 164, 165, 166, 167, 224, 225, 226, 227, 228, 229, 230, 231]
private theorem finish0617Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0617Input1) = fromList finish0617Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0617 : finishSupport ⟨true, bits4 4⟩ support1609 = 2 • support0612 := by
  have hs : support1609 = fromList finish0617Input0 + fromList finish0617Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0617Chunk0, finish0617Chunk1]
  have hn : (finish0617Raw0 : Multiset ℕ) + (finish0617Raw1 : Multiset ℕ) = 2 • (supportNumbers0612 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0612] using hm

private def finish0618Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0618Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 64, 65, 66, 67, 72, 73, 74, 75, 180, 181, 182, 183, 188, 189, 190, 191, 244, 245, 246, 247, 252, 253, 254, 255]
private theorem finish0618Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0618Input0) = fromList finish0618Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0618 : finishSupport ⟨false, bits4 4⟩ support1611 = 1 • support1534 := by
  have hs : support1611 = fromList finish0618Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0618Chunk0]
  have hn : (finish0618Raw0 : Multiset ℕ) = 1 • (supportNumbers1534 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1534] using hm

private def finish0619Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0619Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0619Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0619Input0) = fromList finish0619Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0619Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def finish0619Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0619Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0619Input1) = fromList finish0619Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0619 : finishSupport ⟨true, bits4 4⟩ support1612 = 2 • support1613 := by
  have hs : support1612 = fromList finish0619Input0 + fromList finish0619Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0619Chunk0, finish0619Chunk1]
  have hn : (finish0619Raw0 : Multiset ℕ) + (finish0619Raw1 : Multiset ℕ) = 2 • (supportNumbers1613 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1613] using hm

private def finish0620Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 432, 433, 434, 435, 436, 437, 438, 439, 496, 497, 498, 499, 500, 501, 502, 503]
private def finish0620Raw0 : List ℕ := [0, 1, 2, 3, 64, 65, 66, 67, 144, 145, 146, 147, 208, 209, 210, 211, 36, 37, 38, 39, 100, 101, 102, 103, 180, 181, 182, 183, 244, 245, 246, 247]
private theorem finish0620Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0620Input0) = fromList finish0620Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0620 : finishSupport ⟨false, bits4 4⟩ support1615 = 1 • support1616 := by
  have hs : support1615 = fromList finish0620Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0620Chunk0]
  have hn : (finish0620Raw0 : Multiset ℕ) = 1 • (supportNumbers1616 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1616] using hm

private def finish0621Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 432, 433, 434, 435, 436, 437, 438, 439, 496, 497, 498, 499, 500, 501, 502, 503]
private def finish0621Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 32, 33, 34, 35, 36, 37, 38, 39, 96, 97, 98, 99, 100, 101, 102, 103, 176, 177, 178, 179, 180, 181, 182, 183, 240, 241, 242, 243, 244, 245, 246, 247]
private theorem finish0621Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0621Input0) = fromList finish0621Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0621Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 656, 657, 658, 659, 660, 661, 662, 663, 720, 721, 722, 723, 724, 725, 726, 727, 800, 801, 802, 803, 804, 805, 806, 807, 864, 865, 866, 867, 868, 869, 870, 871, 944, 945, 946, 947, 948, 949, 950, 951, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015]
private def finish0621Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 32, 33, 34, 35, 36, 37, 38, 39, 96, 97, 98, 99, 100, 101, 102, 103, 176, 177, 178, 179, 180, 181, 182, 183, 240, 241, 242, 243, 244, 245, 246, 247]
private theorem finish0621Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0621Input1) = fromList finish0621Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0621 : finishSupport ⟨true, bits4 4⟩ support1617 = 2 • support1618 := by
  have hs : support1617 = fromList finish0621Input0 + fromList finish0621Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0621Chunk0, finish0621Chunk1]
  have hn : (finish0621Raw0 : Multiset ℕ) + (finish0621Raw1 : Multiset ℕ) = 2 • (supportNumbers1618 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1618] using hm

private def finish0622Input0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 136, 137, 140, 141, 144, 145, 148, 149, 200, 201, 204, 205, 208, 209, 212, 213]
private def finish0622Raw0 : List ℕ := [0, 1, 24, 25, 64, 65, 88, 89, 136, 137, 144, 145, 200, 201, 208, 209]
private theorem finish0622Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0622Input0) = fromList finish0622Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0622 : finishSupport ⟨false, bits4 4⟩ support1619 = 1 • support1620 := by
  have hs : support1619 = fromList finish0622Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0622Chunk0]
  have hn : (finish0622Raw0 : Multiset ℕ) = 1 • (supportNumbers1620 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1620] using hm

private def finish0623Input0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 136, 137, 140, 141, 144, 145, 148, 149, 200, 201, 204, 205, 208, 209, 212, 213, 514, 515, 518, 519, 538, 539, 542, 543, 578, 579, 582, 583, 602, 603, 606, 607, 650, 651, 654, 655, 658, 659, 662, 663, 714, 715, 718, 719, 722, 723, 726, 727]
private def finish0623Raw0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 136, 137, 140, 141, 144, 145, 148, 149, 200, 201, 204, 205, 208, 209, 212, 213, 2, 3, 6, 7, 26, 27, 30, 31, 66, 67, 70, 71, 90, 91, 94, 95, 138, 139, 142, 143, 146, 147, 150, 151, 202, 203, 206, 207, 210, 211, 214, 215]
private theorem finish0623Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0623Input0) = fromList finish0623Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0623 : finishSupport ⟨true, bits4 4⟩ support1621 = 1 • support0411 := by
  have hs : support1621 = fromList finish0623Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0623Chunk0]
  have hn : (finish0623Raw0 : Multiset ℕ) = 1 • (supportNumbers0411 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0411] using hm

private def finish0624Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def finish0624Raw0 : List ℕ := [0, 1, 2, 3, 24, 25, 26, 27, 64, 65, 66, 67, 88, 89, 90, 91, 136, 137, 138, 139, 144, 145, 146, 147, 200, 201, 202, 203, 208, 209, 210, 211]
private theorem finish0624Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0624Input0) = fromList finish0624Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0624 : finishSupport ⟨false, bits4 4⟩ support0411 = 1 • support1622 := by
  have hs : support0411 = fromList finish0624Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0624Chunk0]
  have hn : (finish0624Raw0 : Multiset ℕ) = 1 • (supportNumbers1622 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1622] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
