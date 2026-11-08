import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0615Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839, 904, 906, 908, 910, 969, 971, 973, 975]
private def transition0615Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 136, 680, 138, 682, 140, 684, 142, 686, 201, 745, 203, 747, 205, 749, 207, 751, 8, 552, 10, 554, 12, 556, 14, 558, 73, 617, 75, 619, 77, 621, 79, 623, 128, 672, 130, 674, 132, 676, 134, 678, 193, 737, 195, 739, 197, 741, 199, 743, 264, 808, 266, 810, 268, 812, 270, 814, 329, 873, 331, 875, 333, 877, 335, 879, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 256, 800, 258, 802, 260, 804, 262, 806, 321, 865, 323, 867, 325, 869, 327, 871, 392, 936, 394, 938, 396, 940, 398, 942, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition0615Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0615Input0) = fromList transition0615Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0615 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0078 = 1 • support0930 := by
  have hs : support0078 = fromList transition0615Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0615Chunk0]
  have hn : (transition0615Raw0 : Multiset ℕ) = 1 • (supportNumbers0930 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0930] using hm

private def transition0616Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition0616Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private theorem transition0616Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0616Input0) = fromList transition0616Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0616Input1 : List ℕ := [544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623, 672, 674, 676, 678, 680, 682, 684, 686, 737, 739, 741, 743, 745, 747, 749, 751, 800, 802, 804, 806, 808, 810, 812, 814, 865, 867, 869, 871, 873, 875, 877, 879, 928, 930, 932, 934, 936, 938, 940, 942, 993, 995, 997, 999, 1001, 1003, 1005, 1007]
private def transition0616Raw1 : List ℕ := [288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367, 416, 418, 420, 422, 424, 426, 428, 430, 481, 483, 485, 487, 489, 491, 493, 495, 288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367, 416, 418, 420, 422, 424, 426, 428, 430, 481, 483, 485, 487, 489, 491, 493, 495]
private theorem transition0616Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0616Input1) = fromList transition0616Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0616 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0930 = 2 • support0737 := by
  have hs : support0930 = fromList transition0616Input0 + fromList transition0616Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0616Chunk0, transition0616Chunk1]
  have hn : (transition0616Raw0 : Multiset ℕ) + (transition0616Raw1 : Multiset ℕ) = 2 • (supportNumbers0737 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0737] using hm

private def transition0617Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition0617Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 128, 704, 130, 706, 132, 708, 134, 710, 136, 712, 138, 714, 140, 716, 142, 718, 193, 641, 195, 643, 197, 645, 199, 647, 201, 649, 203, 651, 205, 653, 207, 655, 0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 128, 704, 130, 706, 132, 708, 134, 710, 136, 712, 138, 714, 140, 716, 142, 718, 193, 641, 195, 643, 197, 645, 199, 647, 201, 649, 203, 651, 205, 653, 207, 655]
private theorem transition0617Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0617Input0) = fromList transition0617Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0617Input1 : List ℕ := [544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623, 672, 674, 676, 678, 680, 682, 684, 686, 737, 739, 741, 743, 745, 747, 749, 751, 800, 802, 804, 806, 808, 810, 812, 814, 865, 867, 869, 871, 873, 875, 877, 879, 928, 930, 932, 934, 936, 938, 940, 942, 993, 995, 997, 999, 1001, 1003, 1005, 1007]
private def transition0617Raw1 : List ℕ := [288, 864, 290, 866, 292, 868, 294, 870, 296, 872, 298, 874, 300, 876, 302, 878, 353, 801, 355, 803, 357, 805, 359, 807, 361, 809, 363, 811, 365, 813, 367, 815, 416, 992, 418, 994, 420, 996, 422, 998, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 481, 929, 483, 931, 485, 933, 487, 935, 489, 937, 491, 939, 493, 941, 495, 943, 288, 864, 290, 866, 292, 868, 294, 870, 296, 872, 298, 874, 300, 876, 302, 878, 353, 801, 355, 803, 357, 805, 359, 807, 361, 809, 363, 811, 365, 813, 367, 815, 416, 992, 418, 994, 420, 996, 422, 998, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 481, 929, 483, 931, 485, 933, 487, 935, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition0617Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0617Input1) = fromList transition0617Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0617 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0930 = 2 • support0739 := by
  have hs : support0930 = fromList transition0617Input0 + fromList transition0617Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0617Chunk0, transition0617Chunk1]
  have hn : (transition0617Raw0 : Multiset ℕ) + (transition0617Raw1 : Multiset ℕ) = 2 • (supportNumbers0739 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0739] using hm

private def transition0618Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 521, 523, 525, 527, 584, 586, 588, 590]
private def transition0618Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 265, 267, 269, 271, 328, 330, 332, 334]
private theorem transition0618Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0618Input0) = fromList transition0618Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0618 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0079 = 1 • support0139 := by
  have hs : support0079 = fromList transition0618Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0618Chunk0]
  have hn : (transition0618Raw0 : Multiset ℕ) = 1 • (supportNumbers0139 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0139] using hm

private def transition0619Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 521, 523, 525, 527, 584, 586, 588, 590]
private def transition0619Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 265, 905, 267, 907, 269, 909, 271, 911, 328, 968, 330, 970, 332, 972, 334, 974]
private theorem transition0619Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0619Input0) = fromList transition0619Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0619 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0079 = 1 • support0140 := by
  have hs : support0079 = fromList transition0619Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0619Chunk0]
  have hn : (transition0619Raw0 : Multiset ℕ) = 1 • (supportNumbers0140 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0140] using hm

private def transition0620Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 521, 523, 525, 527, 584, 586, 588, 590]
private def transition0620Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 265, 267, 269, 271, 328, 330, 332, 334]
private theorem transition0620Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0620Input0) = fromList transition0620Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0620 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0079 = 1 • support0139 := by
  have hs : support0079 = fromList transition0620Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0620Chunk0]
  have hn : (transition0620Raw0 : Multiset ℕ) = 1 • (supportNumbers0139 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0139] using hm

private def transition0621Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 265, 267, 269, 271, 328, 330, 332, 334]
private def transition0621Raw0 : List ℕ := [0, 4, 65, 69, 11, 15, 74, 78]
private theorem transition0621Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0621Input0) = fromList transition0621Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0621 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0139 = 1 • support0931 := by
  have hs : support0139 = fromList transition0621Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0621Chunk0]
  have hn : (transition0621Raw0 : Multiset ℕ) = 1 • (supportNumbers0931 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0931] using hm

private def transition0622Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 265, 267, 269, 271, 328, 330, 332, 334]
private def transition0622Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 585, 11, 589, 15, 520, 74, 524, 78]
private theorem transition0622Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0622Input0) = fromList transition0622Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0622 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0139 = 1 • support0933 := by
  have hs : support0139 = fromList transition0622Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0622Chunk0]
  have hn : (transition0622Raw0 : Multiset ℕ) = 1 • (supportNumbers0933 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0933] using hm

private def transition0623Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 521, 523, 525, 527, 584, 586, 588, 590]
private def transition0623Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 265, 809, 267, 811, 269, 813, 271, 815, 328, 872, 330, 874, 332, 876, 334, 878]
private theorem transition0623Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0623Input0) = fromList transition0623Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0623 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0079 = 1 • support0934 := by
  have hs : support0079 = fromList transition0623Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0623Chunk0]
  have hn : (transition0623Raw0 : Multiset ℕ) = 1 • (supportNumbers0934 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0934] using hm

private def transition0624Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 265, 267, 269, 271, 328, 330, 332, 334, 544, 546, 548, 550, 609, 611, 613, 615, 809, 811, 813, 815, 872, 874, 876, 878]
private def transition0624Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 9, 11, 13, 15, 72, 74, 76, 78, 288, 290, 292, 294, 353, 355, 357, 359, 297, 299, 301, 303, 360, 362, 364, 366]
private theorem transition0624Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0624Input0) = fromList transition0624Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0624 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0934 = 1 • support0935 := by
  have hs : support0934 = fromList transition0624Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0624Chunk0]
  have hn : (transition0624Raw0 : Multiset ℕ) = 1 • (supportNumbers0935 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0935] using hm

private def transition0625Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 265, 267, 269, 271, 328, 330, 332, 334, 544, 546, 548, 550, 609, 611, 613, 615, 809, 811, 813, 815, 872, 874, 876, 878]
private def transition0625Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 9, 585, 11, 587, 13, 589, 15, 591, 72, 520, 74, 522, 76, 524, 78, 526, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 297, 873, 299, 875, 301, 877, 303, 879, 360, 808, 362, 810, 364, 812, 366, 814]
private theorem transition0625Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0625Input0) = fromList transition0625Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0625 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0934 = 1 • support0937 := by
  have hs : support0934 = fromList transition0625Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0625Chunk0]
  have hn : (transition0625Raw0 : Multiset ℕ) = 1 • (supportNumbers0937 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0937] using hm

private def transition0626Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 257, 259, 261, 263, 320, 322, 324, 326, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition0626Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition0626Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0626Input0) = fromList transition0626Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0626 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0080 = 1 • support0076 := by
  have hs : support0080 = fromList transition0626Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0626Chunk0]
  have hn : (transition0626Raw0 : Multiset ℕ) = 1 • (supportNumbers0076 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0076] using hm

private def transition0627Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 257, 259, 261, 263, 320, 322, 324, 326, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition0627Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 521, 523, 525, 527, 584, 586, 588, 590, 641, 643, 645, 647, 704, 706, 708, 710, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition0627Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0627Input0) = fromList transition0627Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0627 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0080 = 1 • support0141 := by
  have hs : support0080 = fromList transition0627Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0627Chunk0]
  have hn : (transition0627Raw0 : Multiset ℕ) = 1 • (supportNumbers0141 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0141] using hm

private def transition0628Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 257, 259, 261, 263, 320, 322, 324, 326, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition0628Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition0628Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0628Input0) = fromList transition0628Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0628 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0080 = 1 • support0076 := by
  have hs : support0080 = fromList transition0628Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0628Chunk0]
  have hn : (transition0628Raw0 : Multiset ℕ) = 1 • (supportNumbers0076 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0076] using hm

private def transition0629Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 257, 259, 261, 263, 320, 322, 324, 326, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition0629Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 681, 683, 685, 687, 744, 746, 748, 750, 545, 547, 549, 551, 608, 610, 612, 614, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition0629Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0629Input0) = fromList transition0629Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0629 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0080 = 1 • support0939 := by
  have hs : support0080 = fromList transition0629Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0629Chunk0]
  have hn : (transition0629Raw0 : Multiset ℕ) = 1 • (supportNumbers0939 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0939] using hm

private def transition0630Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 545, 547, 549, 551, 608, 610, 612, 614, 681, 683, 685, 687, 744, 746, 748, 750]
private def transition0630Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 289, 291, 293, 295, 352, 354, 356, 358, 425, 427, 429, 431, 488, 490, 492, 494]
private theorem transition0630Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0630Input0) = fromList transition0630Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0630 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0939 = 1 • support0940 := by
  have hs : support0939 = fromList transition0630Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0630Chunk0]
  have hn : (transition0630Raw0 : Multiset ℕ) = 1 • (supportNumbers0940 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0940] using hm

private def transition0631Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 545, 547, 549, 551, 608, 610, 612, 614, 681, 683, 685, 687, 744, 746, 748, 750]
private def transition0631Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 136, 712, 138, 714, 140, 716, 142, 718, 201, 649, 203, 651, 205, 653, 207, 655, 289, 865, 291, 867, 293, 869, 295, 871, 352, 800, 354, 802, 356, 804, 358, 806, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition0631Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0631Input0) = fromList transition0631Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0631 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0939 = 1 • support0942 := by
  have hs : support0939 = fromList transition0631Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0631Chunk0]
  have hn : (transition0631Raw0 : Multiset ℕ) = 1 • (supportNumbers0942 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0942] using hm

private def transition0632Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 257, 259, 261, 263, 320, 322, 324, 326, 392, 394, 396, 398, 457, 459, 461, 463, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847, 897, 899, 901, 903, 960, 962, 964, 966]
private def transition0632Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 1, 3, 5, 7, 64, 66, 68, 70, 136, 138, 140, 142, 201, 203, 205, 207, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455, 264, 266, 268, 270, 329, 331, 333, 335, 385, 387, 389, 391, 448, 450, 452, 454]
private theorem transition0632Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0632Input0) = fromList transition0632Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0632 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0081 = 1 • support0142 := by
  have hs : support0081 = fromList transition0632Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0632Chunk0]
  have hn : (transition0632Raw0 : Multiset ℕ) = 1 • (supportNumbers0142 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0142] using hm

private def transition0633Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 257, 259, 261, 263, 320, 322, 324, 326, 392, 394, 396, 398, 457, 459, 461, 463, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847, 897, 899, 901, 903, 960, 962, 964, 966]
private def transition0633Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 137, 521, 139, 523, 141, 525, 143, 527, 200, 584, 202, 586, 204, 588, 206, 590, 1, 641, 3, 643, 5, 645, 7, 647, 64, 704, 66, 706, 68, 708, 70, 710, 136, 520, 138, 522, 140, 524, 142, 526, 201, 585, 203, 587, 205, 589, 207, 591, 265, 905, 267, 907, 269, 909, 271, 911, 328, 968, 330, 970, 332, 972, 334, 974, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 264, 904, 266, 906, 268, 908, 270, 910, 329, 969, 331, 971, 333, 973, 335, 975, 385, 769, 387, 771, 389, 773, 391, 775, 448, 832, 450, 834, 452, 836, 454, 838]
private theorem transition0633Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0633Input0) = fromList transition0633Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0633 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0081 = 1 • support0143 := by
  have hs : support0081 = fromList transition0633Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0633Chunk0]
  have hn : (transition0633Raw0 : Multiset ℕ) = 1 • (supportNumbers0143 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0143] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
