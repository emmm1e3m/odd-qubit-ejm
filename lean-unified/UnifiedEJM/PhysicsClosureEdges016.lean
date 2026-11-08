import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0338Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private def transition0338Raw0 : List ℕ := [0, 578, 4, 582, 9, 587, 13, 591, 65, 515, 69, 519, 72, 522, 76, 526, 129, 707, 133, 711, 136, 714, 140, 718, 192, 642, 196, 646, 201, 651, 205, 655]
private theorem transition0338Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0338Input0) = fromList transition0338Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0338 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0082 = 1 • support0752 := by
  have hs : support0082 = fromList transition0338Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0338Chunk0]
  have hn : (transition0338Raw0 : Multiset ℕ) = 1 • (supportNumbers0752 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0752] using hm

private def transition0339Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition0339Raw0 : List ℕ := [0, 2, 4, 6, 552, 554, 556, 558, 65, 67, 69, 71, 617, 619, 621, 623, 129, 131, 133, 135, 681, 683, 685, 687, 192, 194, 196, 198, 744, 746, 748, 750, 545, 547, 549, 551, 9, 11, 13, 15, 608, 610, 612, 614, 72, 74, 76, 78, 672, 674, 676, 678, 136, 138, 140, 142, 737, 739, 741, 743, 201, 203, 205, 207]
private theorem transition0339Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0339Input0) = fromList transition0339Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0339 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0042 = 1 • support0753 := by
  have hs : support0042 = fromList transition0339Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0339Chunk0]
  have hn : (transition0339Raw0 : Multiset ℕ) = 1 • (supportNumbers0753 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0753] using hm

private def transition0340Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 545, 547, 549, 551, 552, 554, 556, 558, 608, 610, 612, 614, 617, 619, 621, 623, 672, 674, 676, 678, 681, 683, 685, 687, 737, 739, 741, 743, 744, 746, 748, 750]
private def transition0340Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 289, 291, 293, 295, 296, 298, 300, 302, 352, 354, 356, 358, 361, 363, 365, 367, 416, 418, 420, 422, 425, 427, 429, 431, 481, 483, 485, 487, 488, 490, 492, 494]
private theorem transition0340Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0340Input0) = fromList transition0340Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0340 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0753 = 1 • support0754 := by
  have hs : support0753 = fromList transition0340Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0340Chunk0]
  have hn : (transition0340Raw0 : Multiset ℕ) = 1 • (supportNumbers0754 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0754] using hm

private def transition0341Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 545, 547, 549, 551, 552, 554, 556, 558, 608, 610, 612, 614, 617, 619, 621, 623, 672, 674, 676, 678, 681, 683, 685, 687, 737, 739, 741, 743, 744, 746, 748, 750]
private def transition0341Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 129, 705, 131, 707, 133, 709, 135, 711, 136, 712, 138, 714, 140, 716, 142, 718, 192, 640, 194, 642, 196, 644, 198, 646, 201, 649, 203, 651, 205, 653, 207, 655, 289, 865, 291, 867, 293, 869, 295, 871, 296, 872, 298, 874, 300, 876, 302, 878, 352, 800, 354, 802, 356, 804, 358, 806, 361, 809, 363, 811, 365, 813, 367, 815, 416, 992, 418, 994, 420, 996, 422, 998, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 481, 929, 483, 931, 485, 933, 487, 935, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition0341Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0341Input0) = fromList transition0341Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0341 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0753 = 1 • support0756 := by
  have hs : support0753 = fromList transition0341Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0341Chunk0]
  have hn : (transition0341Raw0 : Multiset ℕ) = 1 • (supportNumbers0756 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0756] using hm

private def transition0342Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition0342Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 1, 3, 5, 7, 9, 11, 13, 15, 64, 66, 68, 70, 72, 74, 76, 78, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private theorem transition0342Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0342Input0) = fromList transition0342Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0342Input1 : List ℕ := [513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 768, 770, 772, 774, 776, 778, 780, 782, 833, 835, 837, 839, 841, 843, 845, 847, 897, 899, 901, 903, 905, 907, 909, 911, 960, 962, 964, 966, 968, 970, 972, 974]
private def transition0342Raw1 : List ℕ := [257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private theorem transition0342Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0342Input1) = fromList transition0342Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0342 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0043 = 1 • support0084 := by
  have hs : support0043 = fromList transition0342Input0 + fromList transition0342Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0342Chunk0, transition0342Chunk1]
  have hn : (transition0342Raw0 : Multiset ℕ) + (transition0342Raw1 : Multiset ℕ) = 1 • (supportNumbers0084 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0084] using hm

private def transition0343Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition0343Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 129, 513, 131, 515, 133, 517, 135, 519, 137, 521, 139, 523, 141, 525, 143, 527, 192, 576, 194, 578, 196, 580, 198, 582, 200, 584, 202, 586, 204, 588, 206, 590, 1, 641, 3, 643, 5, 645, 7, 647, 9, 649, 11, 651, 13, 653, 15, 655, 64, 704, 66, 706, 68, 708, 70, 710, 72, 712, 74, 714, 76, 716, 78, 718, 128, 512, 130, 514, 132, 516, 134, 518, 136, 520, 138, 522, 140, 524, 142, 526, 193, 577, 195, 579, 197, 581, 199, 583, 201, 585, 203, 587, 205, 589, 207, 591]
private theorem transition0343Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0343Input0) = fromList transition0343Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0343Input1 : List ℕ := [513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 768, 770, 772, 774, 776, 778, 780, 782, 833, 835, 837, 839, 841, 843, 845, 847, 897, 899, 901, 903, 905, 907, 909, 911, 960, 962, 964, 966, 968, 970, 972, 974]
private def transition0343Raw1 : List ℕ := [257, 897, 259, 899, 261, 901, 263, 903, 265, 905, 267, 907, 269, 909, 271, 911, 320, 960, 322, 962, 324, 964, 326, 966, 328, 968, 330, 970, 332, 972, 334, 974, 384, 768, 386, 770, 388, 772, 390, 774, 392, 776, 394, 778, 396, 780, 398, 782, 449, 833, 451, 835, 453, 837, 455, 839, 457, 841, 459, 843, 461, 845, 463, 847, 256, 896, 258, 898, 260, 900, 262, 902, 264, 904, 266, 906, 268, 908, 270, 910, 321, 961, 323, 963, 325, 965, 327, 967, 329, 969, 331, 971, 333, 973, 335, 975, 385, 769, 387, 771, 389, 773, 391, 775, 393, 777, 395, 779, 397, 781, 399, 783, 448, 832, 450, 834, 452, 836, 454, 838, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition0343Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0343Input1) = fromList transition0343Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0343 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0043 = 1 • support0085 := by
  have hs : support0043 = fromList transition0343Input0 + fromList transition0343Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0343Chunk0, transition0343Chunk1]
  have hn : (transition0343Raw0 : Multiset ℕ) + (transition0343Raw1 : Multiset ℕ) = 1 • (supportNumbers0085 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0085] using hm

private def transition0344Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition0344Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 1, 3, 5, 7, 9, 11, 13, 15, 64, 66, 68, 70, 72, 74, 76, 78, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private theorem transition0344Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0344Input0) = fromList transition0344Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0344Input1 : List ℕ := [513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 768, 770, 772, 774, 776, 778, 780, 782, 833, 835, 837, 839, 841, 843, 845, 847, 897, 899, 901, 903, 905, 907, 909, 911, 960, 962, 964, 966, 968, 970, 972, 974]
private def transition0344Raw1 : List ℕ := [257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private theorem transition0344Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0344Input1) = fromList transition0344Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0344 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0043 = 1 • support0084 := by
  have hs : support0043 = fromList transition0344Input0 + fromList transition0344Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0344Chunk0, transition0344Chunk1]
  have hn : (transition0344Raw0 : Multiset ℕ) + (transition0344Raw1 : Multiset ℕ) = 1 • (supportNumbers0084 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0084] using hm

private def transition0345Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition0345Raw0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77, 128, 129, 132, 133, 136, 137, 140, 141, 192, 193, 196, 197, 200, 201, 204, 205]
private theorem transition0345Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0345Input0) = fromList transition0345Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0345Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition0345Raw1 : List ℕ := [2, 3, 6, 7, 10, 11, 14, 15, 66, 67, 70, 71, 74, 75, 78, 79, 130, 131, 134, 135, 138, 139, 142, 143, 194, 195, 198, 199, 202, 203, 206, 207]
private theorem transition0345Chunk1 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0345Input1) = fromList transition0345Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0345 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0084 = 1 • support0148 := by
  have hs : support0084 = fromList transition0345Input0 + fromList transition0345Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0345Chunk0, transition0345Chunk1]
  have hn : (transition0345Raw0 : Multiset ℕ) + (transition0345Raw1 : Multiset ℕ) = 1 • (supportNumbers0148 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0148] using hm

private def transition0346Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition0346Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 8, 9, 586, 587, 12, 13, 590, 591, 64, 65, 514, 515, 68, 69, 518, 519, 72, 73, 522, 523, 76, 77, 526, 527, 128, 129, 706, 707, 132, 133, 710, 711, 136, 137, 714, 715, 140, 141, 718, 719, 192, 193, 642, 643, 196, 197, 646, 647, 200, 201, 650, 651, 204, 205, 654, 655]
private theorem transition0346Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0346Input0) = fromList transition0346Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0346Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition0346Raw1 : List ℕ := [576, 577, 2, 3, 580, 581, 6, 7, 584, 585, 10, 11, 588, 589, 14, 15, 512, 513, 66, 67, 516, 517, 70, 71, 520, 521, 74, 75, 524, 525, 78, 79, 704, 705, 130, 131, 708, 709, 134, 135, 712, 713, 138, 139, 716, 717, 142, 143, 640, 641, 194, 195, 644, 645, 198, 199, 648, 649, 202, 203, 652, 653, 206, 207]
private theorem transition0346Chunk1 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0346Input1) = fromList transition0346Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0346 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0084 = 1 • support0149 := by
  have hs : support0084 = fromList transition0346Input0 + fromList transition0346Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0346Chunk0, transition0346Chunk1]
  have hn : (transition0346Raw0 : Multiset ℕ) + (transition0346Raw1 : Multiset ℕ) = 1 • (supportNumbers0149 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0149] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
