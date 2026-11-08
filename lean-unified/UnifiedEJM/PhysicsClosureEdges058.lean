import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1033Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623, 672, 674, 676, 678, 680, 682, 684, 686, 737, 739, 741, 743, 745, 747, 749, 751]
private def transition1033Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 128, 704, 130, 706, 132, 708, 134, 710, 136, 712, 138, 714, 140, 716, 142, 718, 193, 641, 195, 643, 197, 645, 199, 647, 201, 649, 203, 651, 205, 653, 207, 655, 288, 864, 290, 866, 292, 868, 294, 870, 296, 872, 298, 874, 300, 876, 302, 878, 353, 801, 355, 803, 357, 805, 359, 807, 361, 809, 363, 811, 365, 813, 367, 815, 416, 992, 418, 994, 420, 996, 422, 998, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 481, 929, 483, 931, 485, 933, 487, 935, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition1033Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1033Input0) = fromList transition1033Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1033 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1162 = 1 • support0739 := by
  have hs : support1162 = fromList transition1033Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1033Chunk0]
  have hn : (transition1033Raw0 : Multiset ℕ) = 1 • (supportNumbers0739 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0739] using hm

private def transition1034Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition1034Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private theorem transition1034Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1034Input0) = fromList transition1034Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1034Input1 : List ℕ := [512, 514, 516, 518, 520, 522, 524, 526, 577, 579, 581, 583, 585, 587, 589, 591, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 768, 770, 772, 774, 776, 778, 780, 782, 833, 835, 837, 839, 841, 843, 845, 847, 896, 898, 900, 902, 904, 906, 908, 910, 961, 963, 965, 967, 969, 971, 973, 975]
private def transition1034Raw1 : List ℕ := [256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private theorem transition1034Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1034Input1) = fromList transition1034Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1034 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0138 = 2 • support0137 := by
  have hs : support0138 = fromList transition1034Input0 + fromList transition1034Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1034Chunk0, transition1034Chunk1]
  have hn : (transition1034Raw0 : Multiset ℕ) + (transition1034Raw1 : Multiset ℕ) = 2 • (supportNumbers0137 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0137] using hm

private def transition1035Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition1035Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 128, 512, 130, 514, 132, 516, 134, 518, 136, 520, 138, 522, 140, 524, 142, 526, 193, 577, 195, 579, 197, 581, 199, 583, 201, 585, 203, 587, 205, 589, 207, 591, 0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 128, 512, 130, 514, 132, 516, 134, 518, 136, 520, 138, 522, 140, 524, 142, 526, 193, 577, 195, 579, 197, 581, 199, 583, 201, 585, 203, 587, 205, 589, 207, 591]
private theorem transition1035Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1035Input0) = fromList transition1035Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1035Input1 : List ℕ := [512, 514, 516, 518, 520, 522, 524, 526, 577, 579, 581, 583, 585, 587, 589, 591, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 768, 770, 772, 774, 776, 778, 780, 782, 833, 835, 837, 839, 841, 843, 845, 847, 896, 898, 900, 902, 904, 906, 908, 910, 961, 963, 965, 967, 969, 971, 973, 975]
private def transition1035Raw1 : List ℕ := [256, 896, 258, 898, 260, 900, 262, 902, 264, 904, 266, 906, 268, 908, 270, 910, 321, 961, 323, 963, 325, 965, 327, 967, 329, 969, 331, 971, 333, 973, 335, 975, 384, 768, 386, 770, 388, 772, 390, 774, 392, 776, 394, 778, 396, 780, 398, 782, 449, 833, 451, 835, 453, 837, 455, 839, 457, 841, 459, 843, 461, 845, 463, 847, 256, 896, 258, 898, 260, 900, 262, 902, 264, 904, 266, 906, 268, 908, 270, 910, 321, 961, 323, 963, 325, 965, 327, 967, 329, 969, 331, 971, 333, 973, 335, 975, 384, 768, 386, 770, 388, 772, 390, 774, 392, 776, 394, 778, 396, 780, 398, 782, 449, 833, 451, 835, 453, 837, 455, 839, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition1035Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1035Input1) = fromList transition1035Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1035 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0138 = 2 • support0138 := by
  have hs : support0138 = fromList transition1035Input0 + fromList transition1035Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1035Chunk0, transition1035Chunk1]
  have hn : (transition1035Raw0 : Multiset ℕ) + (transition1035Raw1 : Multiset ℕ) = 2 • (supportNumbers0138 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0138] using hm

private def transition1036Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition1036Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private theorem transition1036Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1036Input0) = fromList transition1036Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1036Input1 : List ℕ := [512, 514, 516, 518, 520, 522, 524, 526, 577, 579, 581, 583, 585, 587, 589, 591, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 768, 770, 772, 774, 776, 778, 780, 782, 833, 835, 837, 839, 841, 843, 845, 847, 896, 898, 900, 902, 904, 906, 908, 910, 961, 963, 965, 967, 969, 971, 973, 975]
private def transition1036Raw1 : List ℕ := [256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private theorem transition1036Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1036Input1) = fromList transition1036Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1036 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0138 = 2 • support0137 := by
  have hs : support0138 = fromList transition1036Input0 + fromList transition1036Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1036Chunk0, transition1036Chunk1]
  have hn : (transition1036Raw0 : Multiset ℕ) + (transition1036Raw1 : Multiset ℕ) = 2 • (supportNumbers0137 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0137] using hm

private def transition1037Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition1037Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623, 128, 672, 130, 674, 132, 676, 134, 678, 136, 680, 138, 682, 140, 684, 142, 686, 193, 737, 195, 739, 197, 741, 199, 743, 201, 745, 203, 747, 205, 749, 207, 751, 0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623, 128, 672, 130, 674, 132, 676, 134, 678, 136, 680, 138, 682, 140, 684, 142, 686, 193, 737, 195, 739, 197, 741, 199, 743, 201, 745, 203, 747, 205, 749, 207, 751]
private theorem transition1037Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1037Input0) = fromList transition1037Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1037Input1 : List ℕ := [512, 514, 516, 518, 520, 522, 524, 526, 577, 579, 581, 583, 585, 587, 589, 591, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 768, 770, 772, 774, 776, 778, 780, 782, 833, 835, 837, 839, 841, 843, 845, 847, 896, 898, 900, 902, 904, 906, 908, 910, 961, 963, 965, 967, 969, 971, 973, 975]
private def transition1037Raw1 : List ℕ := [256, 800, 258, 802, 260, 804, 262, 806, 264, 808, 266, 810, 268, 812, 270, 814, 321, 865, 323, 867, 325, 869, 327, 871, 329, 873, 331, 875, 333, 877, 335, 879, 384, 928, 386, 930, 388, 932, 390, 934, 392, 936, 394, 938, 396, 940, 398, 942, 449, 993, 451, 995, 453, 997, 455, 999, 457, 1001, 459, 1003, 461, 1005, 463, 1007, 256, 800, 258, 802, 260, 804, 262, 806, 264, 808, 266, 810, 268, 812, 270, 814, 321, 865, 323, 867, 325, 869, 327, 871, 329, 873, 331, 875, 333, 877, 335, 879, 384, 928, 386, 930, 388, 932, 390, 934, 392, 936, 394, 938, 396, 940, 398, 942, 449, 993, 451, 995, 453, 997, 455, 999, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition1037Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1037Input1) = fromList transition1037Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1037 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0138 = 2 • support0930 := by
  have hs : support0138 = fromList transition1037Input0 + fromList transition1037Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1037Chunk0, transition1037Chunk1]
  have hn : (transition1037Raw0 : Multiset ℕ) + (transition1037Raw1 : Multiset ℕ) = 2 • (supportNumbers0930 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0930] using hm

private def transition1038Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 265, 267, 269, 271, 328, 330, 332, 334]
private def transition1038Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 9, 11, 13, 15, 72, 74, 76, 78]
private theorem transition1038Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1038Input0) = fromList transition1038Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1038 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0139 = 1 • support0217 := by
  have hs : support0139 = fromList transition1038Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1038Chunk0]
  have hn : (transition1038Raw0 : Multiset ℕ) = 1 • (supportNumbers0217 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0217] using hm

private def transition1039Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 265, 267, 269, 271, 328, 330, 332, 334]
private def transition1039Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 9, 11, 13, 15, 72, 74, 76, 78]
private theorem transition1039Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1039Input0) = fromList transition1039Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1039 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0139 = 1 • support0217 := by
  have hs : support0139 = fromList transition1039Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1039Chunk0]
  have hn : (transition1039Raw0 : Multiset ℕ) = 1 • (supportNumbers0217 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0217] using hm

private def transition1040Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 265, 267, 269, 271, 328, 330, 332, 334]
private def transition1040Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 9, 11, 13, 15, 72, 74, 76, 78]
private theorem transition1040Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1040Input0) = fromList transition1040Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1040 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0139 = 1 • support0217 := by
  have hs : support0139 = fromList transition1040Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1040Chunk0]
  have hn : (transition1040Raw0 : Multiset ℕ) = 1 • (supportNumbers0217 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0217] using hm

private def transition1041Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78]
private def transition1041Raw0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76]
private theorem transition1041Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1041Input0) = fromList transition1041Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1041 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0217 = 1 • support1163 := by
  have hs : support0217 = fromList transition1041Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1041Chunk0]
  have hn : (transition1041Raw0 : Multiset ℕ) = 1 • (supportNumbers1163 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1163] using hm

private def transition1042Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78]
private def transition1042Raw0 : List ℕ := [0, 578, 4, 582, 9, 587, 13, 591, 65, 515, 69, 519, 72, 522, 76, 526]
private theorem transition1042Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1042Input0) = fromList transition1042Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1042 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0217 = 1 • support1165 := by
  have hs : support0217 = fromList transition1042Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1042Chunk0]
  have hn : (transition1042Raw0 : Multiset ℕ) = 1 • (supportNumbers1165 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1165] using hm

private def transition1043Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 265, 267, 269, 271, 328, 330, 332, 334]
private def transition1043Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 9, 11, 13, 15, 72, 74, 76, 78]
private theorem transition1043Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1043Input0) = fromList transition1043Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1043 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0139 = 1 • support0217 := by
  have hs : support0139 = fromList transition1043Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1043Chunk0]
  have hn : (transition1043Raw0 : Multiset ℕ) = 1 • (supportNumbers0217 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0217] using hm

private def transition1044Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78]
private def transition1044Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78]
private theorem transition1044Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1044Input0) = fromList transition1044Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1044 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0217 = 1 • support0217 := by
  have hs : support0217 = fromList transition1044Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1044Chunk0]
  have hn : (transition1044Raw0 : Multiset ℕ) = 1 • (supportNumbers0217 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0217] using hm

private def transition1045Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78]
private def transition1045Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526]
private theorem transition1045Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1045Input0) = fromList transition1045Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1045 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0217 = 1 • support0310 := by
  have hs : support0217 = fromList transition1045Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1045Chunk0]
  have hn : (transition1045Raw0 : Multiset ℕ) = 1 • (supportNumbers0310 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0310] using hm

private def transition1046Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 265, 267, 269, 271, 328, 330, 332, 334, 640, 642, 644, 646, 705, 707, 709, 711, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition1046Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 9, 11, 13, 15, 72, 74, 76, 78, 384, 386, 388, 390, 449, 451, 453, 455, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition1046Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1046Input0) = fromList transition1046Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1046 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0140 = 1 • support0218 := by
  have hs : support0140 = fromList transition1046Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1046Chunk0]
  have hn : (transition1046Raw0 : Multiset ℕ) = 1 • (supportNumbers0218 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0218] using hm

private def transition1047Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 265, 267, 269, 271, 328, 330, 332, 334, 640, 642, 644, 646, 705, 707, 709, 711, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition1047Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 9, 649, 11, 651, 13, 653, 15, 655, 72, 712, 74, 714, 76, 716, 78, 718, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 393, 777, 395, 779, 397, 781, 399, 783, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition1047Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1047Input0) = fromList transition1047Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1047 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0140 = 1 • support0219 := by
  have hs : support0140 = fromList transition1047Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1047Chunk0]
  have hn : (transition1047Raw0 : Multiset ℕ) = 1 • (supportNumbers0219 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0219] using hm

private def transition1048Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 265, 267, 269, 271, 328, 330, 332, 334, 640, 642, 644, 646, 705, 707, 709, 711, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition1048Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 9, 11, 13, 15, 72, 74, 76, 78, 384, 386, 388, 390, 449, 451, 453, 455, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition1048Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1048Input0) = fromList transition1048Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1048 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0140 = 1 • support0218 := by
  have hs : support0140 = fromList transition1048Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1048Chunk0]
  have hn : (transition1048Raw0 : Multiset ℕ) = 1 • (supportNumbers0218 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0218] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
