import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2626Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 264, 266, 268, 270, 329, 331, 333, 335, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2626Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 8, 10, 12, 14, 73, 75, 77, 79, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition2626Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2626Input0) = fromList transition2626Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2626 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0382 = 1 • support0215 := by
  have hs : support0382 = fromList transition2626Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2626Chunk0]
  have hn : (transition2626Raw0 : Multiset ℕ) = 1 • (supportNumbers0215 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0215] using hm

private def transition2627Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 264, 266, 268, 270, 329, 331, 333, 335, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2627Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 8, 10, 12, 14, 73, 75, 77, 79, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition2627Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2627Input0) = fromList transition2627Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2627 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0382 = 1 • support0215 := by
  have hs : support0382 = fromList transition2627Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2627Chunk0]
  have hn : (transition2627Raw0 : Multiset ℕ) = 1 • (supportNumbers0215 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0215] using hm

private def transition2628Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 264, 266, 268, 270, 329, 331, 333, 335, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2628Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 8, 10, 12, 14, 73, 75, 77, 79, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition2628Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2628Input0) = fromList transition2628Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2628 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0382 = 1 • support0215 := by
  have hs : support0382 = fromList transition2628Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2628Chunk0]
  have hn : (transition2628Raw0 : Multiset ℕ) = 1 • (supportNumbers0215 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0215] using hm

private def transition2629Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 264, 266, 268, 270, 329, 331, 333, 335, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2629Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 8, 10, 12, 14, 73, 75, 77, 79, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition2629Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2629Input0) = fromList transition2629Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2629 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0382 = 1 • support0215 := by
  have hs : support0382 = fromList transition2629Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2629Chunk0]
  have hn : (transition2629Raw0 : Multiset ℕ) = 1 • (supportNumbers0215 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0215] using hm

private def transition2630Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private def transition2630Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private theorem transition2630Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2630Input0) = fromList transition2630Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2630 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0215 = 1 • support0215 := by
  have hs : support0215 = fromList transition2630Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2630Chunk0]
  have hn : (transition2630Raw0 : Multiset ℕ) = 1 • (supportNumbers0215 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0215] using hm

private def transition2631Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private def transition2631Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 128, 704, 130, 706, 132, 708, 134, 710, 136, 712, 138, 714, 140, 716, 142, 718, 193, 641, 195, 643, 197, 645, 199, 647, 201, 649, 203, 651, 205, 653, 207, 655]
private theorem transition2631Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2631Input0) = fromList transition2631Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2631 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0215 = 1 • support0929 := by
  have hs : support0215 = fromList transition2631Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2631Chunk0]
  have hn : (transition2631Raw0 : Multiset ℕ) = 1 • (supportNumbers0929 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0929] using hm

private def transition2632Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 264, 266, 268, 270, 329, 331, 333, 335, 392, 394, 396, 398, 457, 459, 461, 463, 512, 514, 516, 518, 577, 579, 581, 583, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847, 904, 906, 908, 910, 969, 971, 973, 975]
private def transition2632Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 8, 10, 12, 14, 73, 75, 77, 79, 136, 138, 140, 142, 201, 203, 205, 207, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455, 264, 266, 268, 270, 329, 331, 333, 335, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition2632Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2632Input0) = fromList transition2632Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2632 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0383 = 1 • support0137 := by
  have hs : support0383 = fromList transition2632Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2632Chunk0]
  have hn : (transition2632Raw0 : Multiset ℕ) = 1 • (supportNumbers0137 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0137] using hm

private def transition2633Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 264, 266, 268, 270, 329, 331, 333, 335, 392, 394, 396, 398, 457, 459, 461, 463, 512, 514, 516, 518, 577, 579, 581, 583, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847, 904, 906, 908, 910, 969, 971, 973, 975]
private def transition2633Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 128, 512, 130, 514, 132, 516, 134, 518, 193, 577, 195, 579, 197, 581, 199, 583, 8, 648, 10, 650, 12, 652, 14, 654, 73, 713, 75, 715, 77, 717, 79, 719, 136, 520, 138, 522, 140, 524, 142, 526, 201, 585, 203, 587, 205, 589, 207, 591, 256, 896, 258, 898, 260, 900, 262, 902, 321, 961, 323, 963, 325, 965, 327, 967, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 264, 904, 266, 906, 268, 908, 270, 910, 329, 969, 331, 971, 333, 973, 335, 975, 392, 776, 394, 778, 396, 780, 398, 782, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition2633Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2633Input0) = fromList transition2633Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2633 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0383 = 1 • support0138 := by
  have hs : support0383 = fromList transition2633Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2633Chunk0]
  have hn : (transition2633Raw0 : Multiset ℕ) = 1 • (supportNumbers0138 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0138] using hm

private def transition2634Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 264, 266, 268, 270, 329, 331, 333, 335, 392, 394, 396, 398, 457, 459, 461, 463, 512, 514, 516, 518, 577, 579, 581, 583, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847, 904, 906, 908, 910, 969, 971, 973, 975]
private def transition2634Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 8, 10, 12, 14, 73, 75, 77, 79, 136, 138, 140, 142, 201, 203, 205, 207, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455, 264, 266, 268, 270, 329, 331, 333, 335, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition2634Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2634Input0) = fromList transition2634Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2634 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0383 = 1 • support0137 := by
  have hs : support0383 = fromList transition2634Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2634Chunk0]
  have hn : (transition2634Raw0 : Multiset ℕ) = 1 • (supportNumbers0137 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0137] using hm

private def transition2635Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 264, 266, 268, 270, 329, 331, 333, 335, 392, 394, 396, 398, 457, 459, 461, 463, 512, 514, 516, 518, 577, 579, 581, 583, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847, 904, 906, 908, 910, 969, 971, 973, 975]
private def transition2635Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 128, 672, 130, 674, 132, 676, 134, 678, 193, 737, 195, 739, 197, 741, 199, 743, 8, 552, 10, 554, 12, 556, 14, 558, 73, 617, 75, 619, 77, 621, 79, 623, 136, 680, 138, 682, 140, 684, 142, 686, 201, 745, 203, 747, 205, 749, 207, 751, 256, 800, 258, 802, 260, 804, 262, 806, 321, 865, 323, 867, 325, 869, 327, 871, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 264, 808, 266, 810, 268, 812, 270, 814, 329, 873, 331, 875, 333, 877, 335, 879, 392, 936, 394, 938, 396, 940, 398, 942, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition2635Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2635Input0) = fromList transition2635Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2635 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0383 = 1 • support0930 := by
  have hs : support0383 = fromList transition2635Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2635Chunk0]
  have hn : (transition2635Raw0 : Multiset ℕ) = 1 • (supportNumbers0930 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0930] using hm

private def transition2636Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition2636Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition2636Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2636Input0) = fromList transition2636Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2636 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0384 = 1 • support0040 := by
  have hs : support0384 = fromList transition2636Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2636Chunk0]
  have hn : (transition2636Raw0 : Multiset ℕ) = 1 • (supportNumbers0040 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0040] using hm

private def transition2637Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition2637Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition2637Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2637Input0) = fromList transition2637Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2637 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0384 = 1 • support0040 := by
  have hs : support0384 = fromList transition2637Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2637Chunk0]
  have hn : (transition2637Raw0 : Multiset ℕ) = 1 • (supportNumbers0040 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0040] using hm

private def transition2638Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition2638Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition2638Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2638Input0) = fromList transition2638Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2638 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0384 = 1 • support0040 := by
  have hs : support0384 = fromList transition2638Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2638Chunk0]
  have hn : (transition2638Raw0 : Multiset ℕ) = 1 • (supportNumbers0040 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0040] using hm

private def transition2639Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition2639Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition2639Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2639Input0) = fromList transition2639Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2639 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0384 = 1 • support0040 := by
  have hs : support0384 = fromList transition2639Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2639Chunk0]
  have hn : (transition2639Raw0 : Multiset ℕ) = 1 • (supportNumbers0040 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0040] using hm

private def transition2640Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private def transition2640Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition2640Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2640Input0) = fromList transition2640Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2640 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0040 = 1 • support0040 := by
  have hs : support0040 = fromList transition2640Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2640Chunk0]
  have hn : (transition2640Raw0 : Multiset ℕ) = 1 • (supportNumbers0040 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0040] using hm

private def transition2641Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private def transition2641Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 137, 713, 139, 715, 141, 717, 143, 719, 200, 648, 202, 650, 204, 652, 206, 654]
private theorem transition2641Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2641Input0) = fromList transition2641Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2641 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0040 = 1 • support0041 := by
  have hs : support0040 = fromList transition2641Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2641Chunk0]
  have hn : (transition2641Raw0 : Multiset ℕ) = 1 • (supportNumbers0041 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0041] using hm

private def transition2642Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 393, 395, 397, 399, 456, 458, 460, 462, 640, 642, 644, 646, 705, 707, 709, 711, 777, 779, 781, 783, 840, 842, 844, 846]
private def transition2642Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 384, 386, 388, 390, 449, 451, 453, 455, 265, 267, 269, 271, 328, 330, 332, 334]
private theorem transition2642Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2642Input0) = fromList transition2642Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2642 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0385 = 1 • support0439 := by
  have hs : support0385 = fromList transition2642Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2642Chunk0]
  have hn : (transition2642Raw0 : Multiset ℕ) = 1 • (supportNumbers0439 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0439] using hm

private def transition2643Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 393, 395, 397, 399, 456, 458, 460, 462, 640, 642, 644, 646, 705, 707, 709, 711, 777, 779, 781, 783, 840, 842, 844, 846]
private def transition2643Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 137, 521, 139, 523, 141, 525, 143, 527, 200, 584, 202, 586, 204, 588, 206, 590, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 265, 905, 267, 907, 269, 909, 271, 911, 328, 968, 330, 970, 332, 972, 334, 974]
private theorem transition2643Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2643Input0) = fromList transition2643Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2643 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0385 = 1 • support0440 := by
  have hs : support0385 = fromList transition2643Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2643Chunk0]
  have hn : (transition2643Raw0 : Multiset ℕ) = 1 • (supportNumbers0440 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0440] using hm

private def transition2644Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 393, 395, 397, 399, 456, 458, 460, 462, 640, 642, 644, 646, 705, 707, 709, 711, 777, 779, 781, 783, 840, 842, 844, 846]
private def transition2644Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 384, 386, 388, 390, 449, 451, 453, 455, 265, 267, 269, 271, 328, 330, 332, 334]
private theorem transition2644Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2644Input0) = fromList transition2644Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2644 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0385 = 1 • support0439 := by
  have hs : support0385 = fromList transition2644Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2644Chunk0]
  have hn : (transition2644Raw0 : Multiset ℕ) = 1 • (supportNumbers0439 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0439] using hm

private def transition2645Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition2645Raw0 : List ℕ := [0, 4, 65, 69, 137, 141, 200, 204, 11, 15, 74, 78, 130, 134, 195, 199]
private theorem transition2645Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2645Input0) = fromList transition2645Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2645 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0439 = 1 • support1690 := by
  have hs : support0439 = fromList transition2645Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2645Chunk0]
  have hn : (transition2645Raw0 : Multiset ℕ) = 1 • (supportNumbers1690 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1690] using hm

private def transition2646Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition2646Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 137, 715, 141, 719, 200, 650, 204, 654, 585, 11, 589, 15, 520, 74, 524, 78, 704, 130, 708, 134, 641, 195, 645, 199]
private theorem transition2646Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2646Input0) = fromList transition2646Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2646 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0439 = 1 • support1692 := by
  have hs : support0439 = fromList transition2646Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2646Chunk0]
  have hn : (transition2646Raw0 : Multiset ℕ) = 1 • (supportNumbers1692 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1692] using hm

private def transition2647Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 393, 395, 397, 399, 456, 458, 460, 462, 640, 642, 644, 646, 705, 707, 709, 711, 777, 779, 781, 783, 840, 842, 844, 846]
private def transition2647Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 137, 681, 139, 683, 141, 685, 143, 687, 200, 744, 202, 746, 204, 748, 206, 750, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 265, 809, 267, 811, 269, 813, 271, 815, 328, 872, 330, 874, 332, 876, 334, 878]
private theorem transition2647Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2647Input0) = fromList transition2647Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2647 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0385 = 1 • support1693 := by
  have hs : support0385 = fromList transition2647Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2647Chunk0]
  have hn : (transition2647Raw0 : Multiset ℕ) = 1 • (supportNumbers1693 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1693] using hm

private def transition2648Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455, 544, 546, 548, 550, 609, 611, 613, 615, 681, 683, 685, 687, 744, 746, 748, 750, 809, 811, 813, 815, 872, 874, 876, 878, 928, 930, 932, 934, 993, 995, 997, 999]
private def transition2648Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 9, 11, 13, 15, 72, 74, 76, 78, 128, 130, 132, 134, 193, 195, 197, 199, 288, 290, 292, 294, 353, 355, 357, 359, 425, 427, 429, 431, 488, 490, 492, 494, 297, 299, 301, 303, 360, 362, 364, 366, 416, 418, 420, 422, 481, 483, 485, 487]
private theorem transition2648Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2648Input0) = fromList transition2648Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2648 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1693 = 1 • support1171 := by
  have hs : support1693 = fromList transition2648Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2648Chunk0]
  have hn : (transition2648Raw0 : Multiset ℕ) = 1 • (supportNumbers1171 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1171] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
