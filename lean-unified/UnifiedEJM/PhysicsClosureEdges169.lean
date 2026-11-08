import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2936Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 256, 258, 260, 262, 321, 323, 325, 327, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2936Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition2936Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2936Input0) = fromList transition2936Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2936 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0437 = 1 • support0076 := by
  have hs : support0437 = fromList transition2936Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2936Chunk0]
  have hn : (transition2936Raw0 : Multiset ℕ) = 1 • (supportNumbers0076 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0076] using hm

private def transition2937Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 256, 258, 260, 262, 321, 323, 325, 327, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2937Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 680, 682, 684, 686, 745, 747, 749, 751, 544, 546, 548, 550, 609, 611, 613, 615, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition2937Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2937Input0) = fromList transition2937Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2937 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0437 = 1 • support0918 := by
  have hs : support0437 = fromList transition2937Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2937Chunk0]
  have hn : (transition2937Raw0 : Multiset ℕ) = 1 • (supportNumbers0918 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0918] using hm

private def transition2938Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 256, 258, 260, 262, 321, 323, 325, 327, 392, 394, 396, 398, 457, 459, 461, 463, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition2938Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition2938Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2938Input0) = fromList transition2938Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2938 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0438 = 2 • support0077 := by
  have hs : support0438 = fromList transition2938Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2938Chunk0]
  have hn : (transition2938Raw0 : Multiset ℕ) = 2 • (supportNumbers0077 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0077] using hm

private def transition2939Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 256, 258, 260, 262, 321, 323, 325, 327, 392, 394, 396, 398, 457, 459, 461, 463, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition2939Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 136, 520, 138, 522, 140, 524, 142, 526, 201, 585, 203, 587, 205, 589, 207, 591, 0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 136, 520, 138, 522, 140, 524, 142, 526, 201, 585, 203, 587, 205, 589, 207, 591, 264, 904, 266, 906, 268, 908, 270, 910, 329, 969, 331, 971, 333, 973, 335, 975, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 264, 904, 266, 906, 268, 908, 270, 910, 329, 969, 331, 971, 333, 973, 335, 975, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839]
private theorem transition2939Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2939Input0) = fromList transition2939Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2939 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0438 = 2 • support0078 := by
  have hs : support0438 = fromList transition2939Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2939Chunk0]
  have hn : (transition2939Raw0 : Multiset ℕ) = 2 • (supportNumbers0078 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0078] using hm

private def transition2940Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 256, 258, 260, 262, 321, 323, 325, 327, 392, 394, 396, 398, 457, 459, 461, 463, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition2940Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition2940Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2940Input0) = fromList transition2940Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2940 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0438 = 2 • support0077 := by
  have hs : support0438 = fromList transition2940Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2940Chunk0]
  have hn : (transition2940Raw0 : Multiset ℕ) = 2 • (supportNumbers0077 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0077] using hm

private def transition2941Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 256, 258, 260, 262, 321, 323, 325, 327, 392, 394, 396, 398, 457, 459, 461, 463, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition2941Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 136, 680, 138, 682, 140, 684, 142, 686, 201, 745, 203, 747, 205, 749, 207, 751, 0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 136, 680, 138, 682, 140, 684, 142, 686, 201, 745, 203, 747, 205, 749, 207, 751, 264, 808, 266, 810, 268, 812, 270, 814, 329, 873, 331, 875, 333, 877, 335, 879, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 264, 808, 266, 810, 268, 812, 270, 814, 329, 873, 331, 875, 333, 877, 335, 879, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999]
private theorem transition2941Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2941Input0) = fromList transition2941Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2941 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0438 = 2 • support0736 := by
  have hs : support0438 = fromList transition2941Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2941Chunk0]
  have hn : (transition2941Raw0 : Multiset ℕ) = 2 • (supportNumbers0736 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0736] using hm

private def transition2942Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private def transition2942Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private theorem transition2942Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2942Input0) = fromList transition2942Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2942 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0215 = 1 • support0215 := by
  have hs : support0215 = fromList transition2942Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2942Chunk0]
  have hn : (transition2942Raw0 : Multiset ℕ) = 1 • (supportNumbers0215 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0215] using hm

private def transition2943Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private def transition2943Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 128, 512, 130, 514, 132, 516, 134, 518, 136, 520, 138, 522, 140, 524, 142, 526, 193, 577, 195, 579, 197, 581, 199, 583, 201, 585, 203, 587, 205, 589, 207, 591]
private theorem transition2943Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2943Input0) = fromList transition2943Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2943 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0215 = 1 • support0216 := by
  have hs : support0215 = fromList transition2943Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2943Chunk0]
  have hn : (transition2943Raw0 : Multiset ℕ) = 1 • (supportNumbers0216 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0216] using hm

private def transition2944Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private def transition2944Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private theorem transition2944Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2944Input0) = fromList transition2944Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2944 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0215 = 1 • support0215 := by
  have hs : support0215 = fromList transition2944Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2944Chunk0]
  have hn : (transition2944Raw0 : Multiset ℕ) = 1 • (supportNumbers0215 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0215] using hm

private def transition2945Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private def transition2945Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623, 128, 672, 130, 674, 132, 676, 134, 678, 136, 680, 138, 682, 140, 684, 142, 686, 193, 737, 195, 739, 197, 741, 199, 743, 201, 745, 203, 747, 205, 749, 207, 751]
private theorem transition2945Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2945Input0) = fromList transition2945Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2945 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0215 = 1 • support1162 := by
  have hs : support0215 = fromList transition2945Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2945Chunk0]
  have hn : (transition2945Raw0 : Multiset ℕ) = 1 • (supportNumbers1162 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1162] using hm

private def transition2946Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private def transition2946Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition2946Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2946Input0) = fromList transition2946Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2946 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0040 = 1 • support0040 := by
  have hs : support0040 = fromList transition2946Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2946Chunk0]
  have hn : (transition2946Raw0 : Multiset ℕ) = 1 • (supportNumbers0040 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0040] using hm

private def transition2947Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private def transition2947Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 137, 521, 139, 523, 141, 525, 143, 527, 200, 584, 202, 586, 204, 588, 206, 590]
private theorem transition2947Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2947Input0) = fromList transition2947Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2947 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0040 = 1 • support0441 := by
  have hs : support0040 = fromList transition2947Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2947Chunk0]
  have hn : (transition2947Raw0 : Multiset ℕ) = 1 • (supportNumbers0441 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0441] using hm

private def transition2948Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private def transition2948Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition2948Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2948Input0) = fromList transition2948Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2948 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0040 = 1 • support0040 := by
  have hs : support0040 = fromList transition2948Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2948Chunk0]
  have hn : (transition2948Raw0 : Multiset ℕ) = 1 • (supportNumbers0040 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0040] using hm

private def transition2949Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private def transition2949Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 137, 681, 139, 683, 141, 685, 143, 687, 200, 744, 202, 746, 204, 748, 206, 750]
private theorem transition2949Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2949Input0) = fromList transition2949Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2949 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0040 = 1 • support1694 := by
  have hs : support0040 = fromList transition2949Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2949Chunk0]
  have hn : (transition2949Raw0 : Multiset ℕ) = 1 • (supportNumbers1694 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1694] using hm

private def transition2950Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition2950Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 9, 11, 13, 15, 72, 74, 76, 78]
private theorem transition2950Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2950Input0) = fromList transition2950Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2950 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0439 = 1 • support0217 := by
  have hs : support0439 = fromList transition2950Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2950Chunk0]
  have hn : (transition2950Raw0 : Multiset ℕ) = 1 • (supportNumbers0217 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0217] using hm

private def transition2951Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition2951Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 521, 523, 525, 527, 584, 586, 588, 590, 9, 11, 13, 15, 72, 74, 76, 78, 512, 514, 516, 518, 577, 579, 581, 583]
private theorem transition2951Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2951Input0) = fromList transition2951Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2951 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0439 = 1 • support0463 := by
  have hs : support0439 = fromList transition2951Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2951Chunk0]
  have hn : (transition2951Raw0 : Multiset ℕ) = 1 • (supportNumbers0463 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0463] using hm

private def transition2952Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition2952Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 9, 11, 13, 15, 72, 74, 76, 78]
private theorem transition2952Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2952Input0) = fromList transition2952Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2952 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0439 = 1 • support0217 := by
  have hs : support0439 = fromList transition2952Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2952Chunk0]
  have hn : (transition2952Raw0 : Multiset ℕ) = 1 • (supportNumbers0217 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0217] using hm

private def transition2953Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition2953Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 681, 683, 685, 687, 744, 746, 748, 750, 9, 11, 13, 15, 72, 74, 76, 78, 672, 674, 676, 678, 737, 739, 741, 743]
private theorem transition2953Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2953Input0) = fromList transition2953Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2953 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0439 = 1 • support1754 := by
  have hs : support0439 = fromList transition2953Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2953Chunk0]
  have hn : (transition2953Raw0 : Multiset ℕ) = 1 • (supportNumbers1754 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1754] using hm

private def transition2954Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 672, 674, 676, 678, 681, 683, 685, 687, 737, 739, 741, 743, 744, 746, 748, 750]
private def transition2954Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 416, 418, 420, 422, 425, 427, 429, 431, 481, 483, 485, 487, 488, 490, 492, 494]
private theorem transition2954Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2954Input0) = fromList transition2954Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2954 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1754 = 1 • support1755 := by
  have hs : support1754 = fromList transition2954Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2954Chunk0]
  have hn : (transition2954Raw0 : Multiset ℕ) = 1 • (supportNumbers1755 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1755] using hm

private def transition2955Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 672, 674, 676, 678, 681, 683, 685, 687, 737, 739, 741, 743, 744, 746, 748, 750]
private def transition2955Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 416, 992, 418, 994, 420, 996, 422, 998, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 481, 929, 483, 931, 485, 933, 487, 935, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition2955Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2955Input0) = fromList transition2955Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2955 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1754 = 1 • support1757 := by
  have hs : support1754 = fromList transition2955Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2955Chunk0]
  have hn : (transition2955Raw0 : Multiset ℕ) = 1 • (supportNumbers1757 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1757] using hm

private def transition2956Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition2956Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 9, 11, 13, 15, 72, 74, 76, 78, 128, 130, 132, 134, 193, 195, 197, 199, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455, 256, 258, 260, 262, 321, 323, 325, 327, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition2956Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2956Input0) = fromList transition2956Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2956 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0440 = 1 • support0308 := by
  have hs : support0440 = fromList transition2956Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2956Chunk0]
  have hn : (transition2956Raw0 : Multiset ℕ) = 1 • (supportNumbers0308 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0308] using hm

private def transition2957Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition2957Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 137, 521, 139, 523, 141, 525, 143, 527, 200, 584, 202, 586, 204, 588, 206, 590, 9, 649, 11, 651, 13, 653, 15, 655, 72, 712, 74, 714, 76, 716, 78, 718, 128, 512, 130, 514, 132, 516, 134, 518, 193, 577, 195, 579, 197, 581, 199, 583, 265, 905, 267, 907, 269, 909, 271, 911, 328, 968, 330, 970, 332, 972, 334, 974, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 256, 896, 258, 898, 260, 900, 262, 902, 321, 961, 323, 963, 325, 965, 327, 967, 393, 777, 395, 779, 397, 781, 399, 783, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition2957Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2957Input0) = fromList transition2957Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2957 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0440 = 1 • support0309 := by
  have hs : support0440 = fromList transition2957Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2957Chunk0]
  have hn : (transition2957Raw0 : Multiset ℕ) = 1 • (supportNumbers0309 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0309] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
