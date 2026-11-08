import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2132Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 768, 770, 772, 774, 776, 778, 780, 782, 833, 835, 837, 839, 841, 843, 845, 847]
private def transition2132Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335]
private theorem transition2132Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2132Input0) = fromList transition2132Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2132 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0302 = 1 • support0137 := by
  have hs : support0302 = fromList transition2132Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2132Chunk0]
  have hn : (transition2132Raw0 : Multiset ℕ) = 1 • (supportNumbers0137 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0137] using hm

private def transition2133Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 768, 770, 772, 774, 776, 778, 780, 782, 833, 835, 837, 839, 841, 843, 845, 847]
private def transition2133Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623, 128, 672, 130, 674, 132, 676, 134, 678, 136, 680, 138, 682, 140, 684, 142, 686, 193, 737, 195, 739, 197, 741, 199, 743, 201, 745, 203, 747, 205, 749, 207, 751, 384, 928, 386, 930, 388, 932, 390, 934, 392, 936, 394, 938, 396, 940, 398, 942, 449, 993, 451, 995, 453, 997, 455, 999, 457, 1001, 459, 1003, 461, 1005, 463, 1007, 256, 800, 258, 802, 260, 804, 262, 806, 264, 808, 266, 810, 268, 812, 270, 814, 321, 865, 323, 867, 325, 869, 327, 871, 329, 873, 331, 875, 333, 877, 335, 879]
private theorem transition2133Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2133Input0) = fromList transition2133Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2133 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0302 = 1 • support0930 := by
  have hs : support0302 = fromList transition2133Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2133Chunk0]
  have hn : (transition2133Raw0 : Multiset ℕ) = 1 • (supportNumbers0930 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0930] using hm

private def transition2134Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719]
private def transition2134Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private theorem transition2134Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2134Input0) = fromList transition2134Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2134 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0303 = 1 • support0301 := by
  have hs : support0303 = fromList transition2134Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2134Chunk0]
  have hn : (transition2134Raw0 : Multiset ℕ) = 1 • (supportNumbers0301 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0301] using hm

private def transition2135Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719]
private def transition2135Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 384, 768, 386, 770, 388, 772, 390, 774, 392, 776, 394, 778, 396, 780, 398, 782, 449, 833, 451, 835, 453, 837, 455, 839, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition2135Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2135Input0) = fromList transition2135Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2135 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0303 = 1 • support0302 := by
  have hs : support0303 = fromList transition2135Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2135Chunk0]
  have hn : (transition2135Raw0 : Multiset ℕ) = 1 • (supportNumbers0302 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0302] using hm

private def transition2136Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719]
private def transition2136Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private theorem transition2136Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2136Input0) = fromList transition2136Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2136 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0303 = 1 • support0301 := by
  have hs : support0303 = fromList transition2136Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2136Chunk0]
  have hn : (transition2136Raw0 : Multiset ℕ) = 1 • (supportNumbers0301 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0301] using hm

private def transition2137Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719]
private def transition2137Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623, 384, 928, 386, 930, 388, 932, 390, 934, 392, 936, 394, 938, 396, 940, 398, 942, 449, 993, 451, 995, 453, 997, 455, 999, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition2137Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2137Input0) = fromList transition2137Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2137 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0303 = 1 • support1380 := by
  have hs : support0303 = fromList transition2137Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2137Chunk0]
  have hn : (transition2137Raw0 : Multiset ℕ) = 1 • (supportNumbers1380 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1380] using hm

private def transition2138Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 520, 522, 524, 526, 585, 587, 589, 591, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition2138Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 264, 266, 268, 270, 329, 331, 333, 335, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition2138Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2138Input0) = fromList transition2138Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2138 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0304 = 1 • support0382 := by
  have hs : support0304 = fromList transition2138Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2138Chunk0]
  have hn : (transition2138Raw0 : Multiset ℕ) = 1 • (supportNumbers0382 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0382] using hm

private def transition2139Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 520, 522, 524, 526, 585, 587, 589, 591, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition2139Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 128, 512, 130, 514, 132, 516, 134, 518, 193, 577, 195, 579, 197, 581, 199, 583, 264, 904, 266, 906, 268, 908, 270, 910, 329, 969, 331, 971, 333, 973, 335, 975, 392, 776, 394, 778, 396, 780, 398, 782, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition2139Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2139Input0) = fromList transition2139Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2139 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0304 = 1 • support0383 := by
  have hs : support0304 = fromList transition2139Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2139Chunk0]
  have hn : (transition2139Raw0 : Multiset ℕ) = 1 • (supportNumbers0383 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0383] using hm

private def transition2140Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 520, 522, 524, 526, 585, 587, 589, 591, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition2140Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 264, 266, 268, 270, 329, 331, 333, 335, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition2140Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2140Input0) = fromList transition2140Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2140 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0304 = 1 • support0382 := by
  have hs : support0304 = fromList transition2140Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2140Chunk0]
  have hn : (transition2140Raw0 : Multiset ℕ) = 1 • (supportNumbers0382 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0382] using hm

private def transition2141Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 264, 266, 268, 270, 329, 331, 333, 335, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2141Raw0 : List ℕ := [0, 4, 65, 69, 128, 132, 193, 197, 10, 14, 75, 79, 138, 142, 203, 207]
private theorem transition2141Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2141Input0) = fromList transition2141Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2141 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0382 = 1 • support1562 := by
  have hs : support0382 = fromList transition2141Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2141Chunk0]
  have hn : (transition2141Raw0 : Multiset ℕ) = 1 • (supportNumbers1562 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1562] using hm

private def transition2142Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 264, 266, 268, 270, 329, 331, 333, 335, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2142Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 128, 706, 132, 710, 193, 643, 197, 647, 584, 10, 588, 14, 521, 75, 525, 79, 712, 138, 716, 142, 649, 203, 653, 207]
private theorem transition2142Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2142Input0) = fromList transition2142Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2142 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0382 = 1 • support1564 := by
  have hs : support0382 = fromList transition2142Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2142Chunk0]
  have hn : (transition2142Raw0 : Multiset ℕ) = 1 • (supportNumbers1564 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1564] using hm

private def transition2143Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 520, 522, 524, 526, 585, 587, 589, 591, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition2143Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 128, 672, 130, 674, 132, 676, 134, 678, 193, 737, 195, 739, 197, 741, 199, 743, 264, 808, 266, 810, 268, 812, 270, 814, 329, 873, 331, 875, 333, 877, 335, 879, 392, 936, 394, 938, 396, 940, 398, 942, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition2143Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2143Input0) = fromList transition2143Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2143 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0304 = 1 • support1566 := by
  have hs : support0304 = fromList transition2143Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2143Chunk0]
  have hn : (transition2143Raw0 : Multiset ℕ) = 1 • (supportNumbers1566 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1566] using hm

private def transition2144Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 264, 266, 268, 270, 329, 331, 333, 335, 392, 394, 396, 398, 457, 459, 461, 463, 544, 546, 548, 550, 609, 611, 613, 615, 672, 674, 676, 678, 737, 739, 741, 743, 808, 810, 812, 814, 873, 875, 877, 879, 936, 938, 940, 942, 1001, 1003, 1005, 1007]
private def transition2144Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 8, 10, 12, 14, 73, 75, 77, 79, 136, 138, 140, 142, 201, 203, 205, 207, 288, 290, 292, 294, 353, 355, 357, 359, 416, 418, 420, 422, 481, 483, 485, 487, 296, 298, 300, 302, 361, 363, 365, 367, 424, 426, 428, 430, 489, 491, 493, 495]
private theorem transition2144Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2144Input0) = fromList transition2144Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2144 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1566 = 1 • support0737 := by
  have hs : support1566 = fromList transition2144Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2144Chunk0]
  have hn : (transition2144Raw0 : Multiset ℕ) = 1 • (supportNumbers0737 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0737] using hm

private def transition2145Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 264, 266, 268, 270, 329, 331, 333, 335, 392, 394, 396, 398, 457, 459, 461, 463, 544, 546, 548, 550, 609, 611, 613, 615, 672, 674, 676, 678, 737, 739, 741, 743, 808, 810, 812, 814, 873, 875, 877, 879, 936, 938, 940, 942, 1001, 1003, 1005, 1007]
private def transition2145Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 128, 704, 130, 706, 132, 708, 134, 710, 193, 641, 195, 643, 197, 645, 199, 647, 8, 584, 10, 586, 12, 588, 14, 590, 73, 521, 75, 523, 77, 525, 79, 527, 136, 712, 138, 714, 140, 716, 142, 718, 201, 649, 203, 651, 205, 653, 207, 655, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 416, 992, 418, 994, 420, 996, 422, 998, 481, 929, 483, 931, 485, 933, 487, 935, 296, 872, 298, 874, 300, 876, 302, 878, 361, 809, 363, 811, 365, 813, 367, 815, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition2145Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2145Input0) = fromList transition2145Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2145 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1566 = 1 • support0739 := by
  have hs : support1566 = fromList transition2145Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2145Chunk0]
  have hn : (transition2145Raw0 : Multiset ℕ) = 1 • (supportNumbers0739 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0739] using hm

private def transition2146Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 649, 651, 653, 655, 712, 714, 716, 718]
private def transition2146Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition2146Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2146Input0) = fromList transition2146Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2146 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0305 = 1 • support0384 := by
  have hs : support0305 = fromList transition2146Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2146Chunk0]
  have hn : (transition2146Raw0 : Multiset ℕ) = 1 • (supportNumbers0384 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0384] using hm

private def transition2147Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 649, 651, 653, 655, 712, 714, 716, 718]
private def transition2147Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 393, 777, 395, 779, 397, 781, 399, 783, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition2147Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2147Input0) = fromList transition2147Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2147 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0305 = 1 • support0385 := by
  have hs : support0305 = fromList transition2147Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2147Chunk0]
  have hn : (transition2147Raw0 : Multiset ℕ) = 1 • (supportNumbers0385 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0385] using hm

private def transition2148Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 649, 651, 653, 655, 712, 714, 716, 718]
private def transition2148Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition2148Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2148Input0) = fromList transition2148Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2148 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0305 = 1 • support0384 := by
  have hs : support0305 = fromList transition2148Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2148Chunk0]
  have hn : (transition2148Raw0 : Multiset ℕ) = 1 • (supportNumbers0384 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0384] using hm

private def transition2149Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition2149Raw0 : List ℕ := [0, 4, 65, 69, 139, 143, 202, 206]
private theorem transition2149Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2149Input0) = fromList transition2149Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2149 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0384 = 1 • support1567 := by
  have hs : support0384 = fromList transition2149Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2149Chunk0]
  have hn : (transition2149Raw0 : Multiset ℕ) = 1 • (supportNumbers1567 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1567] using hm

private def transition2150Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition2150Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 713, 139, 717, 143, 648, 202, 652, 206]
private theorem transition2150Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2150Input0) = fromList transition2150Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2150 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0384 = 1 • support1569 := by
  have hs : support0384 = fromList transition2150Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2150Chunk0]
  have hn : (transition2150Raw0 : Multiset ℕ) = 1 • (supportNumbers1569 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1569] using hm

private def transition2151Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 649, 651, 653, 655, 712, 714, 716, 718]
private def transition2151Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 393, 937, 395, 939, 397, 941, 399, 943, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition2151Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2151Input0) = fromList transition2151Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2151 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0305 = 1 • support1570 := by
  have hs : support0305 = fromList transition2151Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2151Chunk0]
  have hn : (transition2151Raw0 : Multiset ℕ) = 1 • (supportNumbers1570 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1570] using hm

private def transition2152Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 393, 395, 397, 399, 456, 458, 460, 462, 544, 546, 548, 550, 609, 611, 613, 615, 937, 939, 941, 943, 1000, 1002, 1004, 1006]
private def transition2152Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 288, 290, 292, 294, 353, 355, 357, 359, 425, 427, 429, 431, 488, 490, 492, 494]
private theorem transition2152Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2152Input0) = fromList transition2152Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2152 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1570 = 1 • support1571 := by
  have hs : support1570 = fromList transition2152Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2152Chunk0]
  have hn : (transition2152Raw0 : Multiset ℕ) = 1 • (supportNumbers1571 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1571] using hm

private def transition2153Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 393, 395, 397, 399, 456, 458, 460, 462, 544, 546, 548, 550, 609, 611, 613, 615, 937, 939, 941, 943, 1000, 1002, 1004, 1006]
private def transition2153Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 137, 713, 139, 715, 141, 717, 143, 719, 200, 648, 202, 650, 204, 652, 206, 654, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition2153Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2153Input0) = fromList transition2153Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2153 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1570 = 1 • support1573 := by
  have hs : support1570 = fromList transition2153Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2153Chunk0]
  have hn : (transition2153Raw0 : Multiset ℕ) = 1 • (supportNumbers1573 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1573] using hm

private def transition2154Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718]
private def transition2154Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private theorem transition2154Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2154Input0) = fromList transition2154Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2154 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0306 = 1 • support0218 := by
  have hs : support0306 = fromList transition2154Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2154Chunk0]
  have hn : (transition2154Raw0 : Multiset ℕ) = 1 • (supportNumbers0218 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0218] using hm

private def transition2155Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718]
private def transition2155Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718, 384, 768, 386, 770, 388, 772, 390, 774, 393, 777, 395, 779, 397, 781, 399, 783, 449, 833, 451, 835, 453, 837, 455, 839, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition2155Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2155Input0) = fromList transition2155Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2155 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0306 = 1 • support0219 := by
  have hs : support0306 = fromList transition2155Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2155Chunk0]
  have hn : (transition2155Raw0 : Multiset ℕ) = 1 • (supportNumbers0219 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0219] using hm

private def transition2156Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718]
private def transition2156Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private theorem transition2156Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2156Input0) = fromList transition2156Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2156 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0306 = 1 • support0218 := by
  have hs : support0306 = fromList transition2156Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2156Chunk0]
  have hn : (transition2156Raw0 : Multiset ℕ) = 1 • (supportNumbers0218 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0218] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
