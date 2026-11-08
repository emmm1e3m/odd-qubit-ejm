import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2175Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition2175Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718, 128, 512, 130, 514, 132, 516, 134, 518, 137, 521, 139, 523, 141, 525, 143, 527, 193, 577, 195, 579, 197, 581, 199, 583, 200, 584, 202, 586, 204, 588, 206, 590, 0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718, 128, 512, 130, 514, 132, 516, 134, 518, 137, 521, 139, 523, 141, 525, 143, 527, 193, 577, 195, 579, 197, 581, 199, 583, 200, 584, 202, 586, 204, 588, 206, 590]
private theorem transition2175Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2175Input0) = fromList transition2175Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2175Input1 : List ℕ := [512, 514, 516, 518, 521, 523, 525, 527, 577, 579, 581, 583, 584, 586, 588, 590, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 768, 770, 772, 774, 777, 779, 781, 783, 833, 835, 837, 839, 840, 842, 844, 846, 896, 898, 900, 902, 905, 907, 909, 911, 961, 963, 965, 967, 968, 970, 972, 974]
private def transition2175Raw1 : List ℕ := [256, 896, 258, 898, 260, 900, 262, 902, 265, 905, 267, 907, 269, 909, 271, 911, 321, 961, 323, 963, 325, 965, 327, 967, 328, 968, 330, 970, 332, 972, 334, 974, 384, 768, 386, 770, 388, 772, 390, 774, 393, 777, 395, 779, 397, 781, 399, 783, 449, 833, 451, 835, 453, 837, 455, 839, 456, 840, 458, 842, 460, 844, 462, 846, 256, 896, 258, 898, 260, 900, 262, 902, 265, 905, 267, 907, 269, 909, 271, 911, 321, 961, 323, 963, 325, 965, 327, 967, 328, 968, 330, 970, 332, 972, 334, 974, 384, 768, 386, 770, 388, 772, 390, 774, 393, 777, 395, 779, 397, 781, 399, 783, 449, 833, 451, 835, 453, 837, 455, 839, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition2175Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2175Input1) = fromList transition2175Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2175 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0309 = 2 • support0309 := by
  have hs : support0309 = fromList transition2175Input0 + fromList transition2175Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2175Chunk0, transition2175Chunk1]
  have hn : (transition2175Raw0 : Multiset ℕ) + (transition2175Raw1 : Multiset ℕ) = 2 • (supportNumbers0309 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0309] using hm

private def transition2176Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition2176Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private theorem transition2176Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2176Input0) = fromList transition2176Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2176Input1 : List ℕ := [512, 514, 516, 518, 521, 523, 525, 527, 577, 579, 581, 583, 584, 586, 588, 590, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 768, 770, 772, 774, 777, 779, 781, 783, 833, 835, 837, 839, 840, 842, 844, 846, 896, 898, 900, 902, 905, 907, 909, 911, 961, 963, 965, 967, 968, 970, 972, 974]
private def transition2176Raw1 : List ℕ := [256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private theorem transition2176Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2176Input1) = fromList transition2176Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2176 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0309 = 2 • support0308 := by
  have hs : support0309 = fromList transition2176Input0 + fromList transition2176Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2176Chunk0, transition2176Chunk1]
  have hn : (transition2176Raw0 : Multiset ℕ) + (transition2176Raw1 : Multiset ℕ) = 2 • (supportNumbers0308 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0308] using hm

private def transition2177Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition2177Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 9, 553, 11, 555, 13, 557, 15, 559, 65, 609, 67, 611, 69, 613, 71, 615, 72, 616, 74, 618, 76, 620, 78, 622, 128, 672, 130, 674, 132, 676, 134, 678, 137, 681, 139, 683, 141, 685, 143, 687, 193, 737, 195, 739, 197, 741, 199, 743, 200, 744, 202, 746, 204, 748, 206, 750, 0, 544, 2, 546, 4, 548, 6, 550, 9, 553, 11, 555, 13, 557, 15, 559, 65, 609, 67, 611, 69, 613, 71, 615, 72, 616, 74, 618, 76, 620, 78, 622, 128, 672, 130, 674, 132, 676, 134, 678, 137, 681, 139, 683, 141, 685, 143, 687, 193, 737, 195, 739, 197, 741, 199, 743, 200, 744, 202, 746, 204, 748, 206, 750]
private theorem transition2177Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2177Input0) = fromList transition2177Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2177Input1 : List ℕ := [512, 514, 516, 518, 521, 523, 525, 527, 577, 579, 581, 583, 584, 586, 588, 590, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 768, 770, 772, 774, 777, 779, 781, 783, 833, 835, 837, 839, 840, 842, 844, 846, 896, 898, 900, 902, 905, 907, 909, 911, 961, 963, 965, 967, 968, 970, 972, 974]
private def transition2177Raw1 : List ℕ := [256, 800, 258, 802, 260, 804, 262, 806, 265, 809, 267, 811, 269, 813, 271, 815, 321, 865, 323, 867, 325, 869, 327, 871, 328, 872, 330, 874, 332, 876, 334, 878, 384, 928, 386, 930, 388, 932, 390, 934, 393, 937, 395, 939, 397, 941, 399, 943, 449, 993, 451, 995, 453, 997, 455, 999, 456, 1000, 458, 1002, 460, 1004, 462, 1006, 256, 800, 258, 802, 260, 804, 262, 806, 265, 809, 267, 811, 269, 813, 271, 815, 321, 865, 323, 867, 325, 869, 327, 871, 328, 872, 330, 874, 332, 876, 334, 878, 384, 928, 386, 930, 388, 932, 390, 934, 393, 937, 395, 939, 397, 941, 399, 943, 449, 993, 451, 995, 453, 997, 455, 999, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition2177Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2177Input1) = fromList transition2177Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2177 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0309 = 2 • support1397 := by
  have hs : support0309 = fromList transition2177Input0 + fromList transition2177Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2177Chunk0, transition2177Chunk1]
  have hn : (transition2177Raw0 : Multiset ℕ) + (transition2177Raw1 : Multiset ℕ) = 2 • (supportNumbers1397 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1397] using hm

private def transition2178Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591]
private def transition2178Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335]
private theorem transition2178Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2178Input0) = fromList transition2178Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2178 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0310 = 1 • support0390 := by
  have hs : support0310 = fromList transition2178Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2178Chunk0]
  have hn : (transition2178Raw0 : Multiset ℕ) = 1 • (supportNumbers0390 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0390] using hm

private def transition2179Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591]
private def transition2179Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718, 257, 897, 259, 899, 261, 901, 263, 903, 264, 904, 266, 906, 268, 908, 270, 910, 320, 960, 322, 962, 324, 964, 326, 966, 329, 969, 331, 971, 333, 973, 335, 975]
private theorem transition2179Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2179Input0) = fromList transition2179Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2179 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0310 = 1 • support0391 := by
  have hs : support0310 = fromList transition2179Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2179Chunk0]
  have hn : (transition2179Raw0 : Multiset ℕ) = 1 • (supportNumbers0391 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0391] using hm

private def transition2180Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591]
private def transition2180Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335]
private theorem transition2180Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2180Input0) = fromList transition2180Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2180 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0310 = 1 • support0390 := by
  have hs : support0310 = fromList transition2180Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2180Chunk0]
  have hn : (transition2180Raw0 : Multiset ℕ) = 1 • (supportNumbers0390 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0390] using hm

private def transition2181Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335]
private def transition2181Raw0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 3, 7, 10, 14, 66, 70, 75, 79]
private theorem transition2181Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2181Input0) = fromList transition2181Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2181 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0390 = 1 • support1151 := by
  have hs : support0390 = fromList transition2181Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2181Chunk0]
  have hn : (transition2181Raw0 : Multiset ℕ) = 1 • (supportNumbers1151 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1151] using hm

private def transition2182Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335]
private def transition2182Raw0 : List ℕ := [0, 578, 4, 582, 9, 587, 13, 591, 65, 515, 69, 519, 72, 522, 76, 526, 577, 3, 581, 7, 584, 10, 588, 14, 512, 66, 516, 70, 521, 75, 525, 79]
private theorem transition2182Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2182Input0) = fromList transition2182Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2182 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0390 = 1 • support1580 := by
  have hs : support0390 = fromList transition2182Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2182Chunk0]
  have hn : (transition2182Raw0 : Multiset ℕ) = 1 • (supportNumbers1580 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1580] using hm

private def transition2183Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591]
private def transition2183Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 9, 553, 11, 555, 13, 557, 15, 559, 65, 609, 67, 611, 69, 613, 71, 615, 72, 616, 74, 618, 76, 620, 78, 622, 257, 801, 259, 803, 261, 805, 263, 807, 264, 808, 266, 810, 268, 812, 270, 814, 320, 864, 322, 866, 324, 868, 326, 870, 329, 873, 331, 875, 333, 877, 335, 879]
private theorem transition2183Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2183Input0) = fromList transition2183Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2183 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0310 = 1 • support1581 := by
  have hs : support0310 = fromList transition2183Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2183Chunk0]
  have hn : (transition2183Raw0 : Multiset ℕ) = 1 • (supportNumbers1581 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1581] using hm

private def transition2184Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622, 801, 803, 805, 807, 808, 810, 812, 814, 864, 866, 868, 870, 873, 875, 877, 879]
private def transition2184Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 1, 3, 5, 7, 8, 10, 12, 14, 64, 66, 68, 70, 73, 75, 77, 79, 288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366, 289, 291, 293, 295, 296, 298, 300, 302, 352, 354, 356, 358, 361, 363, 365, 367]
private theorem transition2184Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2184Input0) = fromList transition2184Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2184 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1581 = 1 • support1223 := by
  have hs : support1581 = fromList transition2184Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2184Chunk0]
  have hn : (transition2184Raw0 : Multiset ℕ) = 1 • (supportNumbers1223 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1223] using hm

private def transition2185Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622, 801, 803, 805, 807, 808, 810, 812, 814, 864, 866, 868, 870, 873, 875, 877, 879]
private def transition2185Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 1, 577, 3, 579, 5, 581, 7, 583, 8, 584, 10, 586, 12, 588, 14, 590, 64, 512, 66, 514, 68, 516, 70, 518, 73, 521, 75, 523, 77, 525, 79, 527, 288, 864, 290, 866, 292, 868, 294, 870, 297, 873, 299, 875, 301, 877, 303, 879, 353, 801, 355, 803, 357, 805, 359, 807, 360, 808, 362, 810, 364, 812, 366, 814, 289, 865, 291, 867, 293, 869, 295, 871, 296, 872, 298, 874, 300, 876, 302, 878, 352, 800, 354, 802, 356, 804, 358, 806, 361, 809, 363, 811, 365, 813, 367, 815]
private theorem transition2185Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2185Input0) = fromList transition2185Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2185 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1581 = 1 • support1225 := by
  have hs : support1581 = fromList transition2185Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2185Chunk0]
  have hn : (transition2185Raw0 : Multiset ℕ) = 1 • (supportNumbers1225 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1225] using hm

private def transition2186Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 648, 649, 650, 651, 652, 653, 654, 655, 712, 713, 714, 715, 716, 717, 718, 719]
private def transition2186Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private theorem transition2186Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2186Input0) = fromList transition2186Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2186 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0311 = 1 • support0392 := by
  have hs : support0311 = fromList transition2186Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2186Chunk0]
  have hn : (transition2186Raw0 : Multiset ℕ) = 1 • (supportNumbers0392 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0392] using hm

private def transition2187Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 648, 649, 650, 651, 652, 653, 654, 655, 712, 713, 714, 715, 716, 717, 718, 719]
private def transition2187Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 392, 776, 393, 777, 394, 778, 395, 779, 396, 780, 397, 781, 398, 782, 399, 783, 456, 840, 457, 841, 458, 842, 459, 843, 460, 844, 461, 845, 462, 846, 463, 847]
private theorem transition2187Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2187Input0) = fromList transition2187Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2187 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0311 = 1 • support0393 := by
  have hs : support0311 = fromList transition2187Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2187Chunk0]
  have hn : (transition2187Raw0 : Multiset ℕ) = 1 • (supportNumbers0393 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0393] using hm

private def transition2188Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 648, 649, 650, 651, 652, 653, 654, 655, 712, 713, 714, 715, 716, 717, 718, 719]
private def transition2188Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private theorem transition2188Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2188Input0) = fromList transition2188Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2188 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0311 = 1 • support0392 := by
  have hs : support0311 = fromList transition2188Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2188Chunk0]
  have hn : (transition2188Raw0 : Multiset ℕ) = 1 • (supportNumbers0392 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0392] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
