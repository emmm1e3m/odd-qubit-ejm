import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2157Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718]
private def transition2157Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 9, 553, 11, 555, 13, 557, 15, 559, 65, 609, 67, 611, 69, 613, 71, 615, 72, 616, 74, 618, 76, 620, 78, 622, 384, 928, 386, 930, 388, 932, 390, 934, 393, 937, 395, 939, 397, 941, 399, 943, 449, 993, 451, 995, 453, 997, 455, 999, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition2157Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2157Input0) = fromList transition2157Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2157 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0306 = 1 • support1170 := by
  have hs : support0306 = fromList transition2157Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2157Chunk0]
  have hn : (transition2157Raw0 : Multiset ℕ) = 1 • (supportNumbers1170 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1170] using hm

private def transition2158Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 512, 514, 516, 518, 577, 579, 581, 583, 649, 651, 653, 655, 712, 714, 716, 718]
private def transition2158Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 256, 258, 260, 262, 321, 323, 325, 327, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition2158Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2158Input0) = fromList transition2158Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2158 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0307 = 1 • support0386 := by
  have hs : support0307 = fromList transition2158Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2158Chunk0]
  have hn : (transition2158Raw0 : Multiset ℕ) = 1 • (supportNumbers0386 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0386] using hm

private def transition2159Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 512, 514, 516, 518, 577, 579, 581, 583, 649, 651, 653, 655, 712, 714, 716, 718]
private def transition2159Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 137, 521, 139, 523, 141, 525, 143, 527, 200, 584, 202, 586, 204, 588, 206, 590, 256, 896, 258, 898, 260, 900, 262, 902, 321, 961, 323, 963, 325, 965, 327, 967, 393, 777, 395, 779, 397, 781, 399, 783, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition2159Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2159Input0) = fromList transition2159Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2159 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0307 = 1 • support0387 := by
  have hs : support0307 = fromList transition2159Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2159Chunk0]
  have hn : (transition2159Raw0 : Multiset ℕ) = 1 • (supportNumbers0387 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0387] using hm

private def transition2160Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 512, 514, 516, 518, 577, 579, 581, 583, 649, 651, 653, 655, 712, 714, 716, 718]
private def transition2160Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 256, 258, 260, 262, 321, 323, 325, 327, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition2160Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2160Input0) = fromList transition2160Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2160 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0307 = 1 • support0386 := by
  have hs : support0307 = fromList transition2160Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2160Chunk0]
  have hn : (transition2160Raw0 : Multiset ℕ) = 1 • (supportNumbers0386 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0386] using hm

private def transition2161Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 256, 258, 260, 262, 321, 323, 325, 327, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition2161Raw0 : List ℕ := [0, 4, 65, 69, 137, 141, 200, 204, 2, 6, 67, 71, 139, 143, 202, 206]
private theorem transition2161Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2161Input0) = fromList transition2161Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2161 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0386 = 1 • support0040 := by
  have hs : support0386 = fromList transition2161Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2161Chunk0]
  have hn : (transition2161Raw0 : Multiset ℕ) = 1 • (supportNumbers0040 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0040] using hm

private def transition2162Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 256, 258, 260, 262, 321, 323, 325, 327, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition2162Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 137, 715, 141, 719, 200, 650, 204, 654, 576, 2, 580, 6, 513, 67, 517, 71, 713, 139, 717, 143, 648, 202, 652, 206]
private theorem transition2162Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2162Input0) = fromList transition2162Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2162 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0386 = 1 • support0041 := by
  have hs : support0386 = fromList transition2162Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2162Chunk0]
  have hn : (transition2162Raw0 : Multiset ℕ) = 1 • (supportNumbers0041 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0041] using hm

private def transition2163Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 512, 514, 516, 518, 577, 579, 581, 583, 649, 651, 653, 655, 712, 714, 716, 718]
private def transition2163Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 137, 681, 139, 683, 141, 685, 143, 687, 200, 744, 202, 746, 204, 748, 206, 750, 256, 800, 258, 802, 260, 804, 262, 806, 321, 865, 323, 867, 325, 869, 327, 871, 393, 937, 395, 939, 397, 941, 399, 943, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition2163Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2163Input0) = fromList transition2163Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2163 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0307 = 1 • support1575 := by
  have hs : support0307 = fromList transition2163Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2163Chunk0]
  have hn : (transition2163Raw0 : Multiset ℕ) = 1 • (supportNumbers1575 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1575] using hm

private def transition2164Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 256, 258, 260, 262, 321, 323, 325, 327, 393, 395, 397, 399, 456, 458, 460, 462, 544, 546, 548, 550, 609, 611, 613, 615, 681, 683, 685, 687, 744, 746, 748, 750, 800, 802, 804, 806, 865, 867, 869, 871, 937, 939, 941, 943, 1000, 1002, 1004, 1006]
private def transition2164Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 288, 290, 292, 294, 353, 355, 357, 359, 425, 427, 429, 431, 488, 490, 492, 494, 288, 290, 292, 294, 353, 355, 357, 359, 425, 427, 429, 431, 488, 490, 492, 494]
private theorem transition2164Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2164Input0) = fromList transition2164Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2164 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1575 = 2 • support1571 := by
  have hs : support1575 = fromList transition2164Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2164Chunk0]
  have hn : (transition2164Raw0 : Multiset ℕ) = 2 • (supportNumbers1571 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1571] using hm

private def transition2165Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 256, 258, 260, 262, 321, 323, 325, 327, 393, 395, 397, 399, 456, 458, 460, 462, 544, 546, 548, 550, 609, 611, 613, 615, 681, 683, 685, 687, 744, 746, 748, 750, 800, 802, 804, 806, 865, 867, 869, 871, 937, 939, 941, 943, 1000, 1002, 1004, 1006]
private def transition2165Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 137, 713, 139, 715, 141, 717, 143, 719, 200, 648, 202, 650, 204, 652, 206, 654, 0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 137, 713, 139, 715, 141, 717, 143, 719, 200, 648, 202, 650, 204, 652, 206, 654, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 488, 936, 490, 938, 492, 940, 494, 942, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition2165Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2165Input0) = fromList transition2165Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2165 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1575 = 2 • support1573 := by
  have hs : support1575 = fromList transition2165Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2165Chunk0]
  have hn : (transition2165Raw0 : Multiset ℕ) = 2 • (supportNumbers1573 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1573] using hm

private def transition2166Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition2166Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 9, 11, 13, 15, 72, 74, 76, 78, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition2166Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2166Input0) = fromList transition2166Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2166 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0308 = 1 • support0388 := by
  have hs : support0308 = fromList transition2166Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2166Chunk0]
  have hn : (transition2166Raw0 : Multiset ℕ) = 1 • (supportNumbers0388 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0388] using hm

private def transition2167Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition2167Raw0 : List ℕ := [0, 2, 4, 6, 649, 651, 653, 655, 65, 67, 69, 71, 712, 714, 716, 718, 128, 130, 132, 134, 521, 523, 525, 527, 193, 195, 197, 199, 584, 586, 588, 590, 640, 642, 644, 646, 9, 11, 13, 15, 705, 707, 709, 711, 72, 74, 76, 78, 512, 514, 516, 518, 137, 139, 141, 143, 577, 579, 581, 583, 200, 202, 204, 206]
private theorem transition2167Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2167Input0) = fromList transition2167Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2167 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0308 = 1 • support0389 := by
  have hs : support0308 = fromList transition2167Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2167Chunk0]
  have hn : (transition2167Raw0 : Multiset ℕ) = 1 • (supportNumbers0389 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0389] using hm

private def transition2168Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition2168Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 9, 11, 13, 15, 72, 74, 76, 78, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition2168Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2168Input0) = fromList transition2168Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2168 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0308 = 1 • support0388 := by
  have hs : support0308 = fromList transition2168Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2168Chunk0]
  have hn : (transition2168Raw0 : Multiset ℕ) = 1 • (supportNumbers0388 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0388] using hm

private def transition2169Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private def transition2169Raw0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 128, 132, 137, 141, 193, 197, 200, 204]
private theorem transition2169Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2169Input0) = fromList transition2169Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2169 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0388 = 1 • support1576 := by
  have hs : support0388 = fromList transition2169Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2169Chunk0]
  have hn : (transition2169Raw0 : Multiset ℕ) = 1 • (supportNumbers1576 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1576] using hm

private def transition2170Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private def transition2170Raw0 : List ℕ := [0, 578, 4, 582, 9, 587, 13, 591, 65, 515, 69, 519, 72, 522, 76, 526, 128, 706, 132, 710, 137, 715, 141, 719, 193, 643, 197, 647, 200, 650, 204, 654]
private theorem transition2170Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2170Input0) = fromList transition2170Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2170 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0388 = 1 • support1578 := by
  have hs : support0388 = fromList transition2170Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2170Chunk0]
  have hn : (transition2170Raw0 : Multiset ℕ) = 1 • (supportNumbers1578 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1578] using hm

private def transition2171Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition2171Raw0 : List ℕ := [0, 2, 4, 6, 553, 555, 557, 559, 65, 67, 69, 71, 616, 618, 620, 622, 128, 130, 132, 134, 681, 683, 685, 687, 193, 195, 197, 199, 744, 746, 748, 750, 544, 546, 548, 550, 9, 11, 13, 15, 609, 611, 613, 615, 72, 74, 76, 78, 672, 674, 676, 678, 137, 139, 141, 143, 737, 739, 741, 743, 200, 202, 204, 206]
private theorem transition2171Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2171Input0) = fromList transition2171Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2171 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0308 = 1 • support1579 := by
  have hs : support0308 = fromList transition2171Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2171Chunk0]
  have hn : (transition2171Raw0 : Multiset ℕ) = 1 • (supportNumbers1579 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1579] using hm

private def transition2172Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622, 672, 674, 676, 678, 681, 683, 685, 687, 737, 739, 741, 743, 744, 746, 748, 750]
private def transition2172Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366, 416, 418, 420, 422, 425, 427, 429, 431, 481, 483, 485, 487, 488, 490, 492, 494]
private theorem transition2172Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2172Input0) = fromList transition2172Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2172 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1579 = 1 • support1171 := by
  have hs : support1579 = fromList transition2172Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2172Chunk0]
  have hn : (transition2172Raw0 : Multiset ℕ) = 1 • (supportNumbers1171 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1171] using hm

private def transition2173Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622, 672, 674, 676, 678, 681, 683, 685, 687, 737, 739, 741, 743, 744, 746, 748, 750]
private def transition2173Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 128, 704, 130, 706, 132, 708, 134, 710, 137, 713, 139, 715, 141, 717, 143, 719, 193, 641, 195, 643, 197, 645, 199, 647, 200, 648, 202, 650, 204, 652, 206, 654, 288, 864, 290, 866, 292, 868, 294, 870, 297, 873, 299, 875, 301, 877, 303, 879, 353, 801, 355, 803, 357, 805, 359, 807, 360, 808, 362, 810, 364, 812, 366, 814, 416, 992, 418, 994, 420, 996, 422, 998, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 481, 929, 483, 931, 485, 933, 487, 935, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition2173Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2173Input0) = fromList transition2173Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2173 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1579 = 1 • support1173 := by
  have hs : support1579 = fromList transition2173Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2173Chunk0]
  have hn : (transition2173Raw0 : Multiset ℕ) = 1 • (supportNumbers1173 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1173] using hm

private def transition2174Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition2174Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private theorem transition2174Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2174Input0) = fromList transition2174Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2174Input1 : List ℕ := [512, 514, 516, 518, 521, 523, 525, 527, 577, 579, 581, 583, 584, 586, 588, 590, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 768, 770, 772, 774, 777, 779, 781, 783, 833, 835, 837, 839, 840, 842, 844, 846, 896, 898, 900, 902, 905, 907, 909, 911, 961, 963, 965, 967, 968, 970, 972, 974]
private def transition2174Raw1 : List ℕ := [256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private theorem transition2174Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2174Input1) = fromList transition2174Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2174 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0309 = 2 • support0308 := by
  have hs : support0309 = fromList transition2174Input0 + fromList transition2174Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2174Chunk0, transition2174Chunk1]
  have hn : (transition2174Raw0 : Multiset ℕ) + (transition2174Raw1 : Multiset ℕ) = 2 • (supportNumbers0308 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0308] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
