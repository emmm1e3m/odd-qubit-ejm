import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2101Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition2101Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 20, 564, 21, 565, 22, 566, 23, 567, 28, 572, 29, 573, 30, 574, 31, 575, 128, 672, 129, 673, 130, 674, 131, 675, 136, 680, 137, 681, 138, 682, 139, 683, 148, 692, 149, 693, 150, 694, 151, 695, 156, 700, 157, 701, 158, 702, 159, 703]
private theorem transition2101Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2101Input0) = fromList transition2101Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2101 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0073 = 1 • support0720 := by
  have hs : support0073 = fromList transition2101Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2101Chunk0]
  have hn : (transition2101Raw0 : Multiset ℕ) = 1 • (supportNumbers0720 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0720] using hm

private def transition2102Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 256, 258, 260, 262, 321, 323, 325, 327]
private def transition2102Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition2102Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2102Input0) = fromList transition2102Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2102 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0297 = 1 • support0016 := by
  have hs : support0297 = fromList transition2102Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2102Chunk0]
  have hn : (transition2102Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition2103Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 256, 258, 260, 262, 321, 323, 325, 327]
private def transition2103Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 640, 642, 644, 646, 705, 707, 709, 711]
private theorem transition2103Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2103Input0) = fromList transition2103Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2103 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0297 = 1 • support0075 := by
  have hs : support0297 = fromList transition2103Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2103Chunk0]
  have hn : (transition2103Raw0 : Multiset ℕ) = 1 • (supportNumbers0075 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0075] using hm

private def transition2104Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 256, 258, 260, 262, 321, 323, 325, 327]
private def transition2104Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition2104Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2104Input0) = fromList transition2104Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2104 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0297 = 1 • support0016 := by
  have hs : support0297 = fromList transition2104Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2104Chunk0]
  have hn : (transition2104Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition2105Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 256, 258, 260, 262, 321, 323, 325, 327]
private def transition2105Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 544, 546, 548, 550, 609, 611, 613, 615]
private theorem transition2105Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2105Input0) = fromList transition2105Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2105 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0297 = 1 • support0721 := by
  have hs : support0297 = fromList transition2105Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2105Chunk0]
  have hn : (transition2105Raw0 : Multiset ℕ) = 1 • (supportNumbers0721 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0721] using hm

private def transition2106Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 256, 258, 260, 262, 321, 323, 325, 327, 640, 642, 644, 646, 705, 707, 709, 711, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition2106Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 0, 2, 4, 6, 65, 67, 69, 71, 384, 386, 388, 390, 449, 451, 453, 455, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition2106Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2106Input0) = fromList transition2106Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2106 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0298 = 2 • support0132 := by
  have hs : support0298 = fromList transition2106Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2106Chunk0]
  have hn : (transition2106Raw0 : Multiset ℕ) = 2 • (supportNumbers0132 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0132] using hm

private def transition2107Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 256, 258, 260, 262, 321, 323, 325, 327, 640, 642, 644, 646, 705, 707, 709, 711, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition2107Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839]
private theorem transition2107Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2107Input0) = fromList transition2107Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2107 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0298 = 2 • support0133 := by
  have hs : support0298 = fromList transition2107Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2107Chunk0]
  have hn : (transition2107Raw0 : Multiset ℕ) = 2 • (supportNumbers0133 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0133] using hm

private def transition2108Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 256, 258, 260, 262, 321, 323, 325, 327, 640, 642, 644, 646, 705, 707, 709, 711, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition2108Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 0, 2, 4, 6, 65, 67, 69, 71, 384, 386, 388, 390, 449, 451, 453, 455, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition2108Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2108Input0) = fromList transition2108Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2108 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0298 = 2 • support0132 := by
  have hs : support0298 = fromList transition2108Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2108Chunk0]
  have hn : (transition2108Raw0 : Multiset ℕ) = 2 • (supportNumbers0132 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0132] using hm

private def transition2109Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 256, 258, 260, 262, 321, 323, 325, 327, 640, 642, 644, 646, 705, 707, 709, 711, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition2109Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999]
private theorem transition2109Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2109Input0) = fromList transition2109Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2109 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0298 = 2 • support0909 := by
  have hs : support0298 = fromList transition2109Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2109Chunk0]
  have hn : (transition2109Raw0 : Multiset ℕ) = 2 • (supportNumbers0909 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0909] using hm

private def transition2110Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private def transition2110Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private theorem transition2110Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2110Input0) = fromList transition2110Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2110 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0299 = 1 • support0299 := by
  have hs : support0299 = fromList transition2110Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2110Chunk0]
  have hn : (transition2110Raw0 : Multiset ℕ) = 1 • (supportNumbers0299 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0299] using hm

private def transition2111Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private def transition2111Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private theorem transition2111Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2111Input0) = fromList transition2111Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2111 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0299 = 1 • support0299 := by
  have hs : support0299 = fromList transition2111Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2111Chunk0]
  have hn : (transition2111Raw0 : Multiset ℕ) = 1 • (supportNumbers0299 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0299] using hm

private def transition2112Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private def transition2112Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private theorem transition2112Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2112Input0) = fromList transition2112Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2112 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0299 = 1 • support0299 := by
  have hs : support0299 = fromList transition2112Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2112Chunk0]
  have hn : (transition2112Raw0 : Multiset ℕ) = 1 • (supportNumbers0299 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0299] using hm

private def transition2113Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private def transition2113Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private theorem transition2113Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2113Input0) = fromList transition2113Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2113 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0299 = 1 • support0299 := by
  have hs : support0299 = fromList transition2113Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2113Chunk0]
  have hn : (transition2113Raw0 : Multiset ℕ) = 1 • (supportNumbers0299 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0299] using hm

private def transition2114Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private def transition2114Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private theorem transition2114Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2114Input0) = fromList transition2114Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2114 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0299 = 1 • support0299 := by
  have hs : support0299 = fromList transition2114Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2114Chunk0]
  have hn : (transition2114Raw0 : Multiset ℕ) = 1 • (supportNumbers0299 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0299] using hm

private def transition2115Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private def transition2115Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 128, 704, 130, 706, 132, 708, 134, 710, 193, 641, 195, 643, 197, 645, 199, 647]
private theorem transition2115Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2115Input0) = fromList transition2115Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2115 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0299 = 1 • support1146 := by
  have hs : support0299 = fromList transition2115Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2115Chunk0]
  have hn : (transition2115Raw0 : Multiset ℕ) = 1 • (supportNumbers1146 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1146] using hm

private def transition2116Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 512, 514, 516, 518, 577, 579, 581, 583, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition2116Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition2116Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2116Input0) = fromList transition2116Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2116 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0300 = 1 • support0209 := by
  have hs : support0300 = fromList transition2116Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2116Chunk0]
  have hn : (transition2116Raw0 : Multiset ℕ) = 1 • (supportNumbers0209 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0209] using hm

private def transition2117Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 512, 514, 516, 518, 577, 579, 581, 583, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition2117Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 128, 512, 130, 514, 132, 516, 134, 518, 193, 577, 195, 579, 197, 581, 199, 583, 256, 896, 258, 898, 260, 900, 262, 902, 321, 961, 323, 963, 325, 965, 327, 967, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839]
private theorem transition2117Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2117Input0) = fromList transition2117Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2117 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0300 = 1 • support0210 := by
  have hs : support0300 = fromList transition2117Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2117Chunk0]
  have hn : (transition2117Raw0 : Multiset ℕ) = 1 • (supportNumbers0210 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0210] using hm

private def transition2118Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 512, 514, 516, 518, 577, 579, 581, 583, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition2118Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition2118Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2118Input0) = fromList transition2118Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2118 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0300 = 1 • support0209 := by
  have hs : support0300 = fromList transition2118Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2118Chunk0]
  have hn : (transition2118Raw0 : Multiset ℕ) = 1 • (supportNumbers0209 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0209] using hm

private def transition2119Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 512, 514, 516, 518, 577, 579, 581, 583, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition2119Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 128, 672, 130, 674, 132, 676, 134, 678, 193, 737, 195, 739, 197, 741, 199, 743, 256, 800, 258, 802, 260, 804, 262, 806, 321, 865, 323, 867, 325, 869, 327, 871, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999]
private theorem transition2119Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2119Input0) = fromList transition2119Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2119 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0300 = 1 • support1147 := by
  have hs : support0300 = fromList transition2119Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2119Chunk0]
  have hn : (transition2119Raw0 : Multiset ℕ) = 1 • (supportNumbers1147 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1147] using hm

private def transition2120Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private def transition2120Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private theorem transition2120Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2120Input0) = fromList transition2120Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2120 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0004 = 1 • support0004 := by
  have hs : support0004 = fromList transition2120Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2120Chunk0]
  have hn : (transition2120Raw0 : Multiset ℕ) = 1 • (supportNumbers0004 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0004] using hm

private def transition2121Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private def transition2121Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719]
private theorem transition2121Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2121Input0) = fromList transition2121Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2121 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0004 = 1 • support0303 := by
  have hs : support0004 = fromList transition2121Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2121Chunk0]
  have hn : (transition2121Raw0 : Multiset ℕ) = 1 • (supportNumbers0303 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0303] using hm

private def transition2122Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private def transition2122Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private theorem transition2122Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2122Input0) = fromList transition2122Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2122 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0004 = 1 • support0004 := by
  have hs : support0004 = fromList transition2122Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2122Chunk0]
  have hn : (transition2122Raw0 : Multiset ℕ) = 1 • (supportNumbers0004 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0004] using hm

private def transition2123Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private def transition2123Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623]
private theorem transition2123Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2123Input0) = fromList transition2123Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2123 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0004 = 1 • support1381 := by
  have hs : support0004 = fromList transition2123Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2123Chunk0]
  have hn : (transition2123Raw0 : Multiset ℕ) = 1 • (supportNumbers1381 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1381] using hm

private def transition2124Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition2124Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition2124Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2124Input0) = fromList transition2124Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2124 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0301 = 1 • support0076 := by
  have hs : support0301 = fromList transition2124Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2124Chunk0]
  have hn : (transition2124Raw0 : Multiset ℕ) = 1 • (supportNumbers0076 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0076] using hm

private def transition2125Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition2125Raw0 : List ℕ := [0, 2, 4, 6, 648, 650, 652, 654, 65, 67, 69, 71, 713, 715, 717, 719, 512, 514, 516, 518, 136, 138, 140, 142, 577, 579, 581, 583, 201, 203, 205, 207]
private theorem transition2125Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2125Input0) = fromList transition2125Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2125 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0301 = 1 • support0381 := by
  have hs : support0301 = fromList transition2125Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2125Chunk0]
  have hn : (transition2125Raw0 : Multiset ℕ) = 1 • (supportNumbers0381 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0381] using hm

private def transition2126Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition2126Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition2126Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2126Input0) = fromList transition2126Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2126 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0301 = 1 • support0076 := by
  have hs : support0301 = fromList transition2126Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2126Chunk0]
  have hn : (transition2126Raw0 : Multiset ℕ) = 1 • (supportNumbers0076 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0076] using hm

private def transition2127Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition2127Raw0 : List ℕ := [0, 2, 4, 6, 552, 554, 556, 558, 65, 67, 69, 71, 617, 619, 621, 623, 672, 674, 676, 678, 136, 138, 140, 142, 737, 739, 741, 743, 201, 203, 205, 207]
private theorem transition2127Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2127Input0) = fromList transition2127Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2127 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0301 = 1 • support1558 := by
  have hs : support0301 = fromList transition2127Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2127Chunk0]
  have hn : (transition2127Raw0 : Multiset ℕ) = 1 • (supportNumbers1558 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1558] using hm

private def transition2128Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 552, 554, 556, 558, 617, 619, 621, 623, 672, 674, 676, 678, 737, 739, 741, 743]
private def transition2128Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 296, 298, 300, 302, 361, 363, 365, 367, 416, 418, 420, 422, 481, 483, 485, 487]
private theorem transition2128Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2128Input0) = fromList transition2128Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2128 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1558 = 1 • support1559 := by
  have hs : support1558 = fromList transition2128Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2128Chunk0]
  have hn : (transition2128Raw0 : Multiset ℕ) = 1 • (supportNumbers1559 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1559] using hm

private def transition2129Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 552, 554, 556, 558, 617, 619, 621, 623, 672, 674, 676, 678, 737, 739, 741, 743]
private def transition2129Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 136, 712, 138, 714, 140, 716, 142, 718, 201, 649, 203, 651, 205, 653, 207, 655, 296, 872, 298, 874, 300, 876, 302, 878, 361, 809, 363, 811, 365, 813, 367, 815, 416, 992, 418, 994, 420, 996, 422, 998, 481, 929, 483, 931, 485, 933, 487, 935]
private theorem transition2129Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2129Input0) = fromList transition2129Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2129 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1558 = 1 • support1561 := by
  have hs : support1558 = fromList transition2129Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2129Chunk0]
  have hn : (transition2129Raw0 : Multiset ℕ) = 1 • (supportNumbers1561 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1561] using hm

private def transition2130Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 768, 770, 772, 774, 776, 778, 780, 782, 833, 835, 837, 839, 841, 843, 845, 847]
private def transition2130Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335]
private theorem transition2130Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2130Input0) = fromList transition2130Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2130 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0302 = 1 • support0137 := by
  have hs : support0302 = fromList transition2130Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2130Chunk0]
  have hn : (transition2130Raw0 : Multiset ℕ) = 1 • (supportNumbers0137 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0137] using hm

private def transition2131Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 768, 770, 772, 774, 776, 778, 780, 782, 833, 835, 837, 839, 841, 843, 845, 847]
private def transition2131Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 128, 512, 130, 514, 132, 516, 134, 518, 136, 520, 138, 522, 140, 524, 142, 526, 193, 577, 195, 579, 197, 581, 199, 583, 201, 585, 203, 587, 205, 589, 207, 591, 384, 768, 386, 770, 388, 772, 390, 774, 392, 776, 394, 778, 396, 780, 398, 782, 449, 833, 451, 835, 453, 837, 455, 839, 457, 841, 459, 843, 461, 845, 463, 847, 256, 896, 258, 898, 260, 900, 262, 902, 264, 904, 266, 906, 268, 908, 270, 910, 321, 961, 323, 963, 325, 965, 327, 967, 329, 969, 331, 971, 333, 973, 335, 975]
private theorem transition2131Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2131Input0) = fromList transition2131Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2131 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0302 = 1 • support0138 := by
  have hs : support0302 = fromList transition2131Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2131Chunk0]
  have hn : (transition2131Raw0 : Multiset ℕ) = 1 • (supportNumbers0138 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0138] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
