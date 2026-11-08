import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1533Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 544, 546, 548, 550, 609, 611, 613, 615, 672, 674, 676, 678, 737, 739, 741, 743]
private def transition1533Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 128, 704, 130, 706, 132, 708, 134, 710, 193, 641, 195, 643, 197, 645, 199, 647, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 416, 992, 418, 994, 420, 996, 422, 998, 481, 929, 483, 931, 485, 933, 487, 935]
private theorem transition1533Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1533Input0) = fromList transition1533Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1533 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1376 = 1 • support0912 := by
  have hs : support1376 = fromList transition1533Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1533Chunk0]
  have hn : (transition1533Raw0 : Multiset ℕ) = 1 • (supportNumbers0912 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0912] using hm

private def transition1534Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455, 512, 514, 516, 518, 577, 579, 581, 583, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition1534Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition1534Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1534Input0) = fromList transition1534Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1534 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0210 = 2 • support0209 := by
  have hs : support0210 = fromList transition1534Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1534Chunk0]
  have hn : (transition1534Raw0 : Multiset ℕ) = 2 • (supportNumbers0209 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0209] using hm

private def transition1535Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455, 512, 514, 516, 518, 577, 579, 581, 583, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition1535Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 128, 512, 130, 514, 132, 516, 134, 518, 193, 577, 195, 579, 197, 581, 199, 583, 0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 128, 512, 130, 514, 132, 516, 134, 518, 193, 577, 195, 579, 197, 581, 199, 583, 256, 896, 258, 898, 260, 900, 262, 902, 321, 961, 323, 963, 325, 965, 327, 967, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 256, 896, 258, 898, 260, 900, 262, 902, 321, 961, 323, 963, 325, 965, 327, 967, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839]
private theorem transition1535Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1535Input0) = fromList transition1535Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1535 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0210 = 2 • support0210 := by
  have hs : support0210 = fromList transition1535Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1535Chunk0]
  have hn : (transition1535Raw0 : Multiset ℕ) = 2 • (supportNumbers0210 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0210] using hm

private def transition1536Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455, 512, 514, 516, 518, 577, 579, 581, 583, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition1536Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition1536Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1536Input0) = fromList transition1536Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1536 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0210 = 2 • support0209 := by
  have hs : support0210 = fromList transition1536Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1536Chunk0]
  have hn : (transition1536Raw0 : Multiset ℕ) = 2 • (supportNumbers0209 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0209] using hm

private def transition1537Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455, 512, 514, 516, 518, 577, 579, 581, 583, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition1537Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 128, 672, 130, 674, 132, 676, 134, 678, 193, 737, 195, 739, 197, 741, 199, 743, 0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 128, 672, 130, 674, 132, 676, 134, 678, 193, 737, 195, 739, 197, 741, 199, 743, 256, 800, 258, 802, 260, 804, 262, 806, 321, 865, 323, 867, 325, 869, 327, 871, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 256, 800, 258, 802, 260, 804, 262, 806, 321, 865, 323, 867, 325, 869, 327, 871, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999]
private theorem transition1537Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1537Input0) = fromList transition1537Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1537 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0210 = 2 • support1147 := by
  have hs : support0210 = fromList transition1537Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1537Chunk0]
  have hn : (transition1537Raw0 : Multiset ℕ) = 2 • (supportNumbers1147 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1147] using hm

private def transition1538Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 264, 266, 268, 270, 329, 331, 333, 335]
private def transition1538Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 8, 10, 12, 14, 73, 75, 77, 79]
private theorem transition1538Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1538Input0) = fromList transition1538Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1538 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0211 = 1 • support0004 := by
  have hs : support0211 = fromList transition1538Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1538Chunk0]
  have hn : (transition1538Raw0 : Multiset ℕ) = 1 • (supportNumbers0004 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0004] using hm

private def transition1539Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 264, 266, 268, 270, 329, 331, 333, 335]
private def transition1539Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 8, 10, 12, 14, 73, 75, 77, 79]
private theorem transition1539Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1539Input0) = fromList transition1539Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1539 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0211 = 1 • support0004 := by
  have hs : support0211 = fromList transition1539Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1539Chunk0]
  have hn : (transition1539Raw0 : Multiset ℕ) = 1 • (supportNumbers0004 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0004] using hm

private def transition1540Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 264, 266, 268, 270, 329, 331, 333, 335]
private def transition1540Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 8, 10, 12, 14, 73, 75, 77, 79]
private theorem transition1540Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1540Input0) = fromList transition1540Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1540 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0211 = 1 • support0004 := by
  have hs : support0211 = fromList transition1540Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1540Chunk0]
  have hn : (transition1540Raw0 : Multiset ℕ) = 1 • (supportNumbers0004 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0004] using hm

private def transition1541Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 264, 266, 268, 270, 329, 331, 333, 335]
private def transition1541Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 8, 10, 12, 14, 73, 75, 77, 79]
private theorem transition1541Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1541Input0) = fromList transition1541Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1541 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0211 = 1 • support0004 := by
  have hs : support0211 = fromList transition1541Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1541Chunk0]
  have hn : (transition1541Raw0 : Multiset ℕ) = 1 • (supportNumbers0004 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0004] using hm

private def transition1542Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private def transition1542Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private theorem transition1542Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1542Input0) = fromList transition1542Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1542 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0004 = 1 • support0004 := by
  have hs : support0004 = fromList transition1542Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1542Chunk0]
  have hn : (transition1542Raw0 : Multiset ℕ) = 1 • (supportNumbers0004 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0004] using hm

private def transition1543Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private def transition1543Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527]
private theorem transition1543Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1543Input0) = fromList transition1543Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1543 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0004 = 1 • support1157 := by
  have hs : support0004 = fromList transition1543Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1543Chunk0]
  have hn : (transition1543Raw0 : Multiset ℕ) = 1 • (supportNumbers1157 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1157] using hm

private def transition1544Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 264, 266, 268, 270, 329, 331, 333, 335, 640, 642, 644, 646, 705, 707, 709, 711, 904, 906, 908, 910, 969, 971, 973, 975]
private def transition1544Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 8, 10, 12, 14, 73, 75, 77, 79, 384, 386, 388, 390, 449, 451, 453, 455, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition1544Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1544Input0) = fromList transition1544Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1544 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0212 = 1 • support0301 := by
  have hs : support0212 = fromList transition1544Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1544Chunk0]
  have hn : (transition1544Raw0 : Multiset ℕ) = 1 • (supportNumbers0301 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0301] using hm

private def transition1545Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 264, 266, 268, 270, 329, 331, 333, 335, 640, 642, 644, 646, 705, 707, 709, 711, 904, 906, 908, 910, 969, 971, 973, 975]
private def transition1545Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 8, 648, 10, 650, 12, 652, 14, 654, 73, 713, 75, 715, 77, 717, 79, 719, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 392, 776, 394, 778, 396, 780, 398, 782, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition1545Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1545Input0) = fromList transition1545Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1545 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0212 = 1 • support0302 := by
  have hs : support0212 = fromList transition1545Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1545Chunk0]
  have hn : (transition1545Raw0 : Multiset ℕ) = 1 • (supportNumbers0302 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0302] using hm

private def transition1546Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 264, 266, 268, 270, 329, 331, 333, 335, 640, 642, 644, 646, 705, 707, 709, 711, 904, 906, 908, 910, 969, 971, 973, 975]
private def transition1546Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 8, 10, 12, 14, 73, 75, 77, 79, 384, 386, 388, 390, 449, 451, 453, 455, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition1546Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1546Input0) = fromList transition1546Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1546 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0212 = 1 • support0301 := by
  have hs : support0212 = fromList transition1546Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1546Chunk0]
  have hn : (transition1546Raw0 : Multiset ℕ) = 1 • (supportNumbers0301 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0301] using hm

private def transition1547Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition1547Raw0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 130, 134, 138, 142, 195, 199, 203, 207]
private theorem transition1547Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1547Input0) = fromList transition1547Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1547 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0301 = 1 • support1377 := by
  have hs : support0301 = fromList transition1547Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1547Chunk0]
  have hn : (transition1547Raw0 : Multiset ℕ) = 1 • (supportNumbers1377 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1377] using hm

private def transition1548Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition1548Raw0 : List ℕ := [0, 578, 4, 582, 8, 586, 12, 590, 65, 515, 69, 519, 73, 523, 77, 527, 704, 130, 708, 134, 712, 138, 716, 142, 641, 195, 645, 199, 649, 203, 653, 207]
private theorem transition1548Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1548Input0) = fromList transition1548Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1548 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0301 = 1 • support1379 := by
  have hs : support0301 = fromList transition1548Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1548Chunk0]
  have hn : (transition1548Raw0 : Multiset ℕ) = 1 • (supportNumbers1379 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1379] using hm

private def transition1549Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 264, 266, 268, 270, 329, 331, 333, 335, 640, 642, 644, 646, 705, 707, 709, 711, 904, 906, 908, 910, 969, 971, 973, 975]
private def transition1549Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 8, 552, 10, 554, 12, 556, 14, 558, 73, 617, 75, 619, 77, 621, 79, 623, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 392, 936, 394, 938, 396, 940, 398, 942, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition1549Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1549Input0) = fromList transition1549Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1549 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0212 = 1 • support1380 := by
  have hs : support0212 = fromList transition1549Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1549Chunk0]
  have hn : (transition1549Raw0 : Multiset ℕ) = 1 • (supportNumbers1380 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1380] using hm

private def transition1550Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623, 928, 930, 932, 934, 936, 938, 940, 942, 993, 995, 997, 999, 1001, 1003, 1005, 1007]
private def transition1550Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367, 416, 418, 420, 422, 424, 426, 428, 430, 481, 483, 485, 487, 489, 491, 493, 495]
private theorem transition1550Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1550Input0) = fromList transition1550Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1550 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1380 = 1 • support0737 := by
  have hs : support1380 = fromList transition1550Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1550Chunk0]
  have hn : (transition1550Raw0 : Multiset ℕ) = 1 • (supportNumbers0737 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0737] using hm

private def transition1551Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623, 928, 930, 932, 934, 936, 938, 940, 942, 993, 995, 997, 999, 1001, 1003, 1005, 1007]
private def transition1551Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 128, 704, 130, 706, 132, 708, 134, 710, 136, 712, 138, 714, 140, 716, 142, 718, 193, 641, 195, 643, 197, 645, 199, 647, 201, 649, 203, 651, 205, 653, 207, 655, 288, 864, 290, 866, 292, 868, 294, 870, 296, 872, 298, 874, 300, 876, 302, 878, 353, 801, 355, 803, 357, 805, 359, 807, 361, 809, 363, 811, 365, 813, 367, 815, 416, 992, 418, 994, 420, 996, 422, 998, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 481, 929, 483, 931, 485, 933, 487, 935, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition1551Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1551Input0) = fromList transition1551Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1551 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1380 = 1 • support0739 := by
  have hs : support1380 = fromList transition1551Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1551Chunk0]
  have hn : (transition1551Raw0 : Multiset ℕ) = 1 • (supportNumbers0739 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0739] using hm

private def transition1552Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335]
private def transition1552Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 8, 10, 12, 14, 73, 75, 77, 79]
private theorem transition1552Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1552Input0) = fromList transition1552Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1552 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0213 = 1 • support0004 := by
  have hs : support0213 = fromList transition1552Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1552Chunk0]
  have hn : (transition1552Raw0 : Multiset ℕ) = 1 • (supportNumbers0004 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0004] using hm

private def transition1553Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335]
private def transition1553Raw0 : List ℕ := [0, 2, 4, 6, 648, 650, 652, 654, 65, 67, 69, 71, 713, 715, 717, 719, 640, 642, 644, 646, 8, 10, 12, 14, 705, 707, 709, 711, 73, 75, 77, 79]
private theorem transition1553Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1553Input0) = fromList transition1553Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1553 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0213 = 1 • support0303 := by
  have hs : support0213 = fromList transition1553Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1553Chunk0]
  have hn : (transition1553Raw0 : Multiset ℕ) = 1 • (supportNumbers0303 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0303] using hm

private def transition1554Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335]
private def transition1554Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 8, 10, 12, 14, 73, 75, 77, 79]
private theorem transition1554Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1554Input0) = fromList transition1554Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1554 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0213 = 1 • support0004 := by
  have hs : support0213 = fromList transition1554Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1554Chunk0]
  have hn : (transition1554Raw0 : Multiset ℕ) = 1 • (supportNumbers0004 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0004] using hm

private def transition1555Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335]
private def transition1555Raw0 : List ℕ := [0, 2, 4, 6, 552, 554, 556, 558, 65, 67, 69, 71, 617, 619, 621, 623, 544, 546, 548, 550, 8, 10, 12, 14, 609, 611, 613, 615, 73, 75, 77, 79]
private theorem transition1555Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1555Input0) = fromList transition1555Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1555 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0213 = 1 • support1381 := by
  have hs : support0213 = fromList transition1555Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1555Chunk0]
  have hn : (transition1555Raw0 : Multiset ℕ) = 1 • (supportNumbers1381 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1381] using hm

private def transition1556Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623]
private def transition1556Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367]
private theorem transition1556Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1556Input0) = fromList transition1556Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1556 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1381 = 1 • support1153 := by
  have hs : support1381 = fromList transition1556Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1556Chunk0]
  have hn : (transition1556Raw0 : Multiset ℕ) = 1 • (supportNumbers1153 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1153] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
