import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1557Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623]
private def transition1557Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 288, 864, 290, 866, 292, 868, 294, 870, 296, 872, 298, 874, 300, 876, 302, 878, 353, 801, 355, 803, 357, 805, 359, 807, 361, 809, 363, 811, 365, 813, 367, 815]
private theorem transition1557Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1557Input0) = fromList transition1557Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1557 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1381 = 1 • support1155 := by
  have hs : support1381 = fromList transition1557Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1557Chunk0]
  have hn : (transition1557Raw0 : Multiset ℕ) = 1 • (supportNumbers1155 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1155] using hm

private def transition1558Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 896, 898, 900, 902, 904, 906, 908, 910, 961, 963, 965, 967, 969, 971, 973, 975]
private def transition1558Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private theorem transition1558Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1558Input0) = fromList transition1558Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1558 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0214 = 2 • support0301 := by
  have hs : support0214 = fromList transition1558Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1558Chunk0]
  have hn : (transition1558Raw0 : Multiset ℕ) = 2 • (supportNumbers0301 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0301] using hm

private def transition1559Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 896, 898, 900, 902, 904, 906, 908, 910, 961, 963, 965, 967, 969, 971, 973, 975]
private def transition1559Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 384, 768, 386, 770, 388, 772, 390, 774, 392, 776, 394, 778, 396, 780, 398, 782, 449, 833, 451, 835, 453, 837, 455, 839, 457, 841, 459, 843, 461, 845, 463, 847, 384, 768, 386, 770, 388, 772, 390, 774, 392, 776, 394, 778, 396, 780, 398, 782, 449, 833, 451, 835, 453, 837, 455, 839, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition1559Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1559Input0) = fromList transition1559Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1559 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0214 = 2 • support0302 := by
  have hs : support0214 = fromList transition1559Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1559Chunk0]
  have hn : (transition1559Raw0 : Multiset ℕ) = 2 • (supportNumbers0302 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0302] using hm

private def transition1560Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 896, 898, 900, 902, 904, 906, 908, 910, 961, 963, 965, 967, 969, 971, 973, 975]
private def transition1560Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private theorem transition1560Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1560Input0) = fromList transition1560Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1560 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0214 = 2 • support0301 := by
  have hs : support0214 = fromList transition1560Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1560Chunk0]
  have hn : (transition1560Raw0 : Multiset ℕ) = 2 • (supportNumbers0301 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0301] using hm

private def transition1561Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 896, 898, 900, 902, 904, 906, 908, 910, 961, 963, 965, 967, 969, 971, 973, 975]
private def transition1561Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623, 0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623, 384, 928, 386, 930, 388, 932, 390, 934, 392, 936, 394, 938, 396, 940, 398, 942, 449, 993, 451, 995, 453, 997, 455, 999, 457, 1001, 459, 1003, 461, 1005, 463, 1007, 384, 928, 386, 930, 388, 932, 390, 934, 392, 936, 394, 938, 396, 940, 398, 942, 449, 993, 451, 995, 453, 997, 455, 999, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition1561Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1561Input0) = fromList transition1561Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1561 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0214 = 2 • support1380 := by
  have hs : support0214 = fromList transition1561Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1561Chunk0]
  have hn : (transition1561Raw0 : Multiset ℕ) = 2 • (supportNumbers1380 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1380] using hm

private def transition1562Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private def transition1562Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private theorem transition1562Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1562Input0) = fromList transition1562Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1562 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0215 = 1 • support0299 := by
  have hs : support0215 = fromList transition1562Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1562Chunk0]
  have hn : (transition1562Raw0 : Multiset ℕ) = 1 • (supportNumbers0299 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0299] using hm

private def transition1563Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private def transition1563Raw0 : List ℕ := [0, 2, 4, 6, 648, 650, 652, 654, 65, 67, 69, 71, 713, 715, 717, 719, 128, 130, 132, 134, 520, 522, 524, 526, 193, 195, 197, 199, 585, 587, 589, 591]
private theorem transition1563Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1563Input0) = fromList transition1563Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1563 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0215 = 1 • support0304 := by
  have hs : support0215 = fromList transition1563Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1563Chunk0]
  have hn : (transition1563Raw0 : Multiset ℕ) = 1 • (supportNumbers0304 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0304] using hm

private def transition1564Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private def transition1564Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private theorem transition1564Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1564Input0) = fromList transition1564Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1564 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0215 = 1 • support0299 := by
  have hs : support0215 = fromList transition1564Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1564Chunk0]
  have hn : (transition1564Raw0 : Multiset ℕ) = 1 • (supportNumbers0299 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0299] using hm

private def transition1565Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private def transition1565Raw0 : List ℕ := [0, 2, 4, 6, 552, 554, 556, 558, 65, 67, 69, 71, 617, 619, 621, 623, 128, 130, 132, 134, 680, 682, 684, 686, 193, 195, 197, 199, 745, 747, 749, 751]
private theorem transition1565Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1565Input0) = fromList transition1565Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1565 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0215 = 1 • support1382 := by
  have hs : support0215 = fromList transition1565Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1565Chunk0]
  have hn : (transition1565Raw0 : Multiset ℕ) = 1 • (supportNumbers1382 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1382] using hm

private def transition1566Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 552, 554, 556, 558, 617, 619, 621, 623, 680, 682, 684, 686, 745, 747, 749, 751]
private def transition1566Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 296, 298, 300, 302, 361, 363, 365, 367, 424, 426, 428, 430, 489, 491, 493, 495]
private theorem transition1566Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1566Input0) = fromList transition1566Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1566 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1382 = 1 • support1383 := by
  have hs : support1382 = fromList transition1566Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1566Chunk0]
  have hn : (transition1566Raw0 : Multiset ℕ) = 1 • (supportNumbers1383 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1383] using hm

private def transition1567Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 552, 554, 556, 558, 617, 619, 621, 623, 680, 682, 684, 686, 745, 747, 749, 751]
private def transition1567Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 128, 704, 130, 706, 132, 708, 134, 710, 193, 641, 195, 643, 197, 645, 199, 647, 296, 872, 298, 874, 300, 876, 302, 878, 361, 809, 363, 811, 365, 813, 367, 815, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition1567Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1567Input0) = fromList transition1567Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1567 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1382 = 1 • support1385 := by
  have hs : support1382 = fromList transition1567Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1567Chunk0]
  have hn : (transition1567Raw0 : Multiset ℕ) = 1 • (supportNumbers1385 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1385] using hm

private def transition1568Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 512, 514, 516, 518, 520, 522, 524, 526, 577, 579, 581, 583, 585, 587, 589, 591, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719]
private def transition1568Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private theorem transition1568Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1568Input0) = fromList transition1568Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1568 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0216 = 1 • support0137 := by
  have hs : support0216 = fromList transition1568Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1568Chunk0]
  have hn : (transition1568Raw0 : Multiset ℕ) = 1 • (supportNumbers0137 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0137] using hm

private def transition1569Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 512, 514, 516, 518, 520, 522, 524, 526, 577, 579, 581, 583, 585, 587, 589, 591, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719]
private def transition1569Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 128, 512, 130, 514, 132, 516, 134, 518, 136, 520, 138, 522, 140, 524, 142, 526, 193, 577, 195, 579, 197, 581, 199, 583, 201, 585, 203, 587, 205, 589, 207, 591, 256, 896, 258, 898, 260, 900, 262, 902, 264, 904, 266, 906, 268, 908, 270, 910, 321, 961, 323, 963, 325, 965, 327, 967, 329, 969, 331, 971, 333, 973, 335, 975, 384, 768, 386, 770, 388, 772, 390, 774, 392, 776, 394, 778, 396, 780, 398, 782, 449, 833, 451, 835, 453, 837, 455, 839, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition1569Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1569Input0) = fromList transition1569Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1569 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0216 = 1 • support0138 := by
  have hs : support0216 = fromList transition1569Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1569Chunk0]
  have hn : (transition1569Raw0 : Multiset ℕ) = 1 • (supportNumbers0138 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0138] using hm

private def transition1570Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 512, 514, 516, 518, 520, 522, 524, 526, 577, 579, 581, 583, 585, 587, 589, 591, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719]
private def transition1570Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private theorem transition1570Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1570Input0) = fromList transition1570Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1570 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0216 = 1 • support0137 := by
  have hs : support0216 = fromList transition1570Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1570Chunk0]
  have hn : (transition1570Raw0 : Multiset ℕ) = 1 • (supportNumbers0137 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0137] using hm

private def transition1571Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 512, 514, 516, 518, 520, 522, 524, 526, 577, 579, 581, 583, 585, 587, 589, 591, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719]
private def transition1571Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623, 128, 672, 130, 674, 132, 676, 134, 678, 136, 680, 138, 682, 140, 684, 142, 686, 193, 737, 195, 739, 197, 741, 199, 743, 201, 745, 203, 747, 205, 749, 207, 751, 256, 800, 258, 802, 260, 804, 262, 806, 264, 808, 266, 810, 268, 812, 270, 814, 321, 865, 323, 867, 325, 869, 327, 871, 329, 873, 331, 875, 333, 877, 335, 879, 384, 928, 386, 930, 388, 932, 390, 934, 392, 936, 394, 938, 396, 940, 398, 942, 449, 993, 451, 995, 453, 997, 455, 999, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition1571Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1571Input0) = fromList transition1571Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1571 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0216 = 1 • support0930 := by
  have hs : support0216 = fromList transition1571Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1571Chunk0]
  have hn : (transition1571Raw0 : Multiset ℕ) = 1 • (supportNumbers0930 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0930] using hm

private def transition1572Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78]
private def transition1572Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition1572Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1572Input0) = fromList transition1572Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1572 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0217 = 1 • support0016 := by
  have hs : support0217 = fromList transition1572Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1572Chunk0]
  have hn : (transition1572Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition1573Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78]
private def transition1573Raw0 : List ℕ := [0, 2, 4, 6, 649, 651, 653, 655, 65, 67, 69, 71, 712, 714, 716, 718]
private theorem transition1573Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1573Input0) = fromList transition1573Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1573 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0217 = 1 • support0305 := by
  have hs : support0217 = fromList transition1573Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1573Chunk0]
  have hn : (transition1573Raw0 : Multiset ℕ) = 1 • (supportNumbers0305 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0305] using hm

private def transition1574Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78]
private def transition1574Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition1574Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1574Input0) = fromList transition1574Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1574 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0217 = 1 • support0016 := by
  have hs : support0217 = fromList transition1574Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1574Chunk0]
  have hn : (transition1574Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition1575Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78]
private def transition1575Raw0 : List ℕ := [0, 2, 4, 6, 553, 555, 557, 559, 65, 67, 69, 71, 616, 618, 620, 622]
private theorem transition1575Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1575Input0) = fromList transition1575Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1575 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0217 = 1 • support1386 := by
  have hs : support0217 = fromList transition1575Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1575Chunk0]
  have hn : (transition1575Raw0 : Multiset ℕ) = 1 • (supportNumbers1386 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1386] using hm

private def transition1576Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 553, 555, 557, 559, 616, 618, 620, 622]
private def transition1576Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 297, 299, 301, 303, 360, 362, 364, 366]
private theorem transition1576Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1576Input0) = fromList transition1576Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1576 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1386 = 1 • support1387 := by
  have hs : support1386 = fromList transition1576Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1576Chunk0]
  have hn : (transition1576Raw0 : Multiset ℕ) = 1 • (supportNumbers1387 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1387] using hm

private def transition1577Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 553, 555, 557, 559, 616, 618, 620, 622]
private def transition1577Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 297, 873, 299, 875, 301, 877, 303, 879, 360, 808, 362, 810, 364, 812, 366, 814]
private theorem transition1577Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1577Input0) = fromList transition1577Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1577 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1386 = 1 • support1389 := by
  have hs : support1386 = fromList transition1577Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1577Chunk0]
  have hn : (transition1577Raw0 : Multiset ℕ) = 1 • (supportNumbers1389 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1389] using hm

private def transition1578Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78]
private def transition1578Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78]
private theorem transition1578Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1578Input0) = fromList transition1578Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1578 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0217 = 1 • support0217 := by
  have hs : support0217 = fromList transition1578Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1578Chunk0]
  have hn : (transition1578Raw0 : Multiset ℕ) = 1 • (supportNumbers0217 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0217] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
