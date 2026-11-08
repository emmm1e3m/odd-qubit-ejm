import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1633Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 264, 266, 268, 270, 329, 331, 333, 335, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition1633Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 8, 10, 12, 14, 73, 75, 77, 79, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition1633Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1633Input0) = fromList transition1633Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1633 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0224 = 1 • support0315 := by
  have hs : support0224 = fromList transition1633Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1633Chunk0]
  have hn : (transition1633Raw0 : Multiset ℕ) = 1 • (supportNumbers0315 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0315] using hm

private def transition1634Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private def transition1634Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private theorem transition1634Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1634Input0) = fromList transition1634Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1634 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0315 = 1 • support0315 := by
  have hs : support0315 = fromList transition1634Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1634Chunk0]
  have hn : (transition1634Raw0 : Multiset ℕ) = 1 • (supportNumbers0315 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0315] using hm

private def transition1635Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private def transition1635Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 129, 705, 131, 707, 133, 709, 135, 711, 137, 713, 139, 715, 141, 717, 143, 719, 192, 640, 194, 642, 196, 644, 198, 646, 200, 648, 202, 650, 204, 652, 206, 654]
private theorem transition1635Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1635Input0) = fromList transition1635Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1635 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0315 = 1 • support0398 := by
  have hs : support0315 = fromList transition1635Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1635Chunk0]
  have hn : (transition1635Raw0 : Multiset ℕ) = 1 • (supportNumbers0398 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0398] using hm

private def transition1636Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 264, 266, 268, 270, 329, 331, 333, 335, 393, 395, 397, 399, 456, 458, 460, 462, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 777, 779, 781, 783, 840, 842, 844, 846, 904, 906, 908, 910, 969, 971, 973, 975]
private def transition1636Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 8, 10, 12, 14, 73, 75, 77, 79, 137, 139, 141, 143, 200, 202, 204, 206, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455, 265, 267, 269, 271, 328, 330, 332, 334, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition1636Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1636Input0) = fromList transition1636Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1636 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0225 = 1 • support0042 := by
  have hs : support0225 = fromList transition1636Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1636Chunk0]
  have hn : (transition1636Raw0 : Multiset ℕ) = 1 • (supportNumbers0042 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0042] using hm

private def transition1637Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 264, 266, 268, 270, 329, 331, 333, 335, 393, 395, 397, 399, 456, 458, 460, 462, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 777, 779, 781, 783, 840, 842, 844, 846, 904, 906, 908, 910, 969, 971, 973, 975]
private def transition1637Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 129, 513, 131, 515, 133, 517, 135, 519, 192, 576, 194, 578, 196, 580, 198, 582, 8, 648, 10, 650, 12, 652, 14, 654, 73, 713, 75, 715, 77, 717, 79, 719, 137, 521, 139, 523, 141, 525, 143, 527, 200, 584, 202, 586, 204, 588, 206, 590, 257, 897, 259, 899, 261, 901, 263, 903, 320, 960, 322, 962, 324, 964, 326, 966, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 265, 905, 267, 907, 269, 909, 271, 911, 328, 968, 330, 970, 332, 972, 334, 974, 392, 776, 394, 778, 396, 780, 398, 782, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition1637Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1637Input0) = fromList transition1637Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1637 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0225 = 1 • support0043 := by
  have hs : support0225 = fromList transition1637Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1637Chunk0]
  have hn : (transition1637Raw0 : Multiset ℕ) = 1 • (supportNumbers0043 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0043] using hm

private def transition1638Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 264, 266, 268, 270, 329, 331, 333, 335, 393, 395, 397, 399, 456, 458, 460, 462, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 777, 779, 781, 783, 840, 842, 844, 846, 904, 906, 908, 910, 969, 971, 973, 975]
private def transition1638Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 8, 10, 12, 14, 73, 75, 77, 79, 137, 139, 141, 143, 200, 202, 204, 206, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455, 265, 267, 269, 271, 328, 330, 332, 334, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition1638Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1638Input0) = fromList transition1638Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1638 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0225 = 1 • support0042 := by
  have hs : support0225 = fromList transition1638Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1638Chunk0]
  have hn : (transition1638Raw0 : Multiset ℕ) = 1 • (supportNumbers0042 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0042] using hm

private def transition1639Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 264, 266, 268, 270, 329, 331, 333, 335, 393, 395, 397, 399, 456, 458, 460, 462, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 777, 779, 781, 783, 840, 842, 844, 846, 904, 906, 908, 910, 969, 971, 973, 975]
private def transition1639Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 129, 673, 131, 675, 133, 677, 135, 679, 192, 736, 194, 738, 196, 740, 198, 742, 8, 552, 10, 554, 12, 556, 14, 558, 73, 617, 75, 619, 77, 621, 79, 623, 137, 681, 139, 683, 141, 685, 143, 687, 200, 744, 202, 746, 204, 748, 206, 750, 257, 801, 259, 803, 261, 805, 263, 807, 320, 864, 322, 866, 324, 868, 326, 870, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 265, 809, 267, 811, 269, 813, 271, 815, 328, 872, 330, 874, 332, 876, 334, 878, 392, 936, 394, 938, 396, 940, 398, 942, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition1639Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1639Input0) = fromList transition1639Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1639 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0225 = 1 • support0615 := by
  have hs : support0225 = fromList transition1639Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1639Chunk0]
  have hn : (transition1639Raw0 : Multiset ℕ) = 1 • (supportNumbers0615 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0615] using hm

private def transition1640Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718]
private def transition1640Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private theorem transition1640Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1640Input0) = fromList transition1640Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1640 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0226 = 1 • support0227 := by
  have hs : support0226 = fromList transition1640Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1640Chunk0]
  have hn : (transition1640Raw0 : Multiset ℕ) = 1 • (supportNumbers0227 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0227] using hm

private def transition1641Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718]
private def transition1641Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718, 129, 513, 131, 515, 133, 517, 135, 519, 136, 520, 138, 522, 140, 524, 142, 526, 192, 576, 194, 578, 196, 580, 198, 582, 201, 585, 203, 587, 205, 589, 207, 591, 257, 897, 259, 899, 261, 901, 263, 903, 264, 904, 266, 906, 268, 908, 270, 910, 320, 960, 322, 962, 324, 964, 326, 966, 329, 969, 331, 971, 333, 973, 335, 975, 384, 768, 386, 770, 388, 772, 390, 774, 393, 777, 395, 779, 397, 781, 399, 783, 449, 833, 451, 835, 453, 837, 455, 839, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition1641Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1641Input0) = fromList transition1641Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1641 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0226 = 1 • support0228 := by
  have hs : support0226 = fromList transition1641Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1641Chunk0]
  have hn : (transition1641Raw0 : Multiset ℕ) = 1 • (supportNumbers0228 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0228] using hm

private def transition1642Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718]
private def transition1642Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private theorem transition1642Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1642Input0) = fromList transition1642Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1642 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0226 = 1 • support0227 := by
  have hs : support0226 = fromList transition1642Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1642Chunk0]
  have hn : (transition1642Raw0 : Multiset ℕ) = 1 • (supportNumbers0227 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0227] using hm

private def transition1643Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718]
private def transition1643Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 9, 553, 11, 555, 13, 557, 15, 559, 65, 609, 67, 611, 69, 613, 71, 615, 72, 616, 74, 618, 76, 620, 78, 622, 129, 673, 131, 675, 133, 677, 135, 679, 136, 680, 138, 682, 140, 684, 142, 686, 192, 736, 194, 738, 196, 740, 198, 742, 201, 745, 203, 747, 205, 749, 207, 751, 257, 801, 259, 803, 261, 805, 263, 807, 264, 808, 266, 810, 268, 812, 270, 814, 320, 864, 322, 866, 324, 868, 326, 870, 329, 873, 331, 875, 333, 877, 335, 879, 384, 928, 386, 930, 388, 932, 390, 934, 393, 937, 395, 939, 397, 941, 399, 943, 449, 993, 451, 995, 453, 997, 455, 999, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition1643Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1643Input0) = fromList transition1643Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1643 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0226 = 1 • support1192 := by
  have hs : support0226 = fromList transition1643Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1643Chunk0]
  have hn : (transition1643Raw0 : Multiset ℕ) = 1 • (supportNumbers1192 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1192] using hm

private def transition1644Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1644Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 8, 10, 12, 14, 73, 75, 77, 79, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition1644Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1644Input0) = fromList transition1644Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1644 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0227 = 1 • support0315 := by
  have hs : support0227 = fromList transition1644Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1644Chunk0]
  have hn : (transition1644Raw0 : Multiset ℕ) = 1 • (supportNumbers0315 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0315] using hm

private def transition1645Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1645Raw0 : List ℕ := [0, 2, 4, 6, 649, 651, 653, 655, 65, 67, 69, 71, 712, 714, 716, 718, 129, 131, 133, 135, 520, 522, 524, 526, 192, 194, 196, 198, 585, 587, 589, 591, 641, 643, 645, 647, 8, 10, 12, 14, 704, 706, 708, 710, 73, 75, 77, 79, 512, 514, 516, 518, 137, 139, 141, 143, 577, 579, 581, 583, 200, 202, 204, 206]
private theorem transition1645Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1645Input0) = fromList transition1645Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1645 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0227 = 1 • support0316 := by
  have hs : support0227 = fromList transition1645Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1645Chunk0]
  have hn : (transition1645Raw0 : Multiset ℕ) = 1 • (supportNumbers0316 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0316] using hm

private def transition1646Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1646Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 8, 10, 12, 14, 73, 75, 77, 79, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition1646Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1646Input0) = fromList transition1646Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1646 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0227 = 1 • support0315 := by
  have hs : support0227 = fromList transition1646Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1646Chunk0]
  have hn : (transition1646Raw0 : Multiset ℕ) = 1 • (supportNumbers0315 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0315] using hm

private def transition1647Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 257, 259, 261, 263, 264, 266, 268, 270, 320, 322, 324, 326, 329, 331, 333, 335, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1647Raw0 : List ℕ := [0, 2, 4, 6, 553, 555, 557, 559, 65, 67, 69, 71, 616, 618, 620, 622, 129, 131, 133, 135, 680, 682, 684, 686, 192, 194, 196, 198, 745, 747, 749, 751, 545, 547, 549, 551, 8, 10, 12, 14, 608, 610, 612, 614, 73, 75, 77, 79, 672, 674, 676, 678, 137, 139, 141, 143, 737, 739, 741, 743, 200, 202, 204, 206]
private theorem transition1647Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1647Input0) = fromList transition1647Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1647 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0227 = 1 • support1415 := by
  have hs : support0227 = fromList transition1647Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1647Chunk0]
  have hn : (transition1647Raw0 : Multiset ℕ) = 1 • (supportNumbers1415 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1415] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
