import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2649Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455, 544, 546, 548, 550, 609, 611, 613, 615, 681, 683, 685, 687, 744, 746, 748, 750, 809, 811, 813, 815, 872, 874, 876, 878, 928, 930, 932, 934, 993, 995, 997, 999]
private def transition2649Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 137, 713, 139, 715, 141, 717, 143, 719, 200, 648, 202, 650, 204, 652, 206, 654, 9, 585, 11, 587, 13, 589, 15, 591, 72, 520, 74, 522, 76, 524, 78, 526, 128, 704, 130, 706, 132, 708, 134, 710, 193, 641, 195, 643, 197, 645, 199, 647, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 488, 936, 490, 938, 492, 940, 494, 942, 297, 873, 299, 875, 301, 877, 303, 879, 360, 808, 362, 810, 364, 812, 366, 814, 416, 992, 418, 994, 420, 996, 422, 998, 481, 929, 483, 931, 485, 933, 487, 935]
private theorem transition2649Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2649Input0) = fromList transition2649Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2649 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1693 = 1 • support1173 := by
  have hs : support1693 = fromList transition2649Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2649Chunk0]
  have hn : (transition2649Raw0 : Multiset ℕ) = 1 • (supportNumbers1173 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1173] using hm

private def transition2650Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 256, 258, 260, 262, 321, 323, 325, 327, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition2650Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition2650Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2650Input0) = fromList transition2650Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2650 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0386 = 1 • support0040 := by
  have hs : support0386 = fromList transition2650Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2650Chunk0]
  have hn : (transition2650Raw0 : Multiset ℕ) = 1 • (supportNumbers0040 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0040] using hm

private def transition2651Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 256, 258, 260, 262, 321, 323, 325, 327, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition2651Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition2651Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2651Input0) = fromList transition2651Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2651 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0386 = 1 • support0441 := by
  have hs : support0386 = fromList transition2651Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2651Chunk0]
  have hn : (transition2651Raw0 : Multiset ℕ) = 1 • (supportNumbers0441 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0441] using hm

private def transition2652Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 256, 258, 260, 262, 321, 323, 325, 327, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition2652Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition2652Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2652Input0) = fromList transition2652Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2652 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0386 = 1 • support0040 := by
  have hs : support0386 = fromList transition2652Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2652Chunk0]
  have hn : (transition2652Raw0 : Multiset ℕ) = 1 • (supportNumbers0040 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0040] using hm

private def transition2653Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 256, 258, 260, 262, 321, 323, 325, 327, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition2653Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 681, 683, 685, 687, 744, 746, 748, 750, 544, 546, 548, 550, 609, 611, 613, 615, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition2653Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2653Input0) = fromList transition2653Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2653 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0386 = 1 • support1694 := by
  have hs : support0386 = fromList transition2653Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2653Chunk0]
  have hn : (transition2653Raw0 : Multiset ℕ) = 1 • (supportNumbers1694 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1694] using hm

private def transition2654Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 544, 546, 548, 550, 609, 611, 613, 615, 681, 683, 685, 687, 744, 746, 748, 750]
private def transition2654Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 288, 290, 292, 294, 353, 355, 357, 359, 425, 427, 429, 431, 488, 490, 492, 494]
private theorem transition2654Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2654Input0) = fromList transition2654Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2654 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1694 = 1 • support1571 := by
  have hs : support1694 = fromList transition2654Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2654Chunk0]
  have hn : (transition2654Raw0 : Multiset ℕ) = 1 • (supportNumbers1571 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1571] using hm

private def transition2655Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 544, 546, 548, 550, 609, 611, 613, 615, 681, 683, 685, 687, 744, 746, 748, 750]
private def transition2655Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 137, 713, 139, 715, 141, 717, 143, 719, 200, 648, 202, 650, 204, 652, 206, 654, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition2655Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2655Input0) = fromList transition2655Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2655 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1694 = 1 • support1573 := by
  have hs : support1694 = fromList transition2655Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2655Chunk0]
  have hn : (transition2655Raw0 : Multiset ℕ) = 1 • (supportNumbers1573 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1573] using hm

private def transition2656Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 256, 258, 260, 262, 321, 323, 325, 327, 393, 395, 397, 399, 456, 458, 460, 462, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711, 777, 779, 781, 783, 840, 842, 844, 846, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition2656Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition2656Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2656Input0) = fromList transition2656Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2656 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0387 = 2 • support0439 := by
  have hs : support0387 = fromList transition2656Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2656Chunk0]
  have hn : (transition2656Raw0 : Multiset ℕ) = 2 • (supportNumbers0439 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0439] using hm

private def transition2657Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 256, 258, 260, 262, 321, 323, 325, 327, 393, 395, 397, 399, 456, 458, 460, 462, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711, 777, 779, 781, 783, 840, 842, 844, 846, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition2657Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 137, 521, 139, 523, 141, 525, 143, 527, 200, 584, 202, 586, 204, 588, 206, 590, 0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 137, 521, 139, 523, 141, 525, 143, 527, 200, 584, 202, 586, 204, 588, 206, 590, 265, 905, 267, 907, 269, 909, 271, 911, 328, 968, 330, 970, 332, 972, 334, 974, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 265, 905, 267, 907, 269, 909, 271, 911, 328, 968, 330, 970, 332, 972, 334, 974, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839]
private theorem transition2657Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2657Input0) = fromList transition2657Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2657 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0387 = 2 • support0440 := by
  have hs : support0387 = fromList transition2657Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2657Chunk0]
  have hn : (transition2657Raw0 : Multiset ℕ) = 2 • (supportNumbers0440 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0440] using hm

private def transition2658Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 256, 258, 260, 262, 321, 323, 325, 327, 393, 395, 397, 399, 456, 458, 460, 462, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711, 777, 779, 781, 783, 840, 842, 844, 846, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition2658Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition2658Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2658Input0) = fromList transition2658Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2658 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0387 = 2 • support0439 := by
  have hs : support0387 = fromList transition2658Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2658Chunk0]
  have hn : (transition2658Raw0 : Multiset ℕ) = 2 • (supportNumbers0439 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0439] using hm

private def transition2659Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 256, 258, 260, 262, 321, 323, 325, 327, 393, 395, 397, 399, 456, 458, 460, 462, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711, 777, 779, 781, 783, 840, 842, 844, 846, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition2659Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 137, 681, 139, 683, 141, 685, 143, 687, 200, 744, 202, 746, 204, 748, 206, 750, 0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 137, 681, 139, 683, 141, 685, 143, 687, 200, 744, 202, 746, 204, 748, 206, 750, 265, 809, 267, 811, 269, 813, 271, 815, 328, 872, 330, 874, 332, 876, 334, 878, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 265, 809, 267, 811, 269, 813, 271, 815, 328, 872, 330, 874, 332, 876, 334, 878, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999]
private theorem transition2659Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2659Input0) = fromList transition2659Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2659 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0387 = 2 • support1693 := by
  have hs : support0387 = fromList transition2659Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2659Chunk0]
  have hn : (transition2659Raw0 : Multiset ℕ) = 2 • (supportNumbers1693 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1693] using hm

private def transition2660Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private def transition2660Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private theorem transition2660Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2660Input0) = fromList transition2660Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2660 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0388 = 1 • support0299 := by
  have hs : support0388 = fromList transition2660Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2660Chunk0]
  have hn : (transition2660Raw0 : Multiset ℕ) = 1 • (supportNumbers0299 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0299] using hm

private def transition2661Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private def transition2661Raw0 : List ℕ := [0, 2, 4, 6, 649, 651, 653, 655, 65, 67, 69, 71, 712, 714, 716, 718, 128, 130, 132, 134, 521, 523, 525, 527, 193, 195, 197, 199, 584, 586, 588, 590]
private theorem transition2661Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2661Input0) = fromList transition2661Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2661 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0388 = 1 • support0442 := by
  have hs : support0388 = fromList transition2661Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2661Chunk0]
  have hn : (transition2661Raw0 : Multiset ℕ) = 1 • (supportNumbers0442 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0442] using hm

private def transition2662Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private def transition2662Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private theorem transition2662Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2662Input0) = fromList transition2662Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2662 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0388 = 1 • support0299 := by
  have hs : support0388 = fromList transition2662Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2662Chunk0]
  have hn : (transition2662Raw0 : Multiset ℕ) = 1 • (supportNumbers0299 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0299] using hm

private def transition2663Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private def transition2663Raw0 : List ℕ := [0, 2, 4, 6, 553, 555, 557, 559, 65, 67, 69, 71, 616, 618, 620, 622, 128, 130, 132, 134, 681, 683, 685, 687, 193, 195, 197, 199, 744, 746, 748, 750]
private theorem transition2663Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2663Input0) = fromList transition2663Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2663 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0388 = 1 • support1695 := by
  have hs : support0388 = fromList transition2663Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2663Chunk0]
  have hn : (transition2663Raw0 : Multiset ℕ) = 1 • (supportNumbers1695 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1695] using hm

private def transition2664Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 553, 555, 557, 559, 616, 618, 620, 622, 681, 683, 685, 687, 744, 746, 748, 750]
private def transition2664Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 297, 299, 301, 303, 360, 362, 364, 366, 425, 427, 429, 431, 488, 490, 492, 494]
private theorem transition2664Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2664Input0) = fromList transition2664Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2664 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1695 = 1 • support1696 := by
  have hs : support1695 = fromList transition2664Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2664Chunk0]
  have hn : (transition2664Raw0 : Multiset ℕ) = 1 • (supportNumbers1696 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1696] using hm

private def transition2665Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 553, 555, 557, 559, 616, 618, 620, 622, 681, 683, 685, 687, 744, 746, 748, 750]
private def transition2665Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 128, 704, 130, 706, 132, 708, 134, 710, 193, 641, 195, 643, 197, 645, 199, 647, 297, 873, 299, 875, 301, 877, 303, 879, 360, 808, 362, 810, 364, 812, 366, 814, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition2665Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2665Input0) = fromList transition2665Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2665 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1695 = 1 • support1698 := by
  have hs : support1695 = fromList transition2665Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2665Chunk0]
  have hn : (transition2665Raw0 : Multiset ℕ) = 1 • (supportNumbers1698 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1698] using hm

private def transition2666Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 512, 514, 516, 518, 521, 523, 525, 527, 577, 579, 581, 583, 584, 586, 588, 590, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718]
private def transition2666Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private theorem transition2666Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2666Input0) = fromList transition2666Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2666 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0389 = 1 • support0308 := by
  have hs : support0389 = fromList transition2666Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2666Chunk0]
  have hn : (transition2666Raw0 : Multiset ℕ) = 1 • (supportNumbers0308 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0308] using hm

private def transition2667Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 512, 514, 516, 518, 521, 523, 525, 527, 577, 579, 581, 583, 584, 586, 588, 590, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718]
private def transition2667Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718, 128, 512, 130, 514, 132, 516, 134, 518, 137, 521, 139, 523, 141, 525, 143, 527, 193, 577, 195, 579, 197, 581, 199, 583, 200, 584, 202, 586, 204, 588, 206, 590, 256, 896, 258, 898, 260, 900, 262, 902, 265, 905, 267, 907, 269, 909, 271, 911, 321, 961, 323, 963, 325, 965, 327, 967, 328, 968, 330, 970, 332, 972, 334, 974, 384, 768, 386, 770, 388, 772, 390, 774, 393, 777, 395, 779, 397, 781, 399, 783, 449, 833, 451, 835, 453, 837, 455, 839, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition2667Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2667Input0) = fromList transition2667Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2667 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0389 = 1 • support0309 := by
  have hs : support0389 = fromList transition2667Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2667Chunk0]
  have hn : (transition2667Raw0 : Multiset ℕ) = 1 • (supportNumbers0309 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0309] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
