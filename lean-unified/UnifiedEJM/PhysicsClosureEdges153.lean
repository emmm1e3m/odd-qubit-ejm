import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2719Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition2719Raw0 : List ℕ := [0, 2, 4, 6, 552, 554, 556, 558, 65, 67, 69, 71, 617, 619, 621, 623, 129, 131, 133, 135, 681, 683, 685, 687, 192, 194, 196, 198, 744, 746, 748, 750, 544, 546, 548, 550, 8, 10, 12, 14, 609, 611, 613, 615, 73, 75, 77, 79, 673, 675, 677, 679, 137, 139, 141, 143, 736, 738, 740, 742, 200, 202, 204, 206]
private theorem transition2719Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2719Input0) = fromList transition2719Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2719 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0399 = 1 • support1593 := by
  have hs : support0399 = fromList transition2719Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2719Chunk0]
  have hn : (transition2719Raw0 : Multiset ℕ) = 1 • (supportNumbers1593 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1593] using hm

private def transition2720Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition2720Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private theorem transition2720Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2720Input0) = fromList transition2720Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2720Input1 : List ℕ := [513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 769, 771, 773, 775, 777, 779, 781, 783, 832, 834, 836, 838, 840, 842, 844, 846, 896, 898, 900, 902, 904, 906, 908, 910, 961, 963, 965, 967, 969, 971, 973, 975]
private def transition2720Raw1 : List ℕ := [257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private theorem transition2720Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2720Input1) = fromList transition2720Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2720 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0400 = 2 • support0042 := by
  have hs : support0400 = fromList transition2720Input0 + fromList transition2720Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2720Chunk0, transition2720Chunk1]
  have hn : (transition2720Raw0 : Multiset ℕ) + (transition2720Raw1 : Multiset ℕ) = 2 • (supportNumbers0042 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0042] using hm

private def transition2721Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition2721Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 129, 513, 131, 515, 133, 517, 135, 519, 137, 521, 139, 523, 141, 525, 143, 527, 192, 576, 194, 578, 196, 580, 198, 582, 200, 584, 202, 586, 204, 588, 206, 590, 0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 129, 513, 131, 515, 133, 517, 135, 519, 137, 521, 139, 523, 141, 525, 143, 527, 192, 576, 194, 578, 196, 580, 198, 582, 200, 584, 202, 586, 204, 588, 206, 590]
private theorem transition2721Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2721Input0) = fromList transition2721Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2721Input1 : List ℕ := [513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 769, 771, 773, 775, 777, 779, 781, 783, 832, 834, 836, 838, 840, 842, 844, 846, 896, 898, 900, 902, 904, 906, 908, 910, 961, 963, 965, 967, 969, 971, 973, 975]
private def transition2721Raw1 : List ℕ := [257, 897, 259, 899, 261, 901, 263, 903, 265, 905, 267, 907, 269, 909, 271, 911, 320, 960, 322, 962, 324, 964, 326, 966, 328, 968, 330, 970, 332, 972, 334, 974, 384, 768, 386, 770, 388, 772, 390, 774, 392, 776, 394, 778, 396, 780, 398, 782, 449, 833, 451, 835, 453, 837, 455, 839, 457, 841, 459, 843, 461, 845, 463, 847, 257, 897, 259, 899, 261, 901, 263, 903, 265, 905, 267, 907, 269, 909, 271, 911, 320, 960, 322, 962, 324, 964, 326, 966, 328, 968, 330, 970, 332, 972, 334, 974, 384, 768, 386, 770, 388, 772, 390, 774, 392, 776, 394, 778, 396, 780, 398, 782, 449, 833, 451, 835, 453, 837, 455, 839, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition2721Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2721Input1) = fromList transition2721Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2721 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0400 = 2 • support0043 := by
  have hs : support0400 = fromList transition2721Input0 + fromList transition2721Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2721Chunk0, transition2721Chunk1]
  have hn : (transition2721Raw0 : Multiset ℕ) + (transition2721Raw1 : Multiset ℕ) = 2 • (supportNumbers0043 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0043] using hm

private def transition2722Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition2722Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private theorem transition2722Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2722Input0) = fromList transition2722Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2722Input1 : List ℕ := [513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 769, 771, 773, 775, 777, 779, 781, 783, 832, 834, 836, 838, 840, 842, 844, 846, 896, 898, 900, 902, 904, 906, 908, 910, 961, 963, 965, 967, 969, 971, 973, 975]
private def transition2722Raw1 : List ℕ := [257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463, 257, 259, 261, 263, 265, 267, 269, 271, 320, 322, 324, 326, 328, 330, 332, 334, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private theorem transition2722Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2722Input1) = fromList transition2722Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2722 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0400 = 2 • support0042 := by
  have hs : support0400 = fromList transition2722Input0 + fromList transition2722Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2722Chunk0, transition2722Chunk1]
  have hn : (transition2722Raw0 : Multiset ℕ) + (transition2722Raw1 : Multiset ℕ) = 2 • (supportNumbers0042 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0042] using hm

private def transition2723Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition2723Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623, 129, 673, 131, 675, 133, 677, 135, 679, 137, 681, 139, 683, 141, 685, 143, 687, 192, 736, 194, 738, 196, 740, 198, 742, 200, 744, 202, 746, 204, 748, 206, 750, 0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623, 129, 673, 131, 675, 133, 677, 135, 679, 137, 681, 139, 683, 141, 685, 143, 687, 192, 736, 194, 738, 196, 740, 198, 742, 200, 744, 202, 746, 204, 748, 206, 750]
private theorem transition2723Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2723Input0) = fromList transition2723Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2723Input1 : List ℕ := [513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 769, 771, 773, 775, 777, 779, 781, 783, 832, 834, 836, 838, 840, 842, 844, 846, 896, 898, 900, 902, 904, 906, 908, 910, 961, 963, 965, 967, 969, 971, 973, 975]
private def transition2723Raw1 : List ℕ := [257, 801, 259, 803, 261, 805, 263, 807, 265, 809, 267, 811, 269, 813, 271, 815, 320, 864, 322, 866, 324, 868, 326, 870, 328, 872, 330, 874, 332, 876, 334, 878, 384, 928, 386, 930, 388, 932, 390, 934, 392, 936, 394, 938, 396, 940, 398, 942, 449, 993, 451, 995, 453, 997, 455, 999, 457, 1001, 459, 1003, 461, 1005, 463, 1007, 257, 801, 259, 803, 261, 805, 263, 807, 265, 809, 267, 811, 269, 813, 271, 815, 320, 864, 322, 866, 324, 868, 326, 870, 328, 872, 330, 874, 332, 876, 334, 878, 384, 928, 386, 930, 388, 932, 390, 934, 392, 936, 394, 938, 396, 940, 398, 942, 449, 993, 451, 995, 453, 997, 455, 999, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition2723Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2723Input1) = fromList transition2723Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2723 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0400 = 2 • support0615 := by
  have hs : support0400 = fromList transition2723Input0 + fromList transition2723Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2723Chunk0, transition2723Chunk1]
  have hn : (transition2723Raw0 : Multiset ℕ) + (transition2723Raw1 : Multiset ℕ) = 2 • (supportNumbers0615 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0615] using hm

private def transition2724Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711]
private def transition2724Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private theorem transition2724Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2724Input0) = fromList transition2724Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2724 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0401 = 1 • support0320 := by
  have hs : support0401 = fromList transition2724Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2724Chunk0]
  have hn : (transition2724Raw0 : Multiset ℕ) = 1 • (supportNumbers0320 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0320] using hm

private def transition2725Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711]
private def transition2725Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 128, 512, 129, 513, 130, 514, 131, 515, 132, 516, 133, 517, 134, 518, 135, 519, 192, 576, 193, 577, 194, 578, 195, 579, 196, 580, 197, 581, 198, 582, 199, 583, 256, 896, 257, 897, 258, 898, 259, 899, 260, 900, 261, 901, 262, 902, 263, 903, 320, 960, 321, 961, 322, 962, 323, 963, 324, 964, 325, 965, 326, 966, 327, 967, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839]
private theorem transition2725Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2725Input0) = fromList transition2725Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2725 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0401 = 1 • support0321 := by
  have hs : support0401 = fromList transition2725Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2725Chunk0]
  have hn : (transition2725Raw0 : Multiset ℕ) = 1 • (supportNumbers0321 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0321] using hm

private def transition2726Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711]
private def transition2726Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private theorem transition2726Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2726Input0) = fromList transition2726Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2726 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0401 = 1 • support0320 := by
  have hs : support0401 = fromList transition2726Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2726Chunk0]
  have hn : (transition2726Raw0 : Multiset ℕ) = 1 • (supportNumbers0320 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0320] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
