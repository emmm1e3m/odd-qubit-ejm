import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2221Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private def transition2221Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623, 129, 673, 131, 675, 133, 677, 135, 679, 137, 681, 139, 683, 141, 685, 143, 687, 192, 736, 194, 738, 196, 740, 198, 742, 200, 744, 202, 746, 204, 748, 206, 750]
private theorem transition2221Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2221Input0) = fromList transition2221Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2221 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0315 = 1 • support1593 := by
  have hs : support0315 = fromList transition2221Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2221Chunk0]
  have hn : (transition2221Raw0 : Multiset ℕ) = 1 • (supportNumbers1593 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1593] using hm

private def transition2222Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623, 673, 675, 677, 679, 681, 683, 685, 687, 736, 738, 740, 742, 744, 746, 748, 750]
private def transition2222Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367, 417, 419, 421, 423, 425, 427, 429, 431, 480, 482, 484, 486, 488, 490, 492, 494]
private theorem transition2222Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2222Input0) = fromList transition2222Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2222 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1593 = 1 • support0524 := by
  have hs : support1593 = fromList transition2222Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2222Chunk0]
  have hn : (transition2222Raw0 : Multiset ℕ) = 1 • (supportNumbers0524 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0524] using hm

private def transition2223Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623, 673, 675, 677, 679, 681, 683, 685, 687, 736, 738, 740, 742, 744, 746, 748, 750]
private def transition2223Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 129, 705, 131, 707, 133, 709, 135, 711, 137, 713, 139, 715, 141, 717, 143, 719, 192, 640, 194, 642, 196, 644, 198, 646, 200, 648, 202, 650, 204, 652, 206, 654, 288, 864, 290, 866, 292, 868, 294, 870, 296, 872, 298, 874, 300, 876, 302, 878, 353, 801, 355, 803, 357, 805, 359, 807, 361, 809, 363, 811, 365, 813, 367, 815, 417, 993, 419, 995, 421, 997, 423, 999, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 480, 928, 482, 930, 484, 932, 486, 934, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition2223Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2223Input0) = fromList transition2223Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2223 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1593 = 1 • support0526 := by
  have hs : support1593 = fromList transition2223Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2223Chunk0]
  have hn : (transition2223Raw0 : Multiset ℕ) = 1 • (supportNumbers0526 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0526] using hm

private def transition2224Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 512, 514, 516, 518, 520, 522, 524, 526, 577, 579, 581, 583, 585, 587, 589, 591, 641, 643, 645, 647, 649, 651, 653, 655, 704, 706, 708, 710, 712, 714, 716, 718]
private def transition2224Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private theorem transition2224Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2224Input0) = fromList transition2224Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2224 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0316 = 1 • support0399 := by
  have hs : support0316 = fromList transition2224Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2224Chunk0]
  have hn : (transition2224Raw0 : Multiset ℕ) = 1 • (supportNumbers0399 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0399] using hm

private def transition2225Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 512, 514, 516, 518, 520, 522, 524, 526, 577, 579, 581, 583, 585, 587, 589, 591, 641, 643, 645, 647, 649, 651, 653, 655, 704, 706, 708, 710, 712, 714, 716, 718]
private def transition2225Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 129, 513, 131, 515, 133, 517, 135, 519, 137, 521, 139, 523, 141, 525, 143, 527, 192, 576, 194, 578, 196, 580, 198, 582, 200, 584, 202, 586, 204, 588, 206, 590, 256, 896, 258, 898, 260, 900, 262, 902, 264, 904, 266, 906, 268, 908, 270, 910, 321, 961, 323, 963, 325, 965, 327, 967, 329, 969, 331, 971, 333, 973, 335, 975, 385, 769, 387, 771, 389, 773, 391, 775, 393, 777, 395, 779, 397, 781, 399, 783, 448, 832, 450, 834, 452, 836, 454, 838, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition2225Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2225Input0) = fromList transition2225Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2225 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0316 = 1 • support0400 := by
  have hs : support0316 = fromList transition2225Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2225Chunk0]
  have hn : (transition2225Raw0 : Multiset ℕ) = 1 • (supportNumbers0400 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0400] using hm

private def transition2226Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 512, 514, 516, 518, 520, 522, 524, 526, 577, 579, 581, 583, 585, 587, 589, 591, 641, 643, 645, 647, 649, 651, 653, 655, 704, 706, 708, 710, 712, 714, 716, 718]
private def transition2226Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private theorem transition2226Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2226Input0) = fromList transition2226Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2226 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0316 = 1 • support0399 := by
  have hs : support0316 = fromList transition2226Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2226Chunk0]
  have hn : (transition2226Raw0 : Multiset ℕ) = 1 • (supportNumbers0399 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0399] using hm

private def transition2227Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition2227Raw0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 129, 133, 137, 141, 192, 196, 200, 204, 2, 6, 10, 14, 67, 71, 75, 79, 131, 135, 139, 143, 194, 198, 202, 206]
private theorem transition2227Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2227Input0) = fromList transition2227Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2227 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0399 = 1 • support0315 := by
  have hs : support0399 = fromList transition2227Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2227Chunk0]
  have hn : (transition2227Raw0 : Multiset ℕ) = 1 • (supportNumbers0315 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0315] using hm

private def transition2228Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition2228Raw0 : List ℕ := [0, 578, 4, 582, 8, 586, 12, 590, 65, 515, 69, 519, 73, 523, 77, 527, 129, 707, 133, 711, 137, 715, 141, 719, 192, 642, 196, 646, 200, 650, 204, 654, 576, 2, 580, 6, 584, 10, 588, 14, 513, 67, 517, 71, 521, 75, 525, 79, 705, 131, 709, 135, 713, 139, 717, 143, 640, 194, 644, 198, 648, 202, 652, 206]
private theorem transition2228Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2228Input0) = fromList transition2228Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2228 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0399 = 1 • support0398 := by
  have hs : support0399 = fromList transition2228Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2228Chunk0]
  have hn : (transition2228Raw0 : Multiset ℕ) = 1 • (supportNumbers0398 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0398] using hm

private def transition2229Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 512, 514, 516, 518, 520, 522, 524, 526, 577, 579, 581, 583, 585, 587, 589, 591, 641, 643, 645, 647, 649, 651, 653, 655, 704, 706, 708, 710, 712, 714, 716, 718]
private def transition2229Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623, 129, 673, 131, 675, 133, 677, 135, 679, 137, 681, 139, 683, 141, 685, 143, 687, 192, 736, 194, 738, 196, 740, 198, 742, 200, 744, 202, 746, 204, 748, 206, 750, 256, 800, 258, 802, 260, 804, 262, 806, 264, 808, 266, 810, 268, 812, 270, 814, 321, 865, 323, 867, 325, 869, 327, 871, 329, 873, 331, 875, 333, 877, 335, 879, 385, 929, 387, 931, 389, 933, 391, 935, 393, 937, 395, 939, 397, 941, 399, 943, 448, 992, 450, 994, 452, 996, 454, 998, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition2229Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2229Input0) = fromList transition2229Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2229 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0316 = 1 • support1594 := by
  have hs : support0316 = fromList transition2229Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2229Chunk0]
  have hn : (transition2229Raw0 : Multiset ℕ) = 1 • (supportNumbers1594 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1594] using hm

private def transition2230Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition2230Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private theorem transition2230Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2230Input0) = fromList transition2230Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2230Input1 : List ℕ := [544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623, 673, 675, 677, 679, 681, 683, 685, 687, 736, 738, 740, 742, 744, 746, 748, 750, 800, 802, 804, 806, 808, 810, 812, 814, 865, 867, 869, 871, 873, 875, 877, 879, 929, 931, 933, 935, 937, 939, 941, 943, 992, 994, 996, 998, 1000, 1002, 1004, 1006]
private def transition2230Raw1 : List ℕ := [288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367, 417, 419, 421, 423, 425, 427, 429, 431, 480, 482, 484, 486, 488, 490, 492, 494, 288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367, 417, 419, 421, 423, 425, 427, 429, 431, 480, 482, 484, 486, 488, 490, 492, 494]
private theorem transition2230Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2230Input1) = fromList transition2230Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2230 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1594 = 2 • support0524 := by
  have hs : support1594 = fromList transition2230Input0 + fromList transition2230Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2230Chunk0, transition2230Chunk1]
  have hn : (transition2230Raw0 : Multiset ℕ) + (transition2230Raw1 : Multiset ℕ) = 2 • (supportNumbers0524 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0524] using hm

private def transition2231Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition2231Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 129, 705, 131, 707, 133, 709, 135, 711, 137, 713, 139, 715, 141, 717, 143, 719, 192, 640, 194, 642, 196, 644, 198, 646, 200, 648, 202, 650, 204, 652, 206, 654, 0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 129, 705, 131, 707, 133, 709, 135, 711, 137, 713, 139, 715, 141, 717, 143, 719, 192, 640, 194, 642, 196, 644, 198, 646, 200, 648, 202, 650, 204, 652, 206, 654]
private theorem transition2231Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2231Input0) = fromList transition2231Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2231Input1 : List ℕ := [544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623, 673, 675, 677, 679, 681, 683, 685, 687, 736, 738, 740, 742, 744, 746, 748, 750, 800, 802, 804, 806, 808, 810, 812, 814, 865, 867, 869, 871, 873, 875, 877, 879, 929, 931, 933, 935, 937, 939, 941, 943, 992, 994, 996, 998, 1000, 1002, 1004, 1006]
private def transition2231Raw1 : List ℕ := [288, 864, 290, 866, 292, 868, 294, 870, 296, 872, 298, 874, 300, 876, 302, 878, 353, 801, 355, 803, 357, 805, 359, 807, 361, 809, 363, 811, 365, 813, 367, 815, 417, 993, 419, 995, 421, 997, 423, 999, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 480, 928, 482, 930, 484, 932, 486, 934, 488, 936, 490, 938, 492, 940, 494, 942, 288, 864, 290, 866, 292, 868, 294, 870, 296, 872, 298, 874, 300, 876, 302, 878, 353, 801, 355, 803, 357, 805, 359, 807, 361, 809, 363, 811, 365, 813, 367, 815, 417, 993, 419, 995, 421, 997, 423, 999, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 480, 928, 482, 930, 484, 932, 486, 934, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition2231Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2231Input1) = fromList transition2231Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2231 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1594 = 2 • support0526 := by
  have hs : support1594 = fromList transition2231Input0 + fromList transition2231Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2231Chunk0, transition2231Chunk1]
  have hn : (transition2231Raw0 : Multiset ℕ) + (transition2231Raw1 : Multiset ℕ) = 2 • (supportNumbers0526 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0526] using hm

private def transition2232Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private def transition2232Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition2232Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2232Input0) = fromList transition2232Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2232 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0229 = 1 • support0229 := by
  have hs : support0229 = fromList transition2232Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2232Chunk0]
  have hn : (transition2232Raw0 : Multiset ℕ) = 1 • (supportNumbers0229 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0229] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
