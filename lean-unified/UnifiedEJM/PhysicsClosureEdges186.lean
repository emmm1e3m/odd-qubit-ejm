import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition3144Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition3144Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition3144Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3144Input0) = fromList transition3144Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition3144Input1 : List ℕ := [528, 529, 530, 531, 532, 533, 534, 535, 592, 593, 594, 595, 596, 597, 598, 599, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 792, 793, 794, 795, 796, 797, 798, 799, 856, 857, 858, 859, 860, 861, 862, 863, 904, 905, 906, 907, 908, 909, 910, 911, 968, 969, 970, 971, 972, 973, 974, 975]
private def transition3144Raw1 : List ℕ := [272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private theorem transition3144Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3144Input1) = fromList transition3144Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3144 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0473 = 1 • support0335 := by
  have hs : support0473 = fromList transition3144Input0 + fromList transition3144Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3144Chunk0, transition3144Chunk1]
  have hn : (transition3144Raw0 : Multiset ℕ) + (transition3144Raw1 : Multiset ℕ) = 1 • (supportNumbers0335 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0335] using hm

private def transition3145Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition3145Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 144, 688, 145, 689, 146, 690, 147, 691, 148, 692, 149, 693, 150, 694, 151, 695, 208, 752, 209, 753, 210, 754, 211, 755, 212, 756, 213, 757, 214, 758, 215, 759, 8, 552, 9, 553, 10, 554, 11, 555, 12, 556, 13, 557, 14, 558, 15, 559, 72, 616, 73, 617, 74, 618, 75, 619, 76, 620, 77, 621, 78, 622, 79, 623, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition3145Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3145Input0) = fromList transition3145Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition3145Input1 : List ℕ := [528, 529, 530, 531, 532, 533, 534, 535, 592, 593, 594, 595, 596, 597, 598, 599, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 792, 793, 794, 795, 796, 797, 798, 799, 856, 857, 858, 859, 860, 861, 862, 863, 904, 905, 906, 907, 908, 909, 910, 911, 968, 969, 970, 971, 972, 973, 974, 975]
private def transition3145Raw1 : List ℕ := [272, 816, 273, 817, 274, 818, 275, 819, 276, 820, 277, 821, 278, 822, 279, 823, 336, 880, 337, 881, 338, 882, 339, 883, 340, 884, 341, 885, 342, 886, 343, 887, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007]
private theorem transition3145Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3145Input1) = fromList transition3145Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3145 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0473 = 1 • support1459 := by
  have hs : support0473 = fromList transition3145Input0 + fromList transition3145Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3145Chunk0, transition3145Chunk1]
  have hn : (transition3145Raw0 : Multiset ℕ) + (transition3145Raw1 : Multiset ℕ) = 1 • (supportNumbers1459 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1459] using hm

private def transition3146Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334]
private def transition3146Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 9, 11, 13, 15, 72, 74, 76, 78]
private theorem transition3146Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3146Input0) = fromList transition3146Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3146 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0474 = 1 • support0217 := by
  have hs : support0474 = fromList transition3146Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3146Chunk0]
  have hn : (transition3146Raw0 : Multiset ℕ) = 1 • (supportNumbers0217 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0217] using hm

private def transition3147Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334]
private def transition3147Raw0 : List ℕ := [0, 2, 4, 6, 649, 651, 653, 655, 65, 67, 69, 71, 712, 714, 716, 718, 640, 642, 644, 646, 9, 11, 13, 15, 705, 707, 709, 711, 72, 74, 76, 78]
private theorem transition3147Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3147Input0) = fromList transition3147Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3147 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0474 = 1 • support0306 := by
  have hs : support0474 = fromList transition3147Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3147Chunk0]
  have hn : (transition3147Raw0 : Multiset ℕ) = 1 • (supportNumbers0306 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0306] using hm

private def transition3148Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334]
private def transition3148Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 9, 11, 13, 15, 72, 74, 76, 78]
private theorem transition3148Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3148Input0) = fromList transition3148Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3148 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0474 = 1 • support0217 := by
  have hs : support0474 = fromList transition3148Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3148Chunk0]
  have hn : (transition3148Raw0 : Multiset ℕ) = 1 • (supportNumbers0217 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0217] using hm

private def transition3149Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334]
private def transition3149Raw0 : List ℕ := [0, 2, 4, 6, 553, 555, 557, 559, 65, 67, 69, 71, 616, 618, 620, 622, 544, 546, 548, 550, 9, 11, 13, 15, 609, 611, 613, 615, 72, 74, 76, 78]
private theorem transition3149Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3149Input0) = fromList transition3149Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3149 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0474 = 1 • support1390 := by
  have hs : support0474 = fromList transition3149Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3149Chunk0]
  have hn : (transition3149Raw0 : Multiset ℕ) = 1 • (supportNumbers1390 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1390] using hm

private def transition3150Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 896, 898, 900, 902, 905, 907, 909, 911, 961, 963, 965, 967, 968, 970, 972, 974]
private def transition3150Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private theorem transition3150Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3150Input0) = fromList transition3150Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3150 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0475 = 2 • support0218 := by
  have hs : support0475 = fromList transition3150Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3150Chunk0]
  have hn : (transition3150Raw0 : Multiset ℕ) = 2 • (supportNumbers0218 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0218] using hm

private def transition3151Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 896, 898, 900, 902, 905, 907, 909, 911, 961, 963, 965, 967, 968, 970, 972, 974]
private def transition3151Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718, 0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718, 384, 768, 386, 770, 388, 772, 390, 774, 393, 777, 395, 779, 397, 781, 399, 783, 449, 833, 451, 835, 453, 837, 455, 839, 456, 840, 458, 842, 460, 844, 462, 846, 384, 768, 386, 770, 388, 772, 390, 774, 393, 777, 395, 779, 397, 781, 399, 783, 449, 833, 451, 835, 453, 837, 455, 839, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition3151Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3151Input0) = fromList transition3151Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3151 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0475 = 2 • support0219 := by
  have hs : support0475 = fromList transition3151Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3151Chunk0]
  have hn : (transition3151Raw0 : Multiset ℕ) = 2 • (supportNumbers0219 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0219] using hm

private def transition3152Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 896, 898, 900, 902, 905, 907, 909, 911, 961, 963, 965, 967, 968, 970, 972, 974]
private def transition3152Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private theorem transition3152Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3152Input0) = fromList transition3152Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3152 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0475 = 2 • support0218 := by
  have hs : support0475 = fromList transition3152Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3152Chunk0]
  have hn : (transition3152Raw0 : Multiset ℕ) = 2 • (supportNumbers0218 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0218] using hm

private def transition3153Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 896, 898, 900, 902, 905, 907, 909, 911, 961, 963, 965, 967, 968, 970, 972, 974]
private def transition3153Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 9, 553, 11, 555, 13, 557, 15, 559, 65, 609, 67, 611, 69, 613, 71, 615, 72, 616, 74, 618, 76, 620, 78, 622, 0, 544, 2, 546, 4, 548, 6, 550, 9, 553, 11, 555, 13, 557, 15, 559, 65, 609, 67, 611, 69, 613, 71, 615, 72, 616, 74, 618, 76, 620, 78, 622, 384, 928, 386, 930, 388, 932, 390, 934, 393, 937, 395, 939, 397, 941, 399, 943, 449, 993, 451, 995, 453, 997, 455, 999, 456, 1000, 458, 1002, 460, 1004, 462, 1006, 384, 928, 386, 930, 388, 932, 390, 934, 393, 937, 395, 939, 397, 941, 399, 943, 449, 993, 451, 995, 453, 997, 455, 999, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition3153Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3153Input0) = fromList transition3153Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3153 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0475 = 2 • support1170 := by
  have hs : support0475 = fromList transition3153Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3153Chunk0]
  have hn : (transition3153Raw0 : Multiset ℕ) = 2 • (supportNumbers1170 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1170] using hm

private def transition3154Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition3154Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition3154Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3154Input0) = fromList transition3154Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3154 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0476 = 1 • support0241 := by
  have hs : support0476 = fromList transition3154Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3154Chunk0]
  have hn : (transition3154Raw0 : Multiset ℕ) = 1 • (supportNumbers0241 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0241] using hm

private def transition3155Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition3155Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 528, 529, 530, 531, 532, 533, 534, 535, 592, 593, 594, 595, 596, 597, 598, 599]
private theorem transition3155Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3155Input0) = fromList transition3155Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3155 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0476 = 1 • support0410 := by
  have hs : support0476 = fromList transition3155Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3155Chunk0]
  have hn : (transition3155Raw0 : Multiset ℕ) = 1 • (supportNumbers0410 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0410] using hm

private def transition3156Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition3156Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition3156Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3156Input0) = fromList transition3156Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3156 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0476 = 1 • support0241 := by
  have hs : support0476 = fromList transition3156Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3156Chunk0]
  have hn : (transition3156Raw0 : Multiset ℕ) = 1 • (supportNumbers0241 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0241] using hm

private def transition3157Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition3157Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 688, 689, 690, 691, 692, 693, 694, 695, 752, 753, 754, 755, 756, 757, 758, 759]
private theorem transition3157Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3157Input0) = fromList transition3157Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3157 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0476 = 1 • support1614 := by
  have hs : support0476 = fromList transition3157Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3157Chunk0]
  have hn : (transition3157Raw0 : Multiset ℕ) = 1 • (supportNumbers1614 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1614] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
