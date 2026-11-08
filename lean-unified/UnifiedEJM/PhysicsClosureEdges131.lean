import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2320Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition2320Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition2320Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2320Input0) = fromList transition2320Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2320Input1 : List ℕ := [536, 537, 538, 539, 540, 541, 542, 543, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 784, 785, 786, 787, 788, 789, 790, 791, 848, 849, 850, 851, 852, 853, 854, 855, 904, 905, 906, 907, 908, 909, 910, 911, 968, 969, 970, 971, 972, 973, 974, 975]
private def transition2320Raw1 : List ℕ := [280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private theorem transition2320Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2320Input1) = fromList transition2320Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2320 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0331 = 1 • support0335 := by
  have hs : support0331 = fromList transition2320Input0 + fromList transition2320Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2320Chunk0, transition2320Chunk1]
  have hn : (transition2320Raw0 : Multiset ℕ) + (transition2320Raw1 : Multiset ℕ) = 1 • (supportNumbers0335 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0335] using hm

private def transition2321Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition2321Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767, 8, 552, 9, 553, 10, 554, 11, 555, 12, 556, 13, 557, 14, 558, 15, 559, 72, 616, 73, 617, 74, 618, 75, 619, 76, 620, 77, 621, 78, 622, 79, 623, 144, 688, 145, 689, 146, 690, 147, 691, 148, 692, 149, 693, 150, 694, 151, 695, 208, 752, 209, 753, 210, 754, 211, 755, 212, 756, 213, 757, 214, 758, 215, 759]
private theorem transition2321Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2321Input0) = fromList transition2321Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2321Input1 : List ℕ := [536, 537, 538, 539, 540, 541, 542, 543, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 784, 785, 786, 787, 788, 789, 790, 791, 848, 849, 850, 851, 852, 853, 854, 855, 904, 905, 906, 907, 908, 909, 910, 911, 968, 969, 970, 971, 972, 973, 974, 975]
private def transition2321Raw1 : List ℕ := [280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 272, 816, 273, 817, 274, 818, 275, 819, 276, 820, 277, 821, 278, 822, 279, 823, 336, 880, 337, 881, 338, 882, 339, 883, 340, 884, 341, 885, 342, 886, 343, 887, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007]
private theorem transition2321Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2321Input1) = fromList transition2321Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2321 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0331 = 1 • support1459 := by
  have hs : support0331 = fromList transition2321Input0 + fromList transition2321Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2321Chunk0, transition2321Chunk1]
  have hn : (transition2321Raw0 : Multiset ℕ) + (transition2321Raw1 : Multiset ℕ) = 1 • (supportNumbers1459 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1459] using hm

private def transition2322Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition2322Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition2322Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2322Input0) = fromList transition2322Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2322 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0241 = 1 • support0241 := by
  have hs : support0241 = fromList transition2322Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2322Chunk0]
  have hn : (transition2322Raw0 : Multiset ℕ) = 1 • (supportNumbers0241 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0241] using hm

private def transition2323Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition2323Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 144, 528, 145, 529, 146, 530, 147, 531, 148, 532, 149, 533, 150, 534, 151, 535, 208, 592, 209, 593, 210, 594, 211, 595, 212, 596, 213, 597, 214, 598, 215, 599]
private theorem transition2323Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2323Input0) = fromList transition2323Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2323 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0241 = 1 • support0410 := by
  have hs : support0241 = fromList transition2323Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2323Chunk0]
  have hn : (transition2323Raw0 : Multiset ℕ) = 1 • (supportNumbers0410 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0410] using hm

private def transition2324Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition2324Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition2324Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2324Input0) = fromList transition2324Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2324 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0241 = 1 • support0241 := by
  have hs : support0241 = fromList transition2324Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2324Chunk0]
  have hn : (transition2324Raw0 : Multiset ℕ) = 1 • (supportNumbers0241 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0241] using hm

private def transition2325Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition2325Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 144, 688, 145, 689, 146, 690, 147, 691, 148, 692, 149, 693, 150, 694, 151, 695, 208, 752, 209, 753, 210, 754, 211, 755, 212, 756, 213, 757, 214, 758, 215, 759]
private theorem transition2325Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2325Input0) = fromList transition2325Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2325 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0241 = 1 • support1614 := by
  have hs : support0241 = fromList transition2325Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2325Chunk0]
  have hn : (transition2325Raw0 : Multiset ℕ) = 1 • (supportNumbers1614 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1614] using hm

private def transition2326Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 688, 689, 690, 691, 692, 693, 694, 695, 752, 753, 754, 755, 756, 757, 758, 759]
private def transition2326Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 432, 433, 434, 435, 436, 437, 438, 439, 496, 497, 498, 499, 500, 501, 502, 503]
private theorem transition2326Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2326Input0) = fromList transition2326Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2326 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1614 = 1 • support1615 := by
  have hs : support1614 = fromList transition2326Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2326Chunk0]
  have hn : (transition2326Raw0 : Multiset ℕ) = 1 • (supportNumbers1615 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1615] using hm

private def transition2327Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 688, 689, 690, 691, 692, 693, 694, 695, 752, 753, 754, 755, 756, 757, 758, 759]
private def transition2327Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 144, 720, 145, 721, 146, 722, 147, 723, 148, 724, 149, 725, 150, 726, 151, 727, 208, 656, 209, 657, 210, 658, 211, 659, 212, 660, 213, 661, 214, 662, 215, 663, 288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 432, 1008, 433, 1009, 434, 1010, 435, 1011, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 496, 944, 497, 945, 498, 946, 499, 947, 500, 948, 501, 949, 502, 950, 503, 951]
private theorem transition2327Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2327Input0) = fromList transition2327Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2327 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1614 = 1 • support1617 := by
  have hs : support1614 = fromList transition2327Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2327Chunk0]
  have hn : (transition2327Raw0 : Multiset ℕ) = 1 • (supportNumbers1617 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1617] using hm

private def transition2328Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition2328Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition2328Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2328Input0) = fromList transition2328Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2328 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0332 = 1 • support0411 := by
  have hs : support0332 = fromList transition2328Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2328Chunk0]
  have hn : (transition2328Raw0 : Multiset ℕ) = 1 • (supportNumbers0411 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0411] using hm

private def transition2329Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition2329Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition2329Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2329Input0) = fromList transition2329Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2329 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0332 = 1 • support0411 := by
  have hs : support0332 = fromList transition2329Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2329Chunk0]
  have hn : (transition2329Raw0 : Multiset ℕ) = 1 • (supportNumbers0411 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0411] using hm

private def transition2330Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition2330Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition2330Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2330Input0) = fromList transition2330Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2330 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0332 = 1 • support0411 := by
  have hs : support0332 = fromList transition2330Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2330Chunk0]
  have hn : (transition2330Raw0 : Multiset ℕ) = 1 • (supportNumbers0411 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0411] using hm

private def transition2331Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition2331Raw0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 136, 137, 140, 141, 144, 145, 148, 149, 200, 201, 204, 205, 208, 209, 212, 213]
private theorem transition2331Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2331Input0) = fromList transition2331Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2331 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0411 = 1 • support1619 := by
  have hs : support0411 = fromList transition2331Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2331Chunk0]
  have hn : (transition2331Raw0 : Multiset ℕ) = 1 • (supportNumbers1619 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1619] using hm

private def transition2332Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition2332Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 24, 25, 602, 603, 28, 29, 606, 607, 64, 65, 514, 515, 68, 69, 518, 519, 88, 89, 538, 539, 92, 93, 542, 543, 136, 137, 714, 715, 140, 141, 718, 719, 144, 145, 722, 723, 148, 149, 726, 727, 200, 201, 650, 651, 204, 205, 654, 655, 208, 209, 658, 659, 212, 213, 662, 663]
private theorem transition2332Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2332Input0) = fromList transition2332Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2332 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0411 = 1 • support1621 := by
  have hs : support0411 = fromList transition2332Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2332Chunk0]
  have hn : (transition2332Raw0 : Multiset ℕ) = 1 • (supportNumbers1621 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1621] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
