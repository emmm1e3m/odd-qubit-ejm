import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2311Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition2311Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 8, 552, 9, 553, 10, 554, 11, 555, 12, 556, 13, 557, 14, 558, 15, 559, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 72, 616, 73, 617, 74, 618, 75, 619, 76, 620, 77, 621, 78, 622, 79, 623, 128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751]
private theorem transition2311Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2311Input0) = fromList transition2311Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2311Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847]
private def transition2311Raw1 : List ℕ := [384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007, 256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879]
private theorem transition2311Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2311Input1) = fromList transition2311Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2311 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0329 = 1 • support0757 := by
  have hs : support0329 = fromList transition2311Input0 + fromList transition2311Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2311Chunk0, transition2311Chunk1]
  have hn : (transition2311Raw0 : Multiset ℕ) + (transition2311Raw1 : Multiset ℕ) = 1 • (supportNumbers0757 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0757] using hm

private def transition2312Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition2312Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79]
private theorem transition2312Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2312Input0) = fromList transition2312Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2312 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0330 = 1 • support0222 := by
  have hs : support0330 = fromList transition2312Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2312Chunk0]
  have hn : (transition2312Raw0 : Multiset ℕ) = 1 • (supportNumbers0222 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0222] using hm

private def transition2313Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition2313Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 536, 537, 538, 539, 540, 541, 542, 543, 600, 601, 602, 603, 604, 605, 606, 607, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79, 528, 529, 530, 531, 532, 533, 534, 535, 592, 593, 594, 595, 596, 597, 598, 599]
private theorem transition2313Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2313Input0) = fromList transition2313Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2313 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0330 = 1 • support0409 := by
  have hs : support0330 = fromList transition2313Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2313Chunk0]
  have hn : (transition2313Raw0 : Multiset ℕ) = 1 • (supportNumbers0409 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0409] using hm

private def transition2314Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition2314Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79]
private theorem transition2314Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2314Input0) = fromList transition2314Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2314 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0330 = 1 • support0222 := by
  have hs : support0330 = fromList transition2314Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2314Chunk0]
  have hn : (transition2314Raw0 : Multiset ℕ) = 1 • (supportNumbers0222 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0222] using hm

private def transition2315Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition2315Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 696, 697, 698, 699, 700, 701, 702, 703, 760, 761, 762, 763, 764, 765, 766, 767, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79, 688, 689, 690, 691, 692, 693, 694, 695, 752, 753, 754, 755, 756, 757, 758, 759]
private theorem transition2315Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2315Input0) = fromList transition2315Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2315 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0330 = 1 • support1610 := by
  have hs : support0330 = fromList transition2315Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2315Chunk0]
  have hn : (transition2315Raw0 : Multiset ℕ) = 1 • (supportNumbers1610 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1610] using hm

private def transition2316Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]
private def transition2316Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]
private theorem transition2316Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2316Input0) = fromList transition2316Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2316 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1610 = 1 • support1611 := by
  have hs : support1610 = fromList transition2316Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2316Chunk0]
  have hn : (transition2316Raw0 : Multiset ℕ) = 1 • (supportNumbers1611 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1611] using hm

private def transition2317Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]
private def transition2317Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 8, 584, 9, 585, 10, 586, 11, 587, 12, 588, 13, 589, 14, 590, 15, 591, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 72, 520, 73, 521, 74, 522, 75, 523, 76, 524, 77, 525, 78, 526, 79, 527, 432, 1008, 433, 1009, 434, 1010, 435, 1011, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 440, 1016, 441, 1017, 442, 1018, 443, 1019, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 496, 944, 497, 945, 498, 946, 499, 947, 500, 948, 501, 949, 502, 950, 503, 951, 504, 952, 505, 953, 506, 954, 507, 955, 508, 956, 509, 957, 510, 958, 511, 959]
private theorem transition2317Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2317Input0) = fromList transition2317Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2317 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1610 = 1 • support1612 := by
  have hs : support1610 = fromList transition2317Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2317Chunk0]
  have hn : (transition2317Raw0 : Multiset ℕ) = 1 • (supportNumbers1612 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1612] using hm

private def transition2318Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition2318Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition2318Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2318Input0) = fromList transition2318Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2318Input1 : List ℕ := [536, 537, 538, 539, 540, 541, 542, 543, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 784, 785, 786, 787, 788, 789, 790, 791, 848, 849, 850, 851, 852, 853, 854, 855, 904, 905, 906, 907, 908, 909, 910, 911, 968, 969, 970, 971, 972, 973, 974, 975]
private def transition2318Raw1 : List ℕ := [280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private theorem transition2318Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2318Input1) = fromList transition2318Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2318 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0331 = 1 • support0335 := by
  have hs : support0331 = fromList transition2318Input0 + fromList transition2318Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2318Chunk0, transition2318Chunk1]
  have hn : (transition2318Raw0 : Multiset ℕ) + (transition2318Raw1 : Multiset ℕ) = 1 • (supportNumbers0335 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0335] using hm

private def transition2319Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition2319Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 152, 536, 153, 537, 154, 538, 155, 539, 156, 540, 157, 541, 158, 542, 159, 543, 216, 600, 217, 601, 218, 602, 219, 603, 220, 604, 221, 605, 222, 606, 223, 607, 8, 648, 9, 649, 10, 650, 11, 651, 12, 652, 13, 653, 14, 654, 15, 655, 72, 712, 73, 713, 74, 714, 75, 715, 76, 716, 77, 717, 78, 718, 79, 719, 144, 528, 145, 529, 146, 530, 147, 531, 148, 532, 149, 533, 150, 534, 151, 535, 208, 592, 209, 593, 210, 594, 211, 595, 212, 596, 213, 597, 214, 598, 215, 599]
private theorem transition2319Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2319Input0) = fromList transition2319Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2319Input1 : List ℕ := [536, 537, 538, 539, 540, 541, 542, 543, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 784, 785, 786, 787, 788, 789, 790, 791, 848, 849, 850, 851, 852, 853, 854, 855, 904, 905, 906, 907, 908, 909, 910, 911, 968, 969, 970, 971, 972, 973, 974, 975]
private def transition2319Raw1 : List ℕ := [280, 920, 281, 921, 282, 922, 283, 923, 284, 924, 285, 925, 286, 926, 287, 927, 344, 984, 345, 985, 346, 986, 347, 987, 348, 988, 349, 989, 350, 990, 351, 991, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 272, 912, 273, 913, 274, 914, 275, 915, 276, 916, 277, 917, 278, 918, 279, 919, 336, 976, 337, 977, 338, 978, 339, 979, 340, 980, 341, 981, 342, 982, 343, 983, 392, 776, 393, 777, 394, 778, 395, 779, 396, 780, 397, 781, 398, 782, 399, 783, 456, 840, 457, 841, 458, 842, 459, 843, 460, 844, 461, 845, 462, 846, 463, 847]
private theorem transition2319Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2319Input1) = fromList transition2319Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2319 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0331 = 1 • support0336 := by
  have hs : support0331 = fromList transition2319Input0 + fromList transition2319Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2319Chunk0, transition2319Chunk1]
  have hn : (transition2319Raw0 : Multiset ℕ) + (transition2319Raw1 : Multiset ℕ) = 1 • (supportNumbers0336 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0336] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
