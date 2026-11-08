import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0715Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition0715Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 24, 568, 25, 569, 26, 570, 27, 571, 28, 572, 29, 573, 30, 574, 31, 575, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 88, 632, 89, 633, 90, 634, 91, 635, 92, 636, 93, 637, 94, 638, 95, 639, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 144, 688, 145, 689, 146, 690, 147, 691, 148, 692, 149, 693, 150, 694, 151, 695, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 208, 752, 209, 753, 210, 754, 211, 755, 212, 756, 213, 757, 214, 758, 215, 759]
private theorem transition0715Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0715Input0) = fromList transition0715Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0715Input1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0715Raw1 : List ℕ := [8, 552, 9, 553, 10, 554, 11, 555, 12, 556, 13, 557, 14, 558, 15, 559, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 72, 616, 73, 617, 74, 618, 75, 619, 76, 620, 77, 621, 78, 622, 79, 623, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition0715Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0715Input1) = fromList transition0715Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0715Input2 : List ℕ := [520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition0715Raw2 : List ℕ := [264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 272, 816, 273, 817, 274, 818, 275, 819, 276, 820, 277, 821, 278, 822, 279, 823, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879, 336, 880, 337, 881, 338, 882, 339, 883, 340, 884, 341, 885, 342, 886, 343, 887, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 408, 952, 409, 953, 410, 954, 411, 955, 412, 956, 413, 957, 414, 958, 415, 959, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 472, 1016, 473, 1017, 474, 1018, 475, 1019, 476, 1020, 477, 1021, 478, 1022, 479, 1023]
private theorem transition0715Chunk2 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0715Input2) = fromList transition0715Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0715Input3 : List ℕ := [768, 769, 770, 771, 772, 773, 774, 775, 792, 793, 794, 795, 796, 797, 798, 799, 832, 833, 834, 835, 836, 837, 838, 839, 856, 857, 858, 859, 860, 861, 862, 863, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983]
private def transition0715Raw3 : List ℕ := [256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015]
private theorem transition0715Chunk3 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0715Input3) = fromList transition0715Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0715 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0091 = 1 • support0643 := by
  have hs : support0091 = fromList transition0715Input0 + fromList transition0715Input1 + fromList transition0715Input2 + fromList transition0715Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0715Chunk0, transition0715Chunk1, transition0715Chunk2, transition0715Chunk3]
  have hn : (transition0715Raw0 : Multiset ℕ) + (transition0715Raw1 : Multiset ℕ) + (transition0715Raw2 : Multiset ℕ) + (transition0715Raw3 : Multiset ℕ) = 1 • (supportNumbers0643 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0643] using hm

private def transition0716Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private def transition0716Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private theorem transition0716Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0716Input0) = fromList transition0716Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0716 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0092 = 1 • support0092 := by
  have hs : support0092 = fromList transition0716Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0716Chunk0]
  have hn : (transition0716Raw0 : Multiset ℕ) = 1 • (supportNumbers0092 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0092] using hm

private def transition0717Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private def transition0717Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private theorem transition0717Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0717Input0) = fromList transition0717Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0717 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0092 = 1 • support0092 := by
  have hs : support0092 = fromList transition0717Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0717Chunk0]
  have hn : (transition0717Raw0 : Multiset ℕ) = 1 • (supportNumbers0092 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0092] using hm

private def transition0718Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private def transition0718Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private theorem transition0718Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0718Input0) = fromList transition0718Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0718 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0092 = 1 • support0092 := by
  have hs : support0092 = fromList transition0718Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0718Chunk0]
  have hn : (transition0718Raw0 : Multiset ℕ) = 1 • (supportNumbers0092 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0092] using hm

private def transition0719Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private def transition0719Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private theorem transition0719Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0719Input0) = fromList transition0719Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0719 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0092 = 1 • support0092 := by
  have hs : support0092 = fromList transition0719Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0719Chunk0]
  have hn : (transition0719Raw0 : Multiset ℕ) = 1 • (supportNumbers0092 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0092] using hm

private def transition0720Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private def transition0720Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private theorem transition0720Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0720Input0) = fromList transition0720Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0720 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0092 = 1 • support0092 := by
  have hs : support0092 = fromList transition0720Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0720Chunk0]
  have hn : (transition0720Raw0 : Multiset ℕ) = 1 • (supportNumbers0092 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0092] using hm

private def transition0721Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private def transition0721Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 16, 592, 17, 593, 18, 594, 19, 595, 20, 596, 21, 597, 22, 598, 23, 599, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 80, 528, 81, 529, 82, 530, 83, 531, 84, 532, 85, 533, 86, 534, 87, 535]
private theorem transition0721Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0721Input0) = fromList transition0721Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0721 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0092 = 1 • support0413 := by
  have hs : support0092 = fromList transition0721Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0721Chunk0]
  have hn : (transition0721Raw0 : Multiset ℕ) = 1 • (supportNumbers0413 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0413] using hm

private def transition0722Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 520, 521, 522, 523, 524, 525, 526, 527, 536, 537, 538, 539, 540, 541, 542, 543, 584, 585, 586, 587, 588, 589, 590, 591, 600, 601, 602, 603, 604, 605, 606, 607]
private def transition0722Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351]
private theorem transition0722Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0722Input0) = fromList transition0722Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0722 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0093 = 1 • support0159 := by
  have hs : support0093 = fromList transition0722Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0722Chunk0]
  have hn : (transition0722Raw0 : Multiset ℕ) = 1 • (supportNumbers0159 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0159] using hm

private def transition0723Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 520, 521, 522, 523, 524, 525, 526, 527, 536, 537, 538, 539, 540, 541, 542, 543, 584, 585, 586, 587, 588, 589, 590, 591, 600, 601, 602, 603, 604, 605, 606, 607]
private def transition0723Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 16, 656, 17, 657, 18, 658, 19, 659, 20, 660, 21, 661, 22, 662, 23, 663, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 80, 720, 81, 721, 82, 722, 83, 723, 84, 724, 85, 725, 86, 726, 87, 727, 264, 904, 265, 905, 266, 906, 267, 907, 268, 908, 269, 909, 270, 910, 271, 911, 280, 920, 281, 921, 282, 922, 283, 923, 284, 924, 285, 925, 286, 926, 287, 927, 328, 968, 329, 969, 330, 970, 331, 971, 332, 972, 333, 973, 334, 974, 335, 975, 344, 984, 345, 985, 346, 986, 347, 987, 348, 988, 349, 989, 350, 990, 351, 991]
private theorem transition0723Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0723Input0) = fromList transition0723Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0723 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0093 = 1 • support0160 := by
  have hs : support0093 = fromList transition0723Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0723Chunk0]
  have hn : (transition0723Raw0 : Multiset ℕ) = 1 • (supportNumbers0160 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0160] using hm

private def transition0724Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 520, 521, 522, 523, 524, 525, 526, 527, 536, 537, 538, 539, 540, 541, 542, 543, 584, 585, 586, 587, 588, 589, 590, 591, 600, 601, 602, 603, 604, 605, 606, 607]
private def transition0724Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351]
private theorem transition0724Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0724Input0) = fromList transition0724Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0724 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0093 = 1 • support0159 := by
  have hs : support0093 = fromList transition0724Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0724Chunk0]
  have hn : (transition0724Raw0 : Multiset ℕ) = 1 • (supportNumbers0159 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0159] using hm

private def transition0725Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition0725Raw0 : List ℕ := [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 10, 11, 14, 15, 26, 27, 30, 31, 74, 75, 78, 79, 90, 91, 94, 95]
private theorem transition0725Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0725Input0) = fromList transition0725Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0725 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0159 = 1 • support0997 := by
  have hs : support0159 = fromList transition0725Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0725Chunk0]
  have hn : (transition0725Raw0 : Multiset ℕ) = 1 • (supportNumbers0997 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0997] using hm

private def transition0726Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition0726Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 16, 17, 594, 595, 20, 21, 598, 599, 64, 65, 514, 515, 68, 69, 518, 519, 80, 81, 530, 531, 84, 85, 534, 535, 584, 585, 10, 11, 588, 589, 14, 15, 600, 601, 26, 27, 604, 605, 30, 31, 520, 521, 74, 75, 524, 525, 78, 79, 536, 537, 90, 91, 540, 541, 94, 95]
private theorem transition0726Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0726Input0) = fromList transition0726Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0726 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0159 = 1 • support0999 := by
  have hs : support0159 = fromList transition0726Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0726Chunk0]
  have hn : (transition0726Raw0 : Multiset ℕ) = 1 • (supportNumbers0999 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0999] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
